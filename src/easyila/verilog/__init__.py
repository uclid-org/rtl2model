
"""
Functions for producing a Model from a Verilog file.

This code uses the pyverilog library for parsing and dataflow analysis.
"""

from collections import defaultdict
from dataclasses import dataclass
from enum import Enum, auto
import textwrap
from typing import Dict, List, Optional, Set

import pyverilog
from pyverilog.dataflow.dataflow_analyzer import VerilogDataflowAnalyzer
from pyverilog.dataflow.dataflow import DFTerminal, DFNotTerminal, DFBranch, DFIntConst, DFPartselect, DFOperator
from pyverilog.utils.scope import ScopeChain, ScopeLabel
from pyverilog.utils import signaltype

from easyila.model import Model
import easyila.lynth.smt as smt

class COIConf(Enum):
    """
    Configuration for how to treat cone-of-influence behavior for model generation from Verilog.
    """

    NO_COI = auto()
    """
    No cone-of-influence check is performed. Any non-important signals are omitted entirely, and
    replaced with 0-arity uninterpreted functions.
    """

    KEEP_COI = auto()
    """
    Any signals found to be within the cone-of-influence of an important signal (i.e. the parent
    of an important signal in the dataflow graph) is kept in the resulting model.
    """

    UF_ARGS_COI = auto()
    """
    Signals found to be within the cone-of-influence of an important signal are replaced with
    uninterpreted functions, but the important signals that are its parents in the dependency
    graph are kept as arguments to them.

    TODO just list vars instead of making them args?
    """

def verilog_to_model(
    verilog_file: str,
    top_name: str,
    clock_name: str="clk",
    important_signals: Optional[List[str]]=None,
    coi_conf=COIConf.NO_COI,
    inline_renames=True,
) -> Model:
    """
    Given a verilog modules and a list of important_signals, returns a list of
    partitions for those signals. The returned value is a Model object.

    If `important_signals` is not specified, or is empty, then all signals in the
    design are preserved. References to signals that are not not included in
    `important_signals` are turned into uninterpreted functions
    TODO with arguments based on their parents in the dependency graph.

    `coi_conf` determines how cone of influence calculations are used (see `COIConf` docstring).

    If `inline_renames` is `True` (the default), then pyverilog-generated "rename" variables
    (starting with `_rnN` for some number `N`) are replaced with their corresponding expressions.
    """
    if important_signals is None:
        important_signals = []
    preserve_all_signals = len(important_signals) == 0
    analyzer = VerilogDataflowAnalyzer(verilog_file, top_name, noreorder=True)
    analyzer.generate()

    terms = analyzer.getTerms()
    binddict = analyzer.getBinddict()
    all_signals = [maybe_scope_chain_to_str(t) for t in terms]
    all_signals = [s for s in all_signals if s.split(".")[-1] != clock_name]
    if preserve_all_signals:
        important_signals = all_signals
    else:
        all_signals_set = set(all_signals)
        missing_signal_names = set()
        for i, k in enumerate(important_signals):
            if k not in all_signals_set:
                qual_name = top_name + "." + k
                if qual_name not in all_signals_set:
                    missing_signal_names.add(k)
                else:
                    important_signals[i] = qual_name
        if missing_signal_names:
            raise Exception("Signal names not found in pyverilog terms: " + ",".join([f"'{s}'" for s in missing_signal_names]))

    # TODO for restricting important signals, look into fast COI computation
    # "Fast Cone-Of-Influence computation and estimation in problems with multiple properties"
    # https://ieeexplore.ieee.org/document/6513616
    # First pass: compute dependency graph to get cones of influence for each variable
    # this requires looking at all signals in the design
    # TODO how to handle dependencies going through submodules?
    deps = DependencyGraph(important_signals, terms, binddict)
    ufs = []
    """
    `ufs` is a list of non-important variables that are modeled as a `UFTerm` with arguments based
    on the variable's COI. This behavior changes based on the `coi_conf` option:
    - NO_COI: All functions are 0-arity, and can be determined directly from edges of the dependency
              graph generated in pass #1.
    - KEEP_COI: Any symbol found to be in the cone-of-influence of an important signal is added
                directly to the model -- the `ufs` map should therefore be empty.
    - UF_ARGS_COI: Any symbol found to be an immediate parent of an important signal is modeled as
                   a UF, but unlike NO_COI, this UF takes as arguments the important signals that
                   are in its COI.
    """

    all_missing = set()
    for s in important_signals:
        all_missing.update(deps.next_parents[s])
        all_missing.update(deps.curr_parents[s])
    all_missing.difference_update(important_signals)
    uf_names = set()
    for s in all_missing:
        if not inline_renames or not signaltype.isRename(terms[str_to_scope_chain(s)].termtype):
            uf_names.add(s)
    if coi_conf == COIConf.NO_COI:
        # Model missing variables (all 1 edge away from important signal in dep graph)
        # as 0-arity uninterpreted functions.
        for s in uf_names:
            ufs.append(term_to_smt_var(s, terms, top_name).to_uf())
    elif coi_conf == COIConf.KEEP_COI:
        if preserve_all_signals:
            pass
        else:
            # When KEEP_COI is specified, all signals in the COI of an important signal is kept
            coi = deps.compute_coi(important_signals)
            all_coi_items = set()
            for l in coi.values():
                all_coi_items.update(l)
            # In order to preserve order, we don't use `all_coi_items` directly
            important_signals = [s for s in all_signals if s in all_coi_items]
            important_signal_set = all_coi_items
    elif coi_conf == COIConf.UF_ARGS_COI:
        # Model missing variables as uninterpreted functions, with important signals in COI
        # as arguments
        coi = deps.compute_coi(important_signals)
        for s in uf_names:
            width = get_term_width(s, terms)
            unqual_s = s[len(top_name) + 1:]
            params = tuple(
                term_to_smt_var(p, terms, top_name) for p in coi[s] if p in important_signal_set
            )
            ufs.append(smt.UFTerm(unqual_s, smt.BVSort(width), params))
    else:
        raise NotImplementedError("unimplemented COIConf " + str(coi_conf))
    # 1.5th pass: traverse AST to get expressions for _rn variables.
    rename_substitutions = {}
    """
    Unlike the dicts passed to the model constructor, `rename_substitutions` is keyed on
    fully-qualified variable names.
    """
    if inline_renames:
        for sc, term in terms.items():
            assert isinstance(term.msb, DFIntConst)
            assert isinstance(term.lsb, DFIntConst)
            # TODO deal with `dims` for arrays?
            width = term.msb.eval() - term.lsb.eval() + 1
            s = maybe_scope_chain_to_str(sc)
            if signaltype.isRename(term.termtype):
                for p in binddict[sc]:
                    # In this context, there should never be an empty else branch, so we
                    # make the default branch field None to loudly error
                    rename_substitutions[s] = pv_to_smt_expr(p.tree, width, None)
        # TODO replace renames with other renames (may require modifying SMT tree,
        # or using dependency graph info to topo sort)

    # Second pass: traverse AST to get expressions, and replace missing variables with UFs
    # Sadly, the only way we can distinguish between next cycle and combinatorial udpates is
    # by checking whether the variable is a reg or a variable. This isn't an entirely accurate
    # heuristic (since you can "assign" a reg value), but we should be fine to operate under
    # the assumption that idiomatic and/or auto-generated verilog would not include such constructs.
    next_updates = {}
    """`next_updates` maps variable names to SMT expressions for their _next_ cycle values"""
    logic = {}
    """`logic` maps variable names to SMT expressions to their expressions on the _current_ cycle"""

    # These arrays determine which variables are in our model output
    important_signal_set = set(important_signals)
    m_inputs: List[smt.Variable] = []
    m_outputs: List[smt.Variable] = []
    m_state: List[smt.Variable] = []
    for s in important_signals:
        v = term_to_smt_var(s, terms, top_name)
        width = get_term_width(s, terms)
        # Categorize input, output, or state
        sc = str_to_scope_chain(s)
        termtype = terms[sc].termtype
        if not inline_renames or not signaltype.isRename(termtype):
            if s in important_signal_set:
                if signaltype.isInput(termtype):
                    m_inputs.append(v)
                elif signaltype.isOutput(termtype):
                    m_outputs.append(v)
                else:
                    m_state.append(v)
            # Get expression tree
            if not signaltype.isInput(termtype):
                parents = binddict[sc]
                for p in parents:
                    # Not entirely sure why there's multiple parents
                    if p.tree is not None:
                        expr = pv_to_smt_expr(p.tree, width, v, rename_substitutions)
                        if p.alwaysinfo is not None and p.alwaysinfo.isClockEdge():
                            next_updates[v] = expr
                        else:
                            logic[v] = expr
    return Model(
        top_name,
        inputs=m_inputs,
        outputs=m_outputs,
        state=m_state,
        ufs=ufs,
        logic=logic,
        default_next=[next_updates],
        instructions={},
        init_values={
            # TODO read init values (may require pyverilog editing)
        }
    )


def get_term_width(s, terms):
    sc = str_to_scope_chain(s)
    term = terms[sc]
    assert isinstance(term.msb, DFIntConst)
    assert isinstance(term.lsb, DFIntConst)
    return term.msb.eval() - term.lsb.eval() + 1


def term_to_smt_var(s, terms, top_name):
    width = get_term_width(s, terms)
    # TODO deal with `dims` for arrays?
    unqual_s = s[len(top_name) + 1:]
    # TODO distinguish between bv1 and booleans
    if width == 1:
        v = smt.Variable(unqual_s, smt.BoolSort())
    else:
        v = smt.Variable(unqual_s, smt.BVSort(width))
    return v


@dataclass
class DependencyGraph:
    curr_parents: Dict[str, List[str]]
    """
    Maps signal names to their source signals on the CURRENT cycle.
    For example, the wire assignment `assign out = a + b;` would add the entry
    `{"out": ["a", "b""]}`
    """
    curr_children: Dict[str, Set[str]]
    """
    Maps signal names to their dependent signals on the CURRENT cycle.
    For example, the wire assignment `assign out = a + b;` would add the entries
    `{"a": {"out"}, "b": {"out"}}`
    """
    next_parents: Dict[str, List[str]]
    """
    Maps signal names to their source signals on the NEXT cycle.
    For example, a reg assignment within an always@ block `r = a + b;` would add the
    entry `{"r": ["a", "b"]}`.
    """
    next_children: Dict[str, Set[str]]
    """
    Maps signal names to their dependent signals from the NEXT cycle.
    For example, a reg assignment within an always@ block `r = a + b;` would add the
    entries `{"a": {"r"}, "b": {"r"}}`.
    """

    def __init__(self, important_signals, termdict, binddict):
        """
        Computes a dependency graph from design information parsed by pyverilog.

        `important_signals` specifies a list of signals which MUST be in the resulting
        dependency graph.

        The resulting dependency graph may contain more than just `important_signals`,
        because if intermediate variables maybe omitted that would induce dependencies.
        For example, in the graph `a -> b -> c`, `c` depends on `a`, but if `b` is omitted
        from the dependency graph, this would be undiscoverable.

        `termdict` and `binddict` are generated from pyverilog.
        """
        self.curr_parents = defaultdict(list)
        self.curr_children = defaultdict(set)
        self.next_parents = defaultdict(list)
        self.next_children = defaultdict(set)
        to_visit = list(important_signals)
        visited = set()
        for signal_name in to_visit:
            if signal_name in visited:
                continue
            visited.add(signal_name)
            sc = str_to_scope_chain(signal_name)
            # Inputs are not in binddict, and won't have dependencies
            if sc not in binddict:
                continue
            bind = binddict[sc]
            # for i, p in enumerate(bind):
            #     print("bind information for", signal_name, i)
            #     print(textwrap.dedent(f"""\
            #         tree={p.tree.tocode()}
            #         dest={p.dest}
            #         msb={p.msb}
            #         lsb={p.lsb}
            #         ptr={p.ptr}
            #         alwaysinfo={p.alwaysinfo}
            #         parameterinfo={p.parameterinfo}
            #     """))

            for p in bind:
                if p.tree is not None:
                    parents = find_direct_parent_nodes(p.tree)
                    if signaltype.isReg(termdict[sc].termtype):
                        p_map = self.next_parents
                        c_map = self.next_children
                    else:
                        p_map = self.curr_parents
                        c_map = self.curr_children
                    if len(parents) != 0:
                        p_map[signal_name] = parents
                        for p in parents:
                            c_map[p].add(signal_name)
                    to_visit.extend(parents)

    def compute_coi(self, signals):
        """
        Computes the cone of influence (i.e. dependency graph parents) for every signal
        in the provided list.
        """
        # TODO optimize to use bitmaps instead
        # Values are dicts that function as a set in order to preserve insertion order
        coi = {}
        to_visit = signals
        visited = set()
        def visit(s):
            visited.add(s)
            # children = set(self.curr_children[s]) | set(self.next_children[s])
            parents = self.curr_parents[s] + self.next_parents[s]
            if s not in coi:
                coi[s] = {s: ()}
            for p in parents:
                if p not in visited:
                    if p not in coi:
                        coi[p] = {p: ()}
                    coi[p] |= visit(p)
                coi[s] |= coi[p]
            return coi[s]

        for s in to_visit:
            if s in visited:
                continue
            # probably a redundant assignment
            coi[s] = visit(s)
        return {k: list(v.keys()) for k, v in coi.items()}

def find_direct_parent_nodes(p, parents=None) -> List[str]:
    """
    Traverses pyverilog expression tree `p` to find parents of the signal assigned
    by `p`. It is agnostic to whether the dependency crosses cycle boundaries; that
    logic should be handled by the caller. Also returns the list when done.

    This function will recursively update `parents` while traversing
    the expression tree.
    """
    if parents is None:
        parents = []
    if isinstance(p, DFTerminal):
        # "_rnN_" wires are the value of the wire on the next timestep
        # TODO account for reassigning w/in always@ block? what if there
        # are multiple always@ blocks?
        sc_str = maybe_scope_chain_to_str(p.name)
        # unqualified_name = sc_str.split(".")[-1]
        parents.append(sc_str)
    elif isinstance(p, DFIntConst):
        pass
    elif isinstance(p, DFBranch):
        assert p.condnode is not None, p.tocode()
        # always a dependency on the condition
        find_direct_parent_nodes(p.condnode, parents)
        # truenode and falsenode can both be None for "if/else if/else" blocks that
        # TODO when a node is missing, there should actually be an implict dependency
        # on itself from the previous cycle
        # this is due to constructions like `if (...) begin r <= a; end`
        # that have an implicit `else begin r <= r; end`
        if p.truenode is not None:
            find_direct_parent_nodes(p.truenode, parents)
        if p.falsenode is not None:
            find_direct_parent_nodes(p.falsenode, parents)
    elif isinstance(p, DFNotTerminal):
        # Confusingly, this nodes syntactic "children" are actually its parents in the
        # dependency graph
        for c in p.children():
            assert c is not None
            find_direct_parent_nodes(c, parents)
    else:
        raise NotImplementedError("uncovered DF type: " + str(type(p)))
    return parents


def pv_to_smt_expr(node, width, assignee, substitutions=None):
    """
    Converts the pyverilog AST tree into an expression in our SMT DSL.

    `width` is the bit width needed of this expression.

    `assignee` is the variable the original AST parent of this expression is being
    assigned to. This is necessary because pyverilog generates ITE blocks with missing
    t/f branches for constructs like `if (...) begin r <= a; end`, which implicitly has
    the branch `else r <= r;`. This might fail in situations where `r` has multiple
    drivers, but hopefully those constructions are either already incorrect, or would
    be elided by the dataflow graph.

    `substitutions` is a mapping of fully qualified variable names to SMT expressions.
    If a variable matching a variable in `substitutions` is encountered while traversing
    the tree, it is replaced with the corresponding expression.

    TODO pass important_signals as an argument, and if a referenced variable
    is not in this list, replace it with a synth fun and with its "important"
    parents as possible arguments
    """
    if substitutions is None:
        substitutions = {}
    if isinstance(node, DFTerminal):
        qual_name = maybe_scope_chain_to_str(node.name)
        if qual_name in substitutions:
            return substitutions[qual_name]
        # TODO distinguish bv1 and bool
        unqual_name = maybe_scope_chain_to_str(node.name[1:])
        if width == 1:
            return smt.BoolVariable(unqual_name)
        else:
            return smt.BVVariable(unqual_name, width)
    elif isinstance(node, DFIntConst):
        return smt.BVConst(node.eval(), width)
    elif isinstance(node, DFPartselect):
        # TODO need to get concrete values for LSB/MS
        if not isinstance(node.lsb, DFIntConst) and not isinstance(node.msb, DFIntConst):
            raise NotImplementedError("only constant bit slices can translated")
        lsb_v = node.lsb.eval()
        msb_v = node.msb.eval()
        # TODO width here can be arbitrary?
        return pv_to_smt_expr(node.var, width, assignee, substitutions)[msb_v:lsb_v]
        # lsb = pv_to_smt_expr(node.lsb)
        # msb = pv_to_smt_expr(node.msb)
        # mask = ~(-1 << (msb - lsb + 1)) << lsb
        # return full_val & mask
    elif isinstance(node, DFBranch):
        assert node.condnode is not None, node.tocode()
        cond = pv_to_smt_expr(node.condnode, 1, assignee, substitutions)
        truenode = assignee
        falsenode = assignee
        # truenode and falsenode can both be None for "if/else if/else" blocks that
        if node.truenode is not None:
            truenode = pv_to_smt_expr(node.truenode, width, assignee, substitutions)
        else:
            assert isinstance(assignee, smt.Term)
        if node.falsenode is not None:
            falsenode = pv_to_smt_expr(node.falsenode, width, assignee, substitutions)
        else:
            assert isinstance(assignee, smt.Term)
        return smt.OpTerm(smt.Kind.Ite, (cond, truenode, falsenode))
    elif isinstance(node, DFOperator):
        op = node.operator
        # TODO figure out how to deal with width-changing operations
        evaled_children = [pv_to_smt_expr(c, width, assignee, substitutions) for c in node.nextnodes]
        # https://github.com/PyHDI/Pyverilog/blob/5847539a9d4178a521afe66dbe2b1a1cf36304f3/pyverilog/utils/signaltype.py#L87
        # Assume that arity checks are already done for us
        binops = {
            "Or": smt.Kind.Or if width == 1 else smt.Kind.BVOr,
            "Lor": smt.Kind.Or,
            "And": smt.Kind.And if width == 1 else smt.Kind.BVAnd,
            "Land": smt.Kind.And,
            # "LessThan": lambda a, b: a < b,
            # "GreaterThan": lambda a, b: a > b,
            # "LassEq": lambda a, b: a <= b, # [sic]
            # "GreaterEq": lambda a, b: a >= b,
            "Eq": smt.Kind.Equal,
            # what are "Eql" and "NotEql"???
            "Plus": smt.Kind.BVAdd, # TODO is this saturating for booleans?
        }
        if op in binops or op == "Neq":
            assert len(evaled_children) == 2
            if op == "Neq":
                return evaled_children[0] != evaled_children[1]
            else:
                return smt.OpTerm(binops[op], tuple(evaled_children))
        # By testing, it seems that "Unot" is ~ and "Ulnot" is ! (presumably "Unary Logical NOT")
        unops = {
            "Unot": smt.Kind.Not if width == 1 else smt.Kind.BVNot,
            "Ulnot": smt.Kind.Not,
        }
        if op in unops:
            assert len(evaled_children) == 1
            return smt.OpTerm(unops[op], (evaled_children[0],))
        elif op == "Uor":
            assert len(evaled_children) == 1
            # unary OR just checks if any bit is nonzero
            raise evaled_children[0] != smt.BVConst(0, width)
        raise NotImplementedError("operator tranlation not implemented yet: " + str(op))
    else:
        # return None
        raise NotImplementedError(type(node))


def maybe_scope_chain_to_str(sc):
    if isinstance(sc, ScopeChain):
        return repr(sc)
    else: # pray it's a string
        return sc


def str_to_scope_chain(s):
    return ScopeChain([ScopeLabel(l) for l in s.split(".")])
