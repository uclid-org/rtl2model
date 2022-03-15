
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
) -> Model:
    """
    Given a verilog modules and a list of important_signals, returns a list of
    partitions for those signals. The returned value is a Model object.

    If `important_signals` is not specified, or is empty, then all signals in the
    design are preserved. References to signals that are not not included in
    `important_signals` are turned into uninterpreted functions
    TODO with arguments based on their parents in the dependency graph.

    If `keep_important_parents` is True, then all signals that affect values in `important_signals`
    (i.e. are parents in the dataflow graph of a signal in `important_signals`) are preserved
    as well. Note that COI calculations are performed regardless, as they are needed to identify
    arguments for the uninterpreted functions replacing omitted variables.
    """
    if important_signals is None:
        important_signals = []
    preserve_all_signals = len(important_signals) == 0
    analyzer = VerilogDataflowAnalyzer(verilog_file, top_name, noreorder=True)
    analyzer.generate()

    terms = analyzer.getTerms()
    binddict = analyzer.getBinddict()
    # print(binddict.keys())
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
    # print(all_signals)
    # First pass: compute dependency graph to get cones of influence for each variable
    # this requires looking at all signals in the design
    # TODO how to handle dependencies going through submodules?
    # TODO implement this first pass
    deps = make_dependency_graph(important_signals, terms, binddict)
    # Second pass: traverse AST to get expressions, and replace missing variables with UFs
    # Sadly, the only way we can distinguish between next cycle and combinatorial udpates is
    # by checking whether the variable is a reg or a variable. This isn't an entirely accurate
    # heuristic (since you can "assign" a reg value), but we should be fine to operate under
    # the assumption that idiomatic and/or auto-generated verilog would not include such constructs.
    # `next_updates` maps variable names to SMT expressions for their _next_ cycle values
    next_updates = {}
    # `logic` maps variable names to SMT expressions to their expressions on the _current_ cycle
    logic = {}
    # `ufs` maps ignored (non-important) variables to a corresponding `UFTerm` that describes its
    # cone of influence. This map is updated on calls to `pv_to_smt_expr`.
    ufs = {}
    # These arrays determine which variables are in our model output
    important_signal_set = set(important_signals)
    m_inputs = []
    m_outputs = []
    m_state = []
    for s in important_signals:
        sc = str_to_scope_chain(s)
        termtype = terms[sc].termtype
        # Categorize input, output, or state
        if s in important_signal_set:
            if signaltype.isInput(termtype):
                m_inputs.append(s)
            elif signaltype.isOutput(termtype):
                m_outputs.append(s)
            else:
                m_state.append(s)
        # Get expression tree
        if not signaltype.isInput(termtype):
            parents = binddict[sc]
            for p in parents:
                # Not entirely sure why there's multiple parents
                if p.tree is not None:
                    if p.alwaysinfo is not None and p.alwaysinfo.isClockEdge():
                        next_updates[s] = pv_to_smt_expr(p.tree)
                    else:
                        logic[s] = pv_to_smt_expr(p.tree)
    # TODO unqualify module names
    return Model(
        top_name,
        inputs=m_inputs,
        outputs=m_outputs,
        state=m_state,
        ufs=list(ufs.values()),
        logic=logic, # TODO update to use smt vars as keys instead?
        default_next=next_updates,
        # TODO figure out how to deal with NEXT relations
        instructions={},
        init_values={
            # TODO read init values
        }
    )


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


def make_dependency_graph(important_signals, termdict, binddict) -> DependencyGraph:
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
    curr_parents = defaultdict(list)
    curr_children = defaultdict(set)
    next_parents = defaultdict(list)
    next_children = defaultdict(set)
    to_visit = list(important_signals)
    visited = set()
    for signal_name in to_visit:
        if signal_name in visited:
            continue
        visited.add(signal_name)
        # print("visit", signal_name)
        sc = str_to_scope_chain(signal_name)
        # Inputs are not in binddict, and won't have dependencies
        if sc not in binddict:
            continue
        bind = binddict[sc]
        for i, p in enumerate(bind):
            print("bind information for", signal_name, i)
            print(textwrap.dedent(f"""\
                tree={p.tree.tocode()}
                dest={p.dest}
                msb={p.msb}
                lsb={p.lsb}
                ptr={p.ptr}
                alwaysinfo={p.alwaysinfo}
                parameterinfo={p.parameterinfo}
            """))

        for p in bind:
            if p.tree is not None:
                parents = find_direct_parent_nodes(p.tree)
                if signaltype.isReg(termdict[sc].termtype):
                    # print(f"next cycle parents of {signal_name}:", parents)
                    p_map = next_parents
                    c_map = next_children
                else:
                    # print(f"curr cycle parents of {signal_name}:", parents)
                    p_map = curr_parents
                    c_map = curr_children
                if len(parents) != 0:
                    p_map[signal_name] = parents
                    for p in parents:
                        c_map[p].add(signal_name)
                to_visit.extend(parents)
    return DependencyGraph(curr_parents, curr_children, next_parents, next_children)


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
        # print(td_entry.termtype)
        # unqualified_name = sc_str.split(".")[-1]
        parents.append(sc_str)
    elif isinstance(p, DFIntConst):
        pass
    elif isinstance(p, DFBranch):
        assert p.condnode is not None, p.tocode()
        # always a dependency on the condition
        find_direct_parent_nodes(p.condnode, parents)
        # truenode and falsenode can both be None for "if/else if/else" blocks that
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


def pv_to_smt_expr(node):
    """
    Converts the pyverilog AST tree into an expression in our SMT DSL.

    # TERMDICT is the pyverilog-generated dict mapping scope chains to internal
    # Term objects, which contain information like wire vs. reg and data width.

    TODO merge this into the same pass as find_direct_parent_nodes?

    TODO pass important_signals as an argument, and if a referenced variable
    is not in this list, replace it with a synth fun and with its "important"
    parents as possible arguments

    TODO figure out how to get the width of the expression
    consider passing around an "expected" width?
    """
    if isinstance(node, DFTerminal):
        width = 1 # TODO get the width of the variable
        return smt.Variable(maybe_scope_chain_to_str(node.name), width)
    elif isinstance(node, DFIntConst):
        width = 1 # TODO get the width of the variable
        return smt.BVConst(node.eval(), width)
    elif isinstance(node, DFPartselect):
        lsb = pv_to_smt_expr(node.lsb)
        msb = pv_to_smt_expr(node.msb)
        raise NotImplementedError("bit slicing not implemented yet")
        # mask = ~(-1 << (msb - lsb + 1)) << lsb
        # return full_val & mask
    elif isinstance(node, DFBranch):
        assert node.condnode is not None, p.tocode()
        cond = pv_to_smt_expr(node.condnode)
        # TODO replace empty branch with old value
        truenode = None
        falsenode = None
        # truenode and falsenode can both be None for "if/else if/else" blocks that
        if node.truenode is not None:
            truenode = pv_to_smt_expr(node.truenode)
        if node.falsenode is not None:
            falsenode = pv_to_smt_expr(node.falsenode)
        return smt.OpTerm(smt.Kind.Ite, (cond, truenode, falsenode))
    elif isinstance(node, DFOperator):
        op = node.operator
        evaled_children = [pv_to_smt_expr(c) for c in node.nextnodes]
        # https://github.com/PyHDI/Pyverilog/blob/5847539a9d4178a521afe66dbe2b1a1cf36304f3/pyverilog/utils/signaltype.py#L87
        # Assume that arity checks are already done for us
        reducer = {
            "Or": lambda a, b: a | b,
            "Lor": lambda a, b: a or b,
            "And": lambda a, b: a & b,
            "Land": lambda a, b: a and b,
            "LessThan": lambda a, b: a < b,
            "GreaterThan": lambda a, b: a > b,
            "LassEq": lambda a, b: a <= b, # [sic]
            "GreaterEq": lambda a, b: a >= b,
            "Eq": lambda a, b: a == b,
            "NotEq": lambda a, b: a != b,
            # what are "Eql" and "NotEql"???
        }
        # By testing, it seems that "Unot" is ~ and "Ulnot" is ! (presumably "Unary Logical NOT")
        if op == "Unot":
            assert len(evaled_children) == 1
            return smt.OpTerm(smt.Kind.BVNot, (evaled_children[0],))
        elif op == "Ulnot":
            assert len(evaled_children) == 1
            return smt.OpTerm(smt.Kind.Not, (evaled_children[0],))
        elif op == "Uor":
            assert len(evaled_children) == 1
            # unary OR just checks if any bit is nonzero
            raise NotImplementedError("unary OR not implemented yet")
            # return int(evaled_children[0] > 0)
        return None
        raise NotImplementedError("unary reductions not implemented yet")
        # return functools.reduce(reducer[op], evaled_children)
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
