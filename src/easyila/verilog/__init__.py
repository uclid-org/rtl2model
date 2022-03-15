
from typing import List, Optional

import pyverilog
from pyverilog.dataflow.dataflow_analyzer import VerilogDataflowAnalyzer
from pyverilog.dataflow.dataflow import DFTerminal, DFNotTerminal, DFBranch, DFIntConst, DFPartselect, DFOperator
from pyverilog.utils.scope import ScopeChain, ScopeLabel
from pyverilog.utils import signaltype

from easyila.model import Model
import easyila.lynth.smt as smt

def verilog_to_model(
    verilog_file: str,
    top_name: str,
    clock_name: str="clk",
    important_signals: Optional[List[str]]=None,
    keep_important_parents=False,
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
                    if signaltype.isReg(termtype):
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
        instructions=
            # TODO figure out how to deal with NEXT relations
            next_updates
        ,
        init_values={
            # TODO read init values
        }
    )

def get_dependency_graph(all_signals, binddict):
    ...
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
