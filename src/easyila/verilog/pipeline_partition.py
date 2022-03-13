"""
Automatically derives pipeline partitions from a verilog design.

For example, consider the following design:

module pipe(input clk, input in, output out);
    reg v1;
    reg v2;
    always (@posedge clk) begin
        v1 = in;
        v2 = v1;
    end
    assign out = v1 + v2;
endmodule

`v1` would be part of the first pipeline stage, which has `in` as input
and `v1'` as output. `v2` would be part of the second, which takes `v1`
as input and returns `v2` as output. `out` would cross pipeline stages
and be in the top-level container model.
"""

import argparse
from collections import defaultdict
from dataclasses import dataclass, field
import functools
import json
import re
from typing import Optional, List

# import networkx as nx
import pyverilog
from pyverilog.dataflow.dataflow_analyzer import VerilogDataflowAnalyzer
from pyverilog.dataflow.dataflow import DFTerminal, DFNotTerminal, DFBranch, DFIntConst, DFPartselect, DFOperator
from pyverilog.utils.scope import ScopeChain, ScopeLabel
from pyverilog.utils import signaltype
# import pydot

# from vcd_wrapper import VcdWrapper

@dataclass
class ModuleSkeleton:
    inputs: List[str] = field(default_factory=list)
    outputs: List[str] = field(default_factory=list)
    state_vars: List[str] = field(default_factory=list)

    def print(self):
        print(
            "ModuleSkeleton(" + f"\n\tin=[{', '.join(self.inputs)}]," + \
            f"\n\tout=[{', '.join(self.outputs)}]," + \
            f"\n\tstate=[{', '.join(self.state_vars)}]" + \
            "\n)"
        )

rn_regex = re.compile("_rn[0-9]+_([a-zA-Z_]+)")
def try_get_rename(signal_name, cc):
    """
    pyverilog may create intermediate variables for registers that are assigned
    and read in sequential logic. For example, a variable `x` may have corresponding
    variable `_rn0_x` to represent its next value. In such a case, `x` at cycle 1 would
    be equivalent to `_rn0_x` at cycle 0.
    """
    qual_name = str(signal_name)
    toks = qual_name.rsplit(".", maxsplit=1)
    if len(toks) == 1:
        hierarchy = ""
        base_name = toks[0]
    else:
        hierarchy = toks[0]
        base_name = toks[1]
    # return f"{qual_name} @ {cc}"
    m = re.match(rn_regex, base_name)
    if m:
        renamed = m.group(1)
        if hierarchy:
            return f"{hierarchy}.{renamed} @ {cc + 1}"
        else:
            return f"{renamed} @ {cc + 1}"
    else:
        return f"{qual_name} @ {cc}"

def partition(
    verilog_file: str,
    top_name: str,
    clock_name: str="clk",
    important_signals: Optional[List[str]]=None
) -> List[List[str]]:
    """
    Given a verilog modules and a list of important_signals, returns a list of
    partitions for those signals. The returned value is a list of lists? Where
    each entry in the top-level list corresponds to a pipeline stage.

    If important_signals is not specifiedor is empty, then all signals in the
    design are preserved.
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
        missing_signal_names = {k for k in important_signals if k not in all_signals_set}
        if missing_signal_names:
            raise Exception("Signal names not found in pyverilog terms: " + ",".join([f"'{s}'" for s in missing_signal_names]))

    # Maps signal names to their source signals from the current cycle
    curr_parent_map = defaultdict(list)
    # Maps signal names to their dependents on the current cycle
    curr_child_map = defaultdict(set)
    # Maps signal names to their source signals on the next cycle
    next_parent_map = defaultdict(list)
    next_child_map = defaultdict(set)
    # Regardless of what signals are identified as "important", we always need to visit
    # every single signal in case we miss some pipeline stages
    # Since every signals is visited, this algorithm does not need to be recursive
    for signal_name in all_signals:
        print("visit", signal_name)
        sc = str_to_scope_chain(signal_name)
        if sc not in binddict:
            continue
        parents = binddict[sc]
        for p in parents:
            if p.tree is not None:
                # should only be length 1
                next_parents, curr_parents = [], []
                find_direct_parent_nodes(p.tree, terms, next_parents, curr_parents)
                print(f"next cycle parents of {signal_name}:", next_parents)
                print(f"curr cycle parents of {signal_name}:", curr_parents)
                if len(next_parents) != 0:
                    next_parent_map[signal_name] = next_parents
                    for p in next_parents:
                        next_child_map[p].add(signal_name)
                if len(curr_parents) != 0:
                    curr_parent_map[signal_name] = curr_parents
                    for p in curr_parents:
                        curr_child_map[p].add(signal_name)
    # Sinks in the dependency graph constitute module outputs
    # or imply internal state if they are an __rn variable
    sinks = [s for s in all_signals if len(curr_child_map[s]) == 0]
    # `stages` contains a list of all pipeline stages we've produced, in the order that
    # we visited them in -- not necessarily their order in the pipeline
    # TODO use exprs instead of just signal names
    stages: List[ModuleSkeleton] = []
    # `stage_map` identifies the index in `stages` that a signal corresponds to
    stage_map: Dict[str, int] = {}
    # `next_map` identifies indices in `stages` where the next value of the signal
    # is read (i.e. used as input)
    next_map: Dict[str, List[int]] = {}
    for sink in sinks:
        if sink not in stage_map:
            new_stage = ModuleSkeleton()
            stage_map[sink] = len(stages)
            stages.append(new_stage)
        stage = stages[stage_map[sink]]
        stage.outputs.append(sink)
        for p in curr_parent_map[sink]:
            if len(curr_parent_map[p]) == 0:
                stage.inputs.append(p)
            else:
                stage.state_vars.append(p)
    return stages

def maybe_scope_chain_to_str(sc):
    if isinstance(sc, ScopeChain):
        return repr(sc)
    else: # pray it's a string
        return sc

def str_to_scope_chain(s):
    return ScopeChain([ScopeLabel(l) for l in s.split(".")])

def find_direct_parent_nodes(p, termdict, next_cycle=None, curr_cycle=None):
    """
    Traverses pyverilog expression tree `p` to find parents of the signal assigned
    by `p`. `next_cycle` is a set of signal names where the value of the signal on
    the NEXT cycle is a dependency of `p`, and `curr_cycle` is a set of signal names
    where the signal value on the CURRENT cycle is a dependency of `p`.

    TERMDICT is the pyverilog-generated dict mapping scope chains to internal
    Term objects, which contain information like wire vs. reg and data width.

    This function will recursively update `next_cycle` and `curr_cycle` while traversing
    the expression tree.
    """
    if next_cycle is None:
        next_cycle = []
    if curr_cycle is None:
        curr_cycle = []
    if isinstance(p, DFTerminal):
        # "_rnN_" wires are the value of the wire on the next timestep
        # TODO account for reassigning w/in always@ block? what if there
        # are multiple always@ blocks?
        sc_str = maybe_scope_chain_to_str(p.name)
        td_entry = termdict[p.name]
        # print(td_entry.termtype)
        unqualified_name = sc_str.split(".")[-1]
        if signaltype.isReg(td_entry.termtype):
            next_cycle.append(sc_str)
        else:
            curr_cycle.append(sc_str)
    elif isinstance(p, DFIntConst):
        pass
    elif isinstance(p, DFBranch):
        assert p.condnode is not None, p.tocode()
        # always a dependency on the condition
        find_direct_parent_nodes(p.condnode, termdict, next_cycle, curr_cycle)
        # truenode and falsenode can both be None for "if/else if/else" blocks that
        if p.truenode is not None:
            find_parent_nodes(p.truenode, termdict, next_cycle, curr_cycle)
        if p.falsenode is not None:
            find_parent_nodes(p.falsenode, termdict, next_cycle, curr_cycle)
    elif isinstance(p, DFNotTerminal):
        # Confusingly, this nodes syntactic "children" are actually its parents in the
        # dependency graph
        for c in p.children():
            assert c is not None
            find_direct_parent_nodes(c, termdict, next_cycle, curr_cycle)
    else:
        raise NotImplementedError("uncovered DF type: " + str(type(p)))

def to_smt_expr(node):
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
        lsb = to_smt_expr(node.lsb)
        msb = to_smt_expr(node.msb)
        raise NotImplementedError("bit slicing not implemented yet")
        # mask = ~(-1 << (msb - lsb + 1)) << lsb
        # return full_val & mask
    elif isinstance(node, DFOperator):
        op = node.operator
        evaled_children = [to_smt_expr(c) for c in node.nextnodes]
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
        raise NotImplementedError("unary reductions implemented yet")
        # return functools.reduce(reducer[op], evaled_children)
    else:
        # return None
        raise NotImplementedError(type(node))
