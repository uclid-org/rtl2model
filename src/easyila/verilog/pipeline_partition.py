"""
## INCOMPLETE -- PLEASE IGNORE THIS FILE


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
from easyila.verilog import *

@dataclass
class ModuleSkeleton:
    inputs: List[str] = field(default_factory=list)
    outputs: List[str] = field(default_factory=list)
    state_vars: List[str] = field(default_factory=list)

    def print(self):
        print(
            "ModuleSkeleton(" + f"\n\tin=[{', '.join(self.inputs)}]," + \
            f"\n\tstate=[{', '.join(self.state_vars)}]" + \
            f"\n\tout=[{', '.join(self.outputs)}]," + \
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

    deps = DependencyGraph(important_signals, terms, binddict)
    # Maps signal names to their source signals from the current cycle
    curr_parent_map = deps.curr_parents
    # Maps signal names to their dependents on the current cycle
    curr_child_map = deps.curr_children
    # Maps signal names to their source signals on the next cycle
    next_parent_map = deps.next_parents
    next_child_map = deps.next_children

    # Sinks in the dependency graph constitute module outputs
    sinks = {s for s in all_signals if len(curr_child_map[s]) == 0 and not len(curr_parent_map[s]) == 0}
    # `stages` contains a list of all pipeline stages we've produced, in the order that
    # we visited them in -- not necessarily their order in the pipeline
    # TODO use exprs instead of just signal names
    stages: List[ModuleSkeleton] = []
    # `stage_map` identifies the index in `stages` that a signal corresponds to
    stage_map: Dict[str, int] = {}
    # `input_map` identifies indices in `stages` where the signal is used as input
    input_map: Dict[str, List[int]] = defaultdict(list)
    to_visit = []
    visited = set()
    # First pass: start by identifying outputs (sinks), then add their parents to be
    # traversed
    for sink in sinks:
        new_stage = ModuleSkeleton()
        stage_i = len(stages)
        print("visit sink", sink, "at stage", stage_i)
        stage_map[sink] = stage_i
        stages.append(new_stage)
        new_stage.outputs.append(sink)
        for p in curr_parent_map[sink]:
            has_curr_parents = len(curr_parent_map[p]) == 0
            has_next_parents = len(next_parent_map[p]) == 0
            if has_curr_parents and not has_next_parents:
                # If the node is a source w/ no register edges, then treat it
                # as an input to the module
                new_stage.inputs.append(p)
                input_map[p].append(stage_i)
            else:
                new_stage.state_vars.append(p)
                stage_map[p] = stage_i
                if p not in visited:
                    to_visit.append(p)
    for signal_name in to_visit: # TODO prune non-important signals
        visited.add(signal_name)
        stage_i = stage_map[signal_name]
        print("visit state", signal_name, "at stage", stage_i)
        stage = stages[stage_i]
        for p in curr_parent_map[signal_name]:
            if len(curr_parent_map[p]) == 0:
                stage.inputs.append(p)
                input_map[p].append(stage_i)
            else:
                stage.state_vars.append(p)
                stage_map[p] = stage_i
                if p not in visited:
                    to_visit.append(p)
    return stages
