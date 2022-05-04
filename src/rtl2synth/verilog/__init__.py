
"""
Functions for producing a `rtl2synth.model.Model` from a Verilog file.

This code uses a fork of the [`pyverilog`](https://github.com/noloerino/Pyverilog) library
for parsing and dataflow analysis.
"""

from collections import defaultdict
from dataclasses import dataclass
from enum import Enum, auto
import math
import os
import pickle
import re
import textwrap
from typing import Dict, List, Optional, Set

import pyverilog
from pyverilog.dataflow.dataflow_analyzer import VerilogDataflowAnalyzer
from pyverilog.dataflow.dataflow import (
    DFTerminal,
    DFNotTerminal,
    DFBranch,
    DFConcat,
    DFEvalValue,
    DFIntConst,
    DFOperator,
    DFPartselect,
    DFPointer
)
from pyverilog.utils.scope import ScopeChain, ScopeLabel
from pyverilog.utils import signaltype

from rtl2synth.profile import PROFILE, Segment
from rtl2synth.model import Model, Instance, GeneratedBy, UFPlaceholder
import rtl2synth.lynth.smt as smt

from .vcd_wrapper import VcdWrapper

class COIConf(Enum):
    """
    Configuration for how to treat cone-of-influence (COI) behavior for model generation from Verilog.
    """

    NO_COI = auto()
    """
    No COI check is performed. Any non-important signals are omitted entirely, and
    replaced with 1-arity uninterpreted functions.
    """

    KEEP_COI = auto()
    """
    Any signals found to be within the COI of an important signal (i.e. the parent
    of an important signal in the dataflow graph) is kept in the resulting model.
    """

    UF_ARGS_COI = auto()
    """
    Signals found to be within the COI of an important signal are replaced with
    uninterpreted functions, but the important signals that are its parents in the dependency
    graph are kept as arguments to them. If for a signal `s`, the only signals in the COI are
    `s` itself and `s`'s immediate parents, then no free argument is necessary.
    """

def verilog_to_model(
    verilog_path: str,
    top_name: str,
    clock_pattern: str="clk",
    important_signals: Optional[List[str]]=None,
    coi_conf=COIConf.NO_COI,
    inline_renames=True,
    defined_modules: Optional[List[Model]]=None,
    pickle_path=None,
) -> Model:
    """
    Given a verilog modules and a list of important_signals, returns a list of
    partitions for those signals. The returned value is a Model object.

    :param verilog_path: The path to the Verilog file containing all needed modules. If the design
    is split across multiple RTL files, they should be concatenated into a single file. Because of
    quirks in Pyverilog, this file CANNOT have any `include` directives in it.

    :param top_name: The name of the top-level Verilog module to produce a model for.

    :param clock_pattern: A regex that matches the name of clocks in the design.

    :param important_signals: A list of "important" signals in the design that must be preserved as
    state variables. If left unspecified or is empty, then all signals in the design are preserved.
    References to signals that are not not included in `important_signals` are turned into
    uninterpreted functions with arguments based on their parents in the dependency graph. Note that
    all module inputs and outputs are preserved no matter what, so as to maintain the same I/O
    interface.

    :param coi_conf: Determines how cone of influence calculations are used (see `COIConf` docstring).

    :param inline_renames: If `True` (the default), then pyverilog-generated
    "rename" variables (starting with `_rnN` with some integer `N`) are replaced with their
    corresponding expressions.

    :param defined_modules: Optionally provides a list of existing `Model` definitions. If any of those
    modules are encountered within this verilog modules, they will be replaced with these definitions
    instead of generating new submodules. Any `Model`s defined as instances of a `Model` in this list
    will also be used.

    :param pickle: If specified, the resulting model will be serialized to this file. If this file
    already exists, then the model is read from this path instead of re-parsed from Verilog.

    PERF NOTE: at a cursory glance, it seems like most of the runtime is spent in yacc within
    pyverilog, so algorithmic improvements here probably won't help that much. Perhaps for
    models of multiple RTL modules, the same VerilogDataflowAnalyzer can be reused?
    """
    # === ARGUMENT PROCESSING ===
    if pickle_path is not None and os.path.isfile(pickle_path):
        print("Loading pickled model from", pickle_path)
        with open(pickle_path, "rb") as f:
            return pickle.load(f)

    if important_signals is None:
        important_signals = []
    preserve_all_signals = len(important_signals) == 0

    PROFILE.push(Segment.PV_PARSE)
    analyzer = VerilogDataflowAnalyzer(verilog_path, top_name, noreorder=True)
    analyzer.generate()

    terms = analyzer.getTerms()
    binddict = analyzer.getBinddict()
    PROFILE.pop()
    PROFILE.push(Segment.DF_TRAVERSE)
    all_signals = [str(t) for t in terms]
    clock_regex = re.compile(clock_pattern)
    all_signals = [s for s in all_signals if not clock_regex.search(unqual_name(s))]
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
    submodules: Dict[str, Model] = {}
    """Maps MODULE name (not instance name) to Model object."""
    needed_submodules: Set[str] = set()
    """Set of MODULE names that need to be traversed."""
    instance_names: Dict[str, str] = {}
    """Maps fully qualified INSTANCE names to the corresponding MODULE name."""
    if defined_modules is not None:
        for m in defined_modules:
            for sub in m.get_all_defined_models():
                # This loop includes m
                submodules[sub.name] = sub
    for inst_name, mod_name in analyzer.getInstances():
        if str(inst_name) == top_name:
            continue
        instance_names[str(inst_name)] = mod_name
        if mod_name not in submodules:
            needed_submodules.add(mod_name)
        # TODO raise a warning if a defined submodule is not a needed submodule?

    # === TOP AND SUBMODULE GENERATION ===
    # We can get a topological sort of instances by the length of their scope chain
    # that is, the number of periods in the name from least to greatest
    for inst_name, mod_name in sorted(instance_names.items(), key=lambda p: -p[0].count(".")):
        if mod_name not in needed_submodules:
            continue
        # If there are multiple instances of the same module in a design, the generated
        # model will be based on a traversal of the first encountered instance.
        # This makes no difference in general, but may cause issues when COI configuration is set.
        # if mod_name in submodules:
        #     print("***WARNING: multiples instances of submodule", mod_name, "(doesn't work yet)***")
        submodules[mod_name] = _verilog_model_helper(
            mod_name,
            inst_name,
            terms,
            binddict,
            instance_names,
            True, # TODO configure preserve_all_signals?
            all_signals,
            all_signals, # TODO set important_signals for children
            coi_conf,
            submodules,
            inline_renames
        )
    top_model = _verilog_model_helper(
        top_name,
        top_name,
        terms,
        binddict,
        instance_names,
        preserve_all_signals,
        all_signals,
        important_signals,
        coi_conf,
        submodules,
        inline_renames,
    )
    PROFILE.pop()
    if pickle_path is not None:
        print("Creating pickle at", pickle_path)
        with open(pickle_path, "wb") as f:
            pickle.dump(top_model, f)
    return top_model


def _verilog_model_helper(
    mod_name: str,
    instance_name: str,
    terms,
    binddict,
    instance_names: Dict[str, str],
    preserve_all_signals: bool,
    all_signals: List[str],
    important_signals: List[str],
    coi_conf: COIConf,
    submodules: Dict[str, Model],
    inline_renames,
):
    """
    Helper method for verilog model generation.

    Parameters are as described in `verilog_to_model`, though all arguments are now mandatory.

    `instance_name` is the fully qualified name of this module's instance.
    For the designated top module, this should be the same as `mod_name`.

    `terms` is the term dictionary generated by pyverilog, and `binddict` is the assignment
    dictionary generated by pyverilog.

    `instance_names` is the full mapping of fully qualified instance names to module names.
    Modules are guaranteed to be visited in topological order, so needed models already be populated
    in submodules. Note that this is the list of ALL instances in the design, and thus needs
    to be filtered. TODO optimize that away

    `important_signals` must now always be provided, and must be a list of UNQUALIFIED signal
    names.
    """
    mod_depth = instance_name.count(".") + 1
    """
    `mod_depth` represents the number of scopes deep we're in, e.g. if we're generating
    a model for instance `sub` within `top`, we're at depth 2, and the unqualified signal name
    `top.sub.x` would be converted to `x`.
    """
    if mod_depth == 1:
        assert mod_name == instance_name

    def should_inline(term):
        """
        Returns true if the term is a rename signal or other intermediate thing.
        Not perfect.
        """
        if signaltype.isRename(term.termtype):
            return True
        s = str(term.name)
        return ".md_" in s or ".al_" in s or ".fc_" in s

    # === DEPENDENCY GRAPH STUFF ===

    # 0.5th pass: traverse AST to get expressions for _rn variables.
    rename_substitutions = {}
    """
    Unlike the dicts passed to the model constructor, `rename_substitutions` is keyed on
    fully-qualified variable names.
    """
    if inline_renames:
        for sc, term in terms.items():
            s = str(sc)
            is_curr_scope = scope_prefix(s) == instance_name
            if not is_curr_scope:
                continue
            assert isinstance(term.msb, DFIntConst), term
            assert isinstance(term.lsb, DFIntConst), term
            # TODO deal with `dims` for arrays?
            width = term.msb.eval() - term.lsb.eval() + 1
            if should_inline(term):
                for p in binddict[sc]:
                    # In this context, there should never be an empty else branch, so we
                    # make the default branch field None to loudly error
                    rename_substitutions[s] = pv_to_smt_expr(p.tree, width, terms, None, mod_depth)
        # TODO replace renames with other renames (may require modifying SMT tree,
        # or using dependency graph info to topo sort)

    # TODO for restricting important signals, look into fast COI computation
    # "Fast Cone-Of-Influence computation and estimation in problems with multiple properties"
    # https://ieeexplore.ieee.org/document/6513616
    # First pass: compute dependency graph to get cones of influence for each variable
    # this requires looking at all signals in the design
    deps = DependencyGraph(important_signals, terms, binddict, instance_name, rename_substitutions)
    ufs = []
    """
    `ufs` is a list of non-important variables that are modeled as a an uninterpreted fn with arguments based
    on the variable's COI. This behavior changes based on the `coi_conf` option:
    - NO_COI: All functions are 0-arity, and can be determined directly from edges of the dependency
              graph generated in pass #1.
    - KEEP_COI: Any symbol found to be in the cone-of-influence of an important signal is added
                directly to the model -- the `ufs` map should therefore be empty.
    - UF_ARGS_COI: Any symbol found to be an immediate parent of an important signal is modeled as
                   a UF, but unlike NO_COI, this UF takes as arguments the important signals that
                   are in its COI.
    """
    next_ufs = []
    """
    `next_ufs` is the same as above, except it is a list of non-important _state_ variables whose
    transition relations must be left uninterpereted. COI behavior is the same as for UFs.
    """

    # all_missing = set()
    # Set of all dependencies {b . exists a' <= b}; these become modeled as "next" UFs
    next_missing = set()
    # Set of all dependencies {b . exists a <= b}; these become modeled as UFs
    curr_missing = set()
    # next_missing must recursively contain all parents of signals that are parents of a currently
    # missing signal so as to properly model cross-cycle relations
    to_visit = important_signals[:]
    visited = set()
    for s in to_visit:
        if s in visited:
            continue
        visited.add(s)
        to_visit.extend(list(deps.next_parents[s]))
        to_visit.extend(list(deps.curr_parents[s]))
        if len(deps.next_parents[s]) != 0:
            # If this signal has next_parents, then it belongs to next_missing
            next_missing.add(s)
            assert len(deps.curr_parents[s]) == 0, f"signal {s} had both next and curr parents"
        else:
            curr_missing.add(s)
    next_missing.difference_update(important_signals)
    curr_missing.difference_update(important_signals)
    curr_uf_names = set()
    next_uf_names = set()
    # Filter out any signals that don't belong to this module
    for s in curr_missing:
        is_curr_scope = scope_prefix(s) == instance_name
        if is_curr_scope and (not inline_renames or not should_inline(terms[str_to_scope_chain(s)])):
            curr_uf_names.add(s)
    for s in next_missing:
        is_curr_scope = scope_prefix(s) == instance_name
        if is_curr_scope and (not inline_renames or not should_inline(terms[str_to_scope_chain(s)])):
            next_uf_names.add(s)
    if coi_conf == COIConf.NO_COI:
        # Model missing variables (all 1 edge away from important signal in dep graph)
        # as 0-arity uninterpreted functions.
        for s in curr_uf_names:
            tmp = term_to_smt_var(s, terms, mod_depth)
            ufs.append(UFPlaceholder(tmp.name, tmp.sort, (), True))
        for s in next_uf_names:
            tmp = term_to_smt_var(s, terms, mod_depth)
            next_ufs.append(UFPlaceholder(tmp.name, tmp.sort, (), True))
        important_signal_set = set(important_signals)
    elif coi_conf == COIConf.KEEP_COI:
        if preserve_all_signals:
            important_signal_set = set(important_signals)
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
        important_signal_set = set(important_signals)
        # TODO some amount of recursion needs to happen, since if a UF depends on another variable
        # across a cycle boundary, extra UFs are needed
        for s in curr_uf_names:
            width = get_term_width(s, terms)
            unqual_s = ".".join(s.split(".")[mod_depth:])
            params = tuple(
                term_to_smt_var(p, terms, mod_depth) for p in coi[s] if p in important_signal_set
            )
            # When the COI matches the dependency graph, a degree of freedom is not needed
            # Since immediate parents + self are always a subset of the COI, a length comparison suffices
            free_arg = len(coi[s]) != len(deps.curr_parents[s]) + 1
            ufs.append(UFPlaceholder(unqual_s, smt.BVSort(width), params, free_arg))
        for s in next_uf_names:
            # All arguments of next_uf members must either be state or another UF/next_UF, since
            # they are preserved in order to model cross-cycle relations
            # Thus, we examine the dependency graph rather than the cone of influence
            # and no degree of freedom is needed
            width = get_term_width(s, terms)
            unqual_s = ".".join(s.split(".")[mod_depth:])
            params = tuple(
                term_to_smt_var(p, terms, mod_depth) for p in deps.next_parents[s]
            )
            next_ufs.append(UFPlaceholder(unqual_s, smt.BVSort(width), params, False))
    else:
        raise NotImplementedError("unimplemented COIConf " + str(coi_conf))

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
    m_inputs: List[smt.Variable] = []
    m_outputs: List[smt.Variable] = []
    m_state: List[smt.Variable] = []
    instance_inputs: Dict[str, Dict[smt.Variable, smt.Term]] = defaultdict(dict)
    """
    `instance_inputs` maps an instance name to a dict of
    instance port name to parent expression binding.
    """
    # Preserve all inputs and outputs
    all_signals_set = set(all_signals)
    for sc in terms:
        termtype = terms[sc].termtype
        is_curr_scope = str(sc[:-1]) == instance_name
        if not is_curr_scope:
            continue
        v = term_to_smt_var(str(sc), terms, mod_depth)
        if signaltype.isInput(termtype) and str(sc) in all_signals_set:
            # Ensure this isn't a clock by checking all_signals_set
            m_inputs.append(v)
        elif signaltype.isOutput(termtype):
            m_outputs.append(v)
    for s in important_signals:
        sc = str_to_scope_chain(s)
        not_in_scope = not s.startswith(instance_name + ".")
        if not_in_scope:
            continue
        v = term_to_smt_var(s, terms, mod_depth)
        width = get_term_width(s, terms)
        # Categorize input, output, or state
        termtype = terms[sc].termtype
        is_curr_scope = str(sc[:-1]) == instance_name
        if not inline_renames or not should_inline(terms[sc]):
            # Only add signals belonging to this module
            is_input = signaltype.isInput(termtype)
            if s in important_signal_set and is_curr_scope \
                    and not is_input and not signaltype.isOutput(termtype):
                m_state.append(v)
            # Get expression tree
            # len(sc) == depth + 2 occurs when referencing an instance field
            if sc in binddict and not is_input or len(sc) == mod_depth + 2:
                parents = binddict[sc]
                for p in parents:
                    bv_index_assign = False # Special case for b[v] = expr
                    bv_index_expr = None
                    expr_width = width
                    if p.msb and p.lsb:
                        # BV slice assignment
                        assert v.is_bv_or_bool_expr(), v
                        idx_width = v.c_bitwidth()
                        msb_expr = pv_to_smt_expr(p.msb, idx_width, terms, None, mod_depth, rename_substitutions)
                        msb_expr = msb_expr.const_fold()
                        lsb_expr = pv_to_smt_expr(p.lsb, idx_width, terms, None, mod_depth, rename_substitutions)
                        lsb_expr = lsb_expr.const_fold()
                        if not (msb_expr.is_const() and lsb_expr.is_const()):
                            assert p.msb == p.lsb, "MSB and LSB for BV indexed assign must match"
                            assignee = v
                            bv_index_assign = True
                            bv_index_expr = msb_expr
                        elif lsb_expr.val == 0 and msb_expr.val == idx_width - 1:
                            assignee = v
                        else:
                            assignee = v[msb_expr:lsb_expr]
                    elif p.ptr is not None:
                        # Array index assignment
                        assert v.is_array_expr()
                        idx_width = v.sort.idx_sort.bitwidth
                        assignee = v[pv_to_smt_expr(p.ptr, idx_width, terms, None, mod_depth, rename_substitutions)]
                    else:
                        # Plain old variable assignment
                        assignee = v
                    if p.tree is not None:
                        expr = pv_to_smt_expr(p.tree, expr_width, terms, assignee, mod_depth, rename_substitutions)
                        if bv_index_assign:
                            expr = (assignee & ~(smt.BVConst(1, expr_width).sll(bv_index_expr))) | \
                                expr.zpad(expr_width - expr.c_bitwidth()).sll(bv_index_expr)
                        if is_curr_scope:
                            if p.alwaysinfo is not None and p.alwaysinfo.isClockEdge():
                                # Clocked state update
                                next_updates[assignee] = expr
                            else:
                                # Combinatorial logic
                                logic[assignee] = expr
                        elif is_input:
                            # Instance input
                            # mod_depth + 1 removes the instance name from the variable scope
                            # - 1 when indexing because in "top.x.y" at depth 2, we want "x" at index 1
                            assert p.ptr is None # No array input assignment shenanigans
                            v = term_to_smt_var(s, terms, mod_depth + 1)
                            instance_inputs[str(sc[:-1])][v] = expr
    instances = {}
    for qual_i_name, m_name in instance_names.items():
        if scope_prefix(qual_i_name) != instance_name:
            continue
        sub = submodules[m_name]
        unqual_i_name = unqual_name(qual_i_name)
        bound_inputs = instance_inputs[qual_i_name]
        # If any instance inputs are unbound, that means they were cut by dependency graph traversal --
        # replace them with references to 1-arity UFs
        for i_v in sub.inputs:
            if i_v not in bound_inputs:
                v_name = f"__in__{unqual_i_name}__{i_v.name}"
                ufs.append(UFPlaceholder(v_name, i_v.sort, (), True))
                instance_inputs[qual_i_name][i_v] = smt.Variable(v_name, i_v.sort)
        instances[unqual_i_name] = Instance(sub, instance_inputs[qual_i_name])
    # Remove all UFs that are actually inputs
    input_names = set(v.name for v in m_inputs)
    ufs = [uf for uf in ufs if uf.name not in input_names]
    next_ufs = [uf for uf in next_ufs if uf.name not in input_names]
    # For any outputs that were not important, give them dummy UFs
    defined_uf_names = set(uf.name for uf in ufs) | set(uf.name for uf in next_ufs)
    for o in m_outputs:
        if o.name not in defined_uf_names and o not in logic and o not in next_updates:
            ufs.append(UFPlaceholder(o.name, o.sort, (), True))
    return Model(
        mod_name,
        inputs=m_inputs,
        outputs=m_outputs,
        state=m_state,
        ufs=ufs,
        next_ufs=next_ufs,
        logic=logic,
        transition=next_updates,
        instances=instances,
        generated_by=GeneratedBy.VERILOG_PARSE
    )


def get_term_width(s, terms):
    sc = str_to_scope_chain(s)
    term = terms[sc]
    assert isinstance(term.msb, DFIntConst)
    assert isinstance(term.lsb, DFIntConst)
    return term.msb.eval() - term.lsb.eval() + 1


def term_to_smt_var(s, terms, scope_depth, tall=False):
    sc = str_to_scope_chain(s)
    unqual_s = ".".join(s.split(".")[scope_depth:])
    assert len(unqual_s) > 0, f"scope depth {scope_depth} too deep for {s}"
    term = terms[sc]
    if term.dims:
        # Arrays
        if len(term.dims) != 1:
            raise NotImplementedError("only 1D array indexing is supported")
        data_width = term.msb.eval() - term.lsb.eval() + 1
        idx_0 = term.dims[0][0].eval()
        idx_1 = term.dims[0][1].eval()
        assert idx_0 == 0, f"array indices must start at 0 (was {idx_0})"
        assert idx_1 >= idx_0, f"array second index must be geq first ({idx_0}:{idx_1})"
        idx_width = int(math.log2(idx_1 - idx_0)) + 1
        idx_sort = smt.BoolSort() if idx_width == 1 else smt.BVSort(idx_width)
        data_sort = smt.BoolSort() if data_width == 1 else smt.BVSort(data_width)
        arr_sort = smt.ArraySort(idx_sort, data_sort)
        return smt.Variable(unqual_s, arr_sort)
    width = get_term_width(s, terms)
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

    def __init__(self, important_signals, termdict, binddict, instance_name, rename_substitutions):
        """
        Computes a dependency graph from design information parsed by pyverilog.

        `important_signals` specifies a list of signals which MUST be in the resulting
        dependency graph.

        The resulting dependency graph may contain more than just `important_signals`,
        because if intermediate variables maybe omitted that would induce dependencies.
        For example, in the graph `a -> b -> c`, `c` depends on `a`, but if `b` is omitted
        from the dependency graph, this would be undiscoverable.

        `termdict` and `binddict` are generated from pyverilog.

        `rename_subsitutions` maps "rename" signals to their constituent expressions.
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
            for p in bind:
                if p.tree is not None:
                    direct_parents = find_direct_parent_nodes(p.tree)
                    parents = []
                    for parent in direct_parents:
                        if parent in rename_substitutions:
                            parents.extend(instance_name + "." + v.name for v in rename_substitutions[parent].get_vars())
                        else:
                            parents.append(parent)
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
        sc_str = str(p.name)
        # unqualified_name = sc_str.split(".")[-1]
        parents.append(sc_str)
    elif isinstance(p, DFIntConst) or isinstance(p, DFEvalValue):
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


def pv_to_smt_expr(node, width: Optional[int], terms, assignee, mod_depth, substitutions=None):
    """
    Converts the pyverilog AST tree into an expression in our SMT DSL.

    If specified, `width` is the bit width needed of this expression. This is used for situations
    like inferring the width of a verilog integer constant.

    `terms` is the pyverilog term dictionary, mapping variable scope chains to metadata.

    `assignee` is the SMT term the original AST parent of this expression is being
    assigned to. This is necessary because pyverilog generates ITE blocks with missing
    t/f branches for constructs like `if (...) begin r <= a; end`, which implicitly has
    the branch `else r <= r;`. This might fail in situations where `r` has multiple
    drivers, but hopefully those constructions are either already incorrect, or would
    be elided by the dataflow graph.

    `mod_depth` is the depth of the current module, and determines how many prefix scopes to
    remove from variable names.

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
        qual_name = str(node.name)
        if qual_name in substitutions:
            return substitutions[qual_name]
        return term_to_smt_var(qual_name, terms, mod_depth)
    elif isinstance(node, DFIntConst) or isinstance(node, DFEvalValue):
        v = node.eval()
        if width is None:
            # Pyverilog being quirky again -- DFIntConst makes width a method
            width = node.width() if callable(node.width) else node.width
        if width == 1:
            return smt.BoolConst.T if v else smt.BoolConst.F
        else:
            return smt.BVConst(v, width)
    elif isinstance(node, DFPartselect):
        body_expr = pv_to_smt_expr(node.var, None, terms, assignee, mod_depth, substitutions)
        if isinstance(node.lsb, DFIntConst) and isinstance(node.msb, DFIntConst):
            lsb_v = node.lsb.eval()
            msb_v = node.msb.eval()
            return body_expr[msb_v:lsb_v]
        else:
            # assert node.msb == node.lsb, "MSB and LSB of non-constant index must be identical"
            # TODO handle the distinction between array and BV indexing?
            msb_expr = pv_to_smt_expr(node.msb, None, terms, assignee, mod_depth, substitutions)
            # Pyverilog will produce weird arithmetic expressions when doing assignments to
            # concatenated wires (e.g. assign {a, b} = 32'h3;), so we have to evaluate them
            msb_expr = msb_expr.const_fold()
            lsb_expr = pv_to_smt_expr(node.lsb, None, terms, assignee, mod_depth, substitutions)
            lsb_expr = lsb_expr.const_fold()
            if msb_expr.is_const() and lsb_expr.is_const():
                # Index with raw values to do type conversion properly
                if msb_expr.val >= body_expr.c_bitwidth():
                    # The MSB can exceed prescribed widths in idioms like addition
                    # with carry (assign {C, out} = A + B;), where the argument needs to
                    # be sign extended
                    body_expr = body_expr.zpad_all_children(body_expr.c_bitwidth() - msb_expr.val + 1)
                return body_expr[msb_expr.val:lsb_expr.val]
            else:
                return body_expr[msb_expr:lsb_expr]
    elif isinstance(node, DFBranch):
        assert node.condnode is not None, node.tocode()
        cond = pv_to_smt_expr(node.condnode, 1, terms ,assignee, mod_depth, substitutions)
        truenode = assignee
        falsenode = assignee
        # truenode and falsenode can both be None for "if/else if/else" blocks that
        if node.truenode is not None:
            truenode = pv_to_smt_expr(node.truenode, width, terms, assignee, mod_depth, substitutions)
        else:
            assert isinstance(assignee, smt.Term), (node.tocode(), assignee)
        if node.falsenode is not None:
            falsenode = pv_to_smt_expr(node.falsenode, width, terms, assignee, mod_depth, substitutions)
        else:
            assert isinstance(assignee, smt.Term), (node.tocode(), assignee)
        return cond.ite(truenode, falsenode)
    elif isinstance(node, DFOperator):
        op = node.operator
        # TODO figure out how to deal with width-changing operations
        # (implicit zpad/sext?)
        evaled_children = [pv_to_smt_expr(c, None, terms, assignee, mod_depth, substitutions) for c in node.nextnodes]
        # https://github.com/PyHDI/Pyverilog/blob/5847539a9d4178a521afe66dbe2b1a1cf36304f3/pyverilog/utils/signaltype.py#L87
        # Assume that arity checks are already done for us
        # Invoking the Term class's methods lets us benefit from implicit casts
        t0 = evaled_children[0]
        binops = {
            "Or": t0.__or__,
            "Lor": t0.__or__,
            "And": t0.__and__,
            "Land": t0.__and__,
            "Xor": t0.__xor__,
            # TODO distinguish signedness
            "LessThan": t0.__lt__,
            "GreaterThan": t0.__gt__,
            "LassEq": t0.__le__, # [sic]
            "LessEq": t0.__le__,
            "GreaterEq": t0.__ge__,
            "Eq": t0.op_eq,
            "NotEq": t0.op_ne,
            # what are "Eql" and "NotEql"???
            "Plus": t0.__add__, # TODO is this saturating for booleans?
            "Minus": t0.__sub__,
            "Times": t0.__mul__,
            "Sll": t0.sll,
            "Srl": t0.srl,
            "Sra": t0.sra,
        }
        if op in binops:
            assert len(evaled_children) == 2
            return binops[op](evaled_children[1])
        # By testing, it seems that "Unot" is ~ and "Ulnot" is ! (presumably "Unary Logical NOT")
        unops = {
            "Unot": smt.Kind.Not if width == 1 else smt.Kind.BVNot,
            "Ulnot": smt.Kind.Not,
            "Uor": smt.Kind.BVOrr,
            "Uxor": smt.Kind.BVXorr,
        }
        if op in unops:
            # TODO convert these into method invocations
            assert len(evaled_children) == 1
            return smt.OpTerm(unops[op], (evaled_children[0],))
        if op == "Uminus":
            # 2s complement trick
            assert len(evaled_children) == 1
            return ~evaled_children[0] + 1
        raise NotImplementedError("operator translation not implemented yet: " + str(op))
    elif isinstance(node, DFPointer):
        # Array indexing
        arr = term_to_smt_var(str(node.var.name), terms, mod_depth)
        assert arr.is_array_expr()
        idx_width = arr.sort.idx_sort.bitwidth
        idx_term = pv_to_smt_expr(node.ptr, idx_width, terms, assignee, mod_depth, substitutions)
        return arr[idx_term]
    elif isinstance(node, DFConcat):
        evaled_children = [pv_to_smt_expr(c, None, terms, assignee, mod_depth, substitutions) for c in node.nextnodes]
        return evaled_children[0].concat(*evaled_children[1:])
    else:
        raise NotImplementedError(type(node), node.__dict__, node.tocode())


def str_to_scope_chain(s):
    return ScopeChain([ScopeLabel(l) for l in s.split(".")])


def scope_prefix(s):
    # More efficient than a string split
    idx = s.rfind(".")
    if idx == -1:
        idx = len(s)
    return s[:idx]


def unqual_name(s):
    # More efficient than a string split
    # if rfind returns -1, we should start at index 0 anyway
    return s[s.rfind(".") + 1:]
