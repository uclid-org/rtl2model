from collections import defaultdict
import enum
from dataclasses import dataclass, field
import textwrap
from typing import List, Dict, Optional

import easyila.lynth.smt as smt

"""
An Instruction represents a sequence of state transitions. A transition is a mapping
of state variables to expressions computing their next values.

A single instruction is considered to be atomic.
"""
Instruction = List[Dict[smt.Term, smt.Term]]

class GeneratedBy(enum.IntFlag):
    """Indicates different mechanisms for how the model was generated."""
    VERILOG_PARSE   = enum.auto()
    MANUAL          = enum.auto()
    SYGUS2          = enum.auto()
    CASE_SPLIT      = enum.auto()

# models should look something like this?
# TODO instead of having separate uf/logic/next logic, should they all be values of
# a dict keyed by variables? probably not, because of the splitting behavior of the
# `instructions` array
@dataclass
class Model:
    name: str
    inputs: List[smt.Variable]              = field(default_factory=list)
    outputs: List[smt.Variable]             = field(default_factory=list)
    state: List[smt.Variable]               = field(default_factory=list)
    # TODO variables are just UFs of 0 arity -- should we treat them all the same?
    ufs: List[smt.UFTerm]                   = field(default_factory=list)
    # memories: List[]
    # how do we incorporate child-ILA transitions? how do we connect modules?
    instances: Dict[str, "Instance"]        = field(default_factory=dict)
    """
    Maps instance names to coresponding Model objects. I/O connections should be declared through
    the `logic` field.
    """
    logic: Dict[smt.Term, smt.Term]         = field(default_factory=dict)
    """Same-cycle logic expressions."""

    """
    TODO

    how do we distinguish between having ILA instructions to execute vs.
    having transitions? for now, just have a default "NEXT" instruction
    """
    default_next: Instruction               = field(default_factory=lambda: [{}])
    instructions: Dict[str, Instruction]    = field(default_factory=dict)
    init_values: Dict[str, smt.BVConst]     = field(default_factory=dict)
    generated_by: GeneratedBy              = field(default=GeneratedBy.MANUAL, compare=False)

    def __post_init__(self):
        assert isinstance(self.inputs, list)
        assert isinstance(self.outputs, list)
        assert isinstance(self.state, list)
        assert isinstance(self.ufs, list)
        assert isinstance(self.logic, dict)
        assert isinstance(self.default_next, list)
        assert isinstance(self.instances, dict)
        for i, m in self.instances.items():
            assert isinstance(i, str), f"instance name {i} is not a str (was {type(i)})"
            assert isinstance(m, Instance), f"value for instance {i} is not a Instance (was {type(m)})"
        assert isinstance(self.init_values, dict)

    def validate(self):
        """
        Checks that all expressions are well-typed, variables are declared, etc.
        Returns True on success, False on failure.

        TODO more robust error handling
        """
        errs = []
        def report(s):
            print(f"{self.name}:", s)
            errs.append(s)
        def get_var_counts(l):
            counts = defaultdict(lambda: 0) # maps variable name to appearances in l
            for v in l:
                counts[v.name] += 1
            return counts
        in_counts = get_var_counts(self.inputs)
        out_counts = get_var_counts(self.outputs)
        state_counts = get_var_counts(self.state)
        uf_counts = get_var_counts(self.ufs)
        # Zeroth pass: validate all instances and port bindings
        for subname, sub in self.instances.items():
            if not sub.model.validate():
                report(f"validation error(s) in submodule {subname} (see above output)")
            needed_inputs = sub.model.inputs
            for missing_input in set(needed_inputs) - set(sub.inputs.keys()):
                report(f"instance {subname} is missing binding for input {missing_input}")
            for extra_input in set(sub.inputs.keys()) - set(needed_inputs):
                report(f"instance {subname} has binding for unknown input {extra_input}")
        # First pass: no variable is declared multiple times
        # TODO don't be stateful if isinstance(v, smt.Variable)!
        for s, count in in_counts.items():
            if "." in s:
                report(f"input {s} cannot have . in its name")
            if count > 1:
                report(f"input {s} was declared multiple times")
            if s in out_counts:
                report(f"input {s} was also declared as an output")
            if s in state_counts:
                report(f"input {s} was also declared as a state variable")
            if s in uf_counts:
                report(f"input {s} was also declared as an uninterpreted function")
        for s, count in out_counts.items():
            if "." in s:
                report(f"output {s} cannot have . in its name")
            if count > 1:
                report(f"output {s} was declared multiple times")
            if s in state_counts:
                report(f"output {s} was also declared as a state variable")
            # if s in uf_counts:
            #     report(f"output {s} was also declared as an uninterpreted function")
        for s, count in state_counts.items():
            if "." in s:
                report(f"state variable {s} cannot have . in its name")
            if count > 1:
                report(f"state variable {s} was declared multiple times")
            if s in uf_counts:
                report(f"output {s} was also declared as an uninterpreted function") 
        for s, count in uf_counts.items():
            if "." in s:
                report(f"uninterpreted function {s} cannot have . in its name")
            if count > 1:
                report(f"uninterpreted function {s} was declared multiple times")
        # Second pass: all state and output have assigned expressions xor transition relations
        # and that inputs + UFs do NOT have declared logic
        # TODO for now, outputs can also be UFs
        logic_and_next = {v.name for v in self.logic if isinstance(v, smt.Variable)}
        next_keys = set()
        for l in self.default_next:
            names = {v.name for v in l if isinstance(v, smt.Variable)}
            next_keys.update(names)
            logic_and_next.update(names)
        for v in self.inputs:
            if v.name in self.logic:
                report(f"input variable {v.name} has illegal declared logic")
            if v.name in next_keys:
                report(f"input variable {v.name} has illegal declared transition relation")
        for v in self.state:
            if not isinstance(v.sort, smt.ArraySort) and v.name not in logic_and_next:
                report(f"state variable {v.name} has no declared logic or transition relation")
        for v in self.outputs:
            if v.name not in logic_and_next and v.name not in uf_counts:
                report(f"output variable {v.name} has no declared logic or transition relation")
        for v in self.ufs:
            if v.name in self.logic:
                report(f"uninterpreted function {v.name} has illegal declared logic")
            if v.name in next_keys:
                report(f"uninterpreted function {v.name} has illegal declared transition relation")
        # nth pass: init values correspond to valid variables
        # TODO
        # nth pass: transition relations and expressions type check and are valid
        for v, e in self.logic.items():
            if not e.typecheck():
                report(f"type error in logic for {v} (see above output)")
        for l in self.default_next:
            for v, e in l.items():
                if not e.typecheck():
                    report(f"type error in transition logic for {v} (see above output)")
        return len(errs) == 0

    def pretty_str(self, indent_level=0):
        # Weird things happen with escaped chars in f-strings
        newline = '\n' + ' ' * 20
        c_newline = "," + newline
        if len(self.inputs) > 0:
            input_block = newline + c_newline.join([str(a.get_decl()) for a in self.inputs])
        else:
            input_block = ""
        if len(self.outputs) > 0:
            output_block = newline + c_newline.join([str(a.get_decl()) for a in self.outputs])
        else:
            output_block = ""
        if len(self.state) > 0:
            state_block = newline + c_newline.join([str(a.get_decl()) for a in self.state])
        else:
            state_block = ""
        if len(self.ufs) > 0:
            uf_block = newline + c_newline.join([str(a) for a in self.ufs])
        else:
            uf_block = ""
        if len(self.instances) > 0:
            inst_block = newline + (newline + c_newline).join(str(m) + ':\n' + i.pretty_str(24) for m, i in self.instances.items())
        else:
            inst_block = ""
        if len(self.logic) > 0:
            logic_block = newline + c_newline.join(str(m) + ': ' + str(e) for m, e in self.logic.items())
        else:
            logic_block = ""
        if len(self.default_next) > 0:
            next_block = newline + c_newline.join(str(m) + ': ' + str(e) for m, e in self.default_next[0].items())
        else:
            next_block = ""
        return textwrap.indent(textwrap.dedent(f"""\
            Model {self.name} (generated via {str(self.generated_by)}):
                inputs={input_block}
                outputs={output_block}
                state={state_block}
                ufs={uf_block}
                instances={inst_block}
                logic={logic_block}
                default_next={next_block}
            """
        ), ' ' * indent_level)

    def print(self):
        print(self.pretty_str())

    def to_uclid(self):
        u_vars = []
        def u_append(lst, prefix):
            nonlocal u_vars
            if len(lst) > 0:
                u_vars.extend(prefix + " " + str(s.get_decl()) + ";" for s in lst)
        u_append(self.inputs, "input")
        u_append(self.outputs, "output")
        u_append(self.state, "var")
        if len(self.ufs) > 0:
            u_vars.extend(s.to_uclid() for s in self.ufs)
        newline = ' ' * 16
        u_vars_s = textwrap.indent("\n".join(u_vars), newline)
        instances_s = textwrap.indent("\n".join(i.to_uclid(n) for n, i in self.instances.items()), newline)
        logic_s = textwrap.indent(
            "\n".join(f"{lhs.to_uclid()} = {rhs.to_uclid()};" for lhs, rhs in self.logic.items()),
            newline + "    "
        )
        if len(self.default_next) > 0:
            next_s = textwrap.indent(
                "\n".join(f"{lhs.to_uclid()}' = {rhs.to_uclid()};" for lhs, rhs in self.default_next[0].items()),
                newline + "    "
            )
        else:
            next_s = ""
        if len(self.instances) > 0:
            child_next_s = textwrap.indent(
                "\n".join(f"next({n});" for n in self.instances),
                newline + "    "
            )
        else:
            child_next_s = ""
        return textwrap.dedent(f"""\
            module {self.name} {{
{u_vars_s}
{instances_s}
                init {{

                }}

                next {{
                    // Combinatorial logic
{logic_s}
                    // Transition logic
{next_s}
                    // Instance transitions
{child_next_s}
                }}
            }}""")

    def _get_submodules(self, submodel_list, visited_submodel_names):
        for i in self.instances.values():
            if i.model.name not in visited_submodel_names:
                i.model._get_submodules(submodel_list, visited_submodel_names)
        # DFS postorder traversal
        submodel_list.append(self)
        visited_submodel_names.add(self.name)

    def to_uclid_with_children(self):
        """
        Generates a uclid model, as well as a uclid model for every child instance.
        """
        submodels = []
        visited_submodel_names = set()
        # Submodules are added in DFS postorder traversal
        self._get_submodules(submodels, visited_submodel_names)
        return "\n\n".join(s.to_uclid() for s in submodels)

    def case_split(self, var_name: str, possible_values: Optional[List[int]]=None):
        """
        Automatically case splits this model on different values of `var_name`.
        `var_name` must be a boolean or bitvector variable, and cannot be an output.

        `possible_values` specifies the list of values that `var_name` can take on.
        If not specified, then all values encompassed by `var_name`'s sort will be
        used instead (e.g. a bv3 would have values 0-8).
        """
        for v in self.inputs:
            if v.name == var_name:
                # TODO validate possible_values if provided
                if possible_values is None:
                    if isinstance(v.sort, smt.BoolSort):
                        possible_values = (True, False)
                    elif isinstance(v.sort, smt.BVSort):
                        possible_values = range(0, 2 ** v.sort.bitwidth)
                    else:
                        raise TypeError(f"cannot case split on input {v}: case splits can only be performed on bool/bv variables")
                return self._case_split_input(v, possible_values)
        for v in self.state_vars:
            if isinstance(v, smt.Variable) and v.name == var_name:
                # TODO validate possible_values if provided
                if possible_values is None:
                    if isinstance(v.sort, smt.BoolSort):
                        possible_values = (True, False)
                    elif isinstance(v.sort, smt.BVSort):
                        possible_values = range(0, 2 ** v.sort.bitwidth)
                    else:
                        raise TypeError(f"cannot case split on input {v}: case splits can only be performed on bool/bv variables")
                return self._case_split_input(v, possible_values)
        return KeyError(f"cannot case split on {var_name}: no such input or state variable")

    def _case_split_input(self, input_var: smt.Variable, possible_values: List[int]):
        inputs = self.inputs[:]
        inputs.remove(input_var)
        # module/instance suffixes corresponding to possible_values
        varname = input_var.name
        if possible_values == (True, False):
            suffixes = [f"{varname}_TRUE", f"{varname}_FALSE"]
        else:
            suffixes = [f"{varname}_{n:b}" for n in possible_values]
        instances = {}
        for i, cs_value in enumerate(possible_values):
            if isinstance(input_var.sort, smt.BoolSort):
                cs_value_t = smt.BoolConst.T if cs_value else smt.BoolConst.F
            else:
                cs_value_t = smt.BVConst(cs_value, input_var.sort.bitwidth)
            bindings = {i: i for i in inputs}
            new_model = Model(
                name=f"{self.name}__{suffixes[i]}",
                inputs=inputs,
                outputs=self.outputs,
                state=self.state,
                ufs=self.ufs,
                instances={
                    name: Instance(
                        # Rewrite expressions for all input bindings
                        inst.model,
                        {
                            v_name: t.replace_vars(
                                input_var,
                                cs_value_t
                            )
                            for v_name, t in inst.inputs.items()
                        }
                    )
                    for name, inst in self.instances.items()
                },
                # TODO may need to replace LHS of assignments too? in case of indexing and stuff
                logic={
                    k: t.replace_vars(input_var, cs_value_t) for k, t in self.logic.items()
                },
                default_next=[
                    {k: t.replace_vars(input_var, cs_value_t) for k, t in l.items()}
                    for l in self.default_next
                ],
                generated_by=GeneratedBy.CASE_SPLIT,
            )
            instances[f"{self.name}__{suffixes[i]}_inst"] = Instance(new_model, bindings)
        # TODO generalize to match
        new_logic = {
            o: input_var.ite(
                smt.Variable(f"{self.name}__{suffixes[0]}.{o.name}", o.sort),
                smt.Variable(f"{self.name}__{suffixes[1]}.{o.name}", o.sort)
            ) for o in self.outputs
        }
        return Model(
            name=self.name,
            inputs=self.inputs,
            outputs=self.outputs,
            state=[],
            ufs=self.ufs,
            instances=instances,
            logic=new_logic,
            default_next=[],
            generated_by=self.generated_by | GeneratedBy.CASE_SPLIT,
        )

    def _case_split_var(self, state_var: smt.Variable, possible_values: List[int]):
        raise NotImplementedError()
        # return Model(
        #     generated_by=self.generated_by | GeneratedBy.CASE_SPLIT,
        # )

@dataclass
class Instance:
    """
    A class representing the concrete instantiation of a model.

    Input bindings are represented in the `inputs` field.

    Output bindings are specified only by the parent module.
    """

    model: Model
    inputs: Dict[smt.Variable, smt.Term]
    """
    Maps UNQUALIFIED input names to an expression in the parent module (all variable references
    within the expression are relative to that parent.)
    """

    def pretty_str(self, indent_level=0):
        newline = '\n' + ' ' * 16
        c_newline = "," + newline
        if len(self.inputs) > 0:
            input_block = newline + c_newline.join(str(v) + ": " + str(e) for v, e in self.inputs.items())
        else:
            input_block = newline
        # maybe there's a cleaner way to do this f string :)
        return textwrap.indent(textwrap.dedent(f"""\
            input_bindings={input_block}
            model=
{self.model.pretty_str(16)}"""),
            ' ' * indent_level
        )

    def to_uclid(self, instance_name):
        newline = ",\n" + (' ' * 16)
        i_lines = (' ' * 16) + newline.join(
            f"{lhs.name} : ({rhs.to_uclid()})" for lhs, rhs in self.inputs.items()
        )
        return textwrap.dedent(f"""\
            instance {instance_name} : {self.model.name}
            (
{i_lines}
            );""")


@dataclass
class SynthesizedModel(Model):
    """
    A model with components generated by SyGuS.

    TODO figure out how to compose this
    """
    def __init__(self):
        ...
