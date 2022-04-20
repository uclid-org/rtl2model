from collections import defaultdict
import enum
from dataclasses import dataclass, field
import textwrap
from typing import Collection, List, Dict, Optional, Tuple

import easyila.lynth.smt as smt

Instruction = Dict[smt.Term, smt.Term]
"""
An `Instruction` represents state transitions. A transition is a mapping
of state variables to expressions computing their next values.

A single instruction is considered to be atomic.
"""

class GeneratedBy(enum.IntFlag):
    """Indicates different mechanisms for how the model was generated."""
    VERILOG_PARSE   = enum.auto()
    MANUAL          = enum.auto()
    SYGUS2          = enum.auto()
    CASE_SPLIT      = enum.auto()
    FLATTEN         = enum.auto()


@dataclass(frozen=True)
class UFPlaceholder:
    name: str
    sort: smt.Sort
    params: Tuple[smt.Variable, ...]
    free_arg: bool

    def maybe_free_arg_var(self) -> Optional[smt.Variable]:
        if not self.free_arg:
            return None
        # TODO determine width of free variable
        # for example, if a bv3 was elided but this expression is a boolean,
        # that bv3 may have been used in an 8-way case stmt or something
        return smt.Variable(f"__free_{self.name}", self.sort)

    def get_ref(self) -> smt.Variable:
        return smt.Variable(self.name, self.sort)

    def to_ufterm(self) -> smt.UFTerm:
        free_var = self.maybe_free_arg_var()
        if free_var is not None:
            params = self.params + (free_var,)
        else:
            params = self.params
        return smt.UFTerm(self.name, self.sort, params)


@dataclass
class Model:
    name: str
    inputs: List[smt.Variable]              = field(default_factory=list)
    outputs: List[smt.Variable]             = field(default_factory=list)
    state: List[smt.Variable]               = field(default_factory=list)
    ufs: List[UFPlaceholder]                = field(default_factory=list)
    """Combinatorial relations modeled as uninterpreted functions."""
    next_ufs: List[UFPlaceholder]           = field(default_factory=list)
    """
    Transition relations modeled as uninterpreted functions.
    For example, if a UF f(a, b) is in this list, then it would correspond to some
    transition f' <= f(a, b) in RTL. References to a UF in this list read from
    the current value of the wire rather than the primed (next).

    When emitted to RTL or uclid, each UF effectively induces a new state variable.
    """

    # memories: List[]
    # how do we incorporate child-ILA transitions? how do we connect modules?
    instances: Dict[str, "Instance"]        = field(default_factory=dict)
    """
    Maps instance names to coresponding `Model` objects. I/O connections should be declared through
    the `logic` field.
    """
    logic: Dict[smt.Term, smt.Term]         = field(default_factory=dict)
    """Same-cycle logic expressions."""

    """
    TODO

    how do we distinguish between having ILA instructions to execute vs.
    having transitions? for now, just have a default "NEXT" instruction
    """
    default_next: Instruction               = field(default_factory=dict)
    init_values: Dict[str, smt.BVConst]     = field(default_factory=dict)
    assertions: List[smt.Term]              = field(default_factory=list)
    assumptions: List[smt.Term]             = field(default_factory=list)
    generated_by: GeneratedBy               = field(default=GeneratedBy.MANUAL, compare=False)

    # === VALIDATION AND PROPERTIES ===

    def __post_init__(self):
        assert isinstance(self.inputs, list)
        assert isinstance(self.outputs, list)
        assert isinstance(self.state, list)
        assert isinstance(self.ufs, list)
        for uf in self.ufs:
            assert isinstance(uf, UFPlaceholder)
        assert isinstance(self.logic, dict)
        for _k, t in self.logic.items():
            assert isinstance(t, smt.Term), t
        assert isinstance(self.default_next, dict)
        for _k, t in self.default_next.items():
            assert isinstance(t, smt.Term), t
        assert isinstance(self.instances, dict)
        for i, m in self.instances.items():
            assert isinstance(i, str), f"instance name {i} is not a str (was {type(i)})"
            assert isinstance(m, Instance), f"value for instance {i} is not a Instance (was {type(m)})"
        assert isinstance(self.init_values, dict)
        for a in self.assertions:
            assert isinstance(a.sort, smt.BoolSort)
        for a in self.assumptions:
            assert isinstance(a.sort, smt.BoolSort)

    @property
    def is_stateful(self):
        return len(self.next_ufs) != 0 or len(self.default_next) != 0

    def validate(self):
        """
        Checks that all expressions are well-typed, variables are declared, etc.
        Returns `True` on success, `False` on failure.

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
        for subname, inst in self.instances.items():
            if not inst.model.validate():
                report(f"validation error(s) in submodule {subname} (see above output)")
            bound_names = [i.name for i in inst.inputs]
            bound_sorts = {i.name: t.sort for i, t in inst.inputs.items()}
            needed_names = [i.name for i in inst.model.inputs]
            needed_sorts = {i.name: i.sort for i in inst.model.inputs}
            for missing_input in set(needed_names) - set(bound_names):
                report(f"instance {subname} is missing binding for input {missing_input}")
            for extra_input in set(bound_names) - set(needed_names):
                report(f"instance {subname} has binding for unknown input {extra_input}")
            for name, sort in needed_sorts.items():
                if name in bound_sorts and sort != bound_sorts[name]:
                    report(f"instance {subname} has mismatched binding for input {name}: needed {sort}, got {bound_sorts[name]}")
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
        def get_assignee_name(term):
            if isinstance(term, smt.Variable):
                return term.name
            else:
                return get_assignee_name(term._children[0])
        logic_and_next = {get_assignee_name(v) for v in self.logic}
        next_keys = set()
        names = {get_assignee_name(v) for v in self.default_next}
        next_keys.update(names)
        logic_and_next.update(names)
        for v in self.inputs:
            # TODO allow multiple assigns to different bit fields of the same wire?
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
        for v, e in self.default_next.items():
            if not e.typecheck():
                report(f"type error in transition logic for {v} (see above output)")
        return len(errs) == 0

    # === STRING/FORMAT CONVERSIONS ===

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
        if len(self.next_ufs) > 0:
            next_uf_block = newline + c_newline.join([str(a) for a in self.next_ufs])
        else:
            next_uf_block = ""
        if len(self.instances) > 0:
            inst_block = newline + (newline + c_newline).join(str(m) + ':\n' + i.pretty_str(24) for m, i in self.instances.items())
        else:
            inst_block = ""
        if len(self.logic) > 0:
            logic_block = newline + c_newline.join(str(m) + ': ' + str(e) for m, e in self.logic.items())
        else:
            logic_block = ""
        if len(self.default_next) > 0:
            next_block = newline + c_newline.join(str(m) + ': ' + str(e) for m, e in self.default_next.items())
        else:
            next_block = ""
        return textwrap.indent(textwrap.dedent(f"""\
            Model {self.name} (generated via {str(self.generated_by)}):
                inputs={input_block}
                outputs={output_block}
                state={state_block}
                ufs={uf_block}
                next_ufs={next_uf_block}
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
        raise Exception("need to add UF placeholder vars")
        # Generate "__next" temp vars
        next_vars = {}
        for transitions in self.default_next:
            for v in transitions:
                assert isinstance(v, smt.Variable), "uclid translation only works for variable (not array) assignments"
                next_vars[v] = smt.Variable(v.name + "__next", v.sort)
        u_append(next_vars.values(), "var")
        if len(self.ufs) > 0:
            u_vars.extend(s.to_ufterm().to_uclid() for s in self.ufs)
        newline = ' ' * 16
        u_vars_s = textwrap.indent("\n".join(u_vars), newline)
        instances_s = textwrap.indent("\n".join(i.to_uclid(n) for n, i in self.instances.items()), newline)
        def fix_var_refs(expr, prime_vars=False):
            """
            Replaces variable references to calls to uninterpreted functions when appropriate.
            """
            # trick: since we named uf params the same as module variables,
            # we can just call on variable terms with those same names
            ufs = {
                smt.Variable(uf.name, uf.sort): smt.ApplyUF(uf.to_ufterm(), uf.params)
                for uf in self.ufs
            }
            # TODO what if a UF takes in another UF as argument?
            ufs.update({
                smt.Variable(uf.name, uf.sort): smt.ApplyUF(uf.to_ufterm(), uf.params)
                for uf in self.next_ufs
            })
            return expr.replace_vars(ufs).to_uclid(prime_vars=prime_vars)
        init_logic_s = textwrap.indent(
            "\n".join(f"{lhs.to_uclid()} = {fix_var_refs(rhs)};" for lhs, rhs in self.logic.items()),
            newline + "    "
        )
        logic_s = textwrap.indent(
            "\n".join(f"{lhs.to_uclid(prime_vars=True)} = {fix_var_refs(rhs, prime_vars=True)};" for lhs, rhs in self.logic.items()),
            newline + "    "
        )
        if len(self.default_next) > 0:
            init_next_s = textwrap.indent(
                "\n".join(
                    f"{next_vars[lhs].to_uclid()} = {fix_var_refs(rhs)};\n"
                    f"{lhs.to_uclid()} = {next_vars[lhs].to_uclid()};"
                    for lhs, rhs in self.default_next.items()
                ),
                newline + "    "
            )
            next_s = textwrap.indent(
                "\n".join(
                    f"{next_vars[lhs].to_uclid(prime_vars=True)} = {fix_var_refs(rhs, prime_vars=True)};\n"
                    f"{lhs.to_uclid(prime_vars=True)} = {next_vars[lhs].to_uclid(prime_vars=True)};"
                    for lhs, rhs in self.default_next.items()
                ),
                newline + "    "
            )
        else:
            init_next_s = ""
            next_s = ""
        if len(self.instances) > 0:
            child_next_s = textwrap.indent(
                "\n".join(f"next({n});" for n in self.instances),
                newline + "    "
            )
        else:
            child_next_s = ""
        # TODO serialize assertions and assumptions
        return textwrap.dedent(f"""\
            module {self.name} {{
{u_vars_s}
{instances_s}
                init {{
{init_logic_s}
{init_next_s}
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

    def to_uclid_with_children(self) -> str:
        """
        Generates a uclid model, as well as a uclid model for every child instance.
        """
        submodels = []
        visited_submodel_names = set()
        # Submodules are added in DFS postorder traversal
        self._get_submodules(submodels, visited_submodel_names)
        return "\n\n".join(s.to_uclid() for s in submodels)

    # === SOLVER STUFF ===

    def to_solver(self):
        """
        Encodes the transition relations of this model as a one-cycle unrolling of SMT assertions.
        """
        s = smt.Solver()
        return self._to_solver_helper(s, "")

    def _to_solver_helper(self, s: smt.Solver, inst_prefix: str):
        BASE_PREFIX = "__BASE." + inst_prefix # current cycle signals
        STEP_PREFIX = "__STEP." + inst_prefix # next cycle signals
        FREE_PREFIX = "__FREE." + inst_prefix # UF free variables
        base_dict = {
            v: v.add_prefix(BASE_PREFIX)
            for v in self.inputs + self.outputs + self.state
        }
        # TODO deal with arrays
        next_dict = {
            v: v.add_prefix(STEP_PREFIX)
            for v in self.outputs + self.state if v in self.default_next
        }
        # BMC: the approach uclid takes to modeling transitions is
        # on every cycle of simulation is to create a separate set of state vars
        # for each cycle, and then assert the vars of the next cycle wrt vars of the first cycle
        # e.g. `b' <= b` would result in `assert (state_2_b == state_1_b)`
        # for some assumed invariant/property (e.g. b > 0), you would assert the property holds
        # on state_1_b (assert (not (> state_1_b 0))), then assert it falsifiable on state_2_b
        # (assert (not (> state_1_b 0))) -- if you get an UNSAT result, then that tells you no
        # assignment of variables violates the invariant
        # Induction:
        # basically the same story, with state_1_b in terms of initial_b
        # logic from submodules gets inlined
        for v in base_dict.values():
            s.add_variable(v)
        for v in next_dict.values():
            s.add_variable(v)
        # For each uninterpreted function with free variables, create a dummy free variable
        # TODO havoc uf free variables
        uf_replacements = {}
        for uf_p in self.ufs:
            ref = uf_p.get_ref()
            args = [base_dict[a] for a in uf_p.params]
            if uf_p.free_arg:
                free_var = ref.add_prefix(FREE_PREFIX)
                s.add_variable(free_var)
                args.append(free_var)
            call = uf_p.to_ufterm().apply(*args)
            uf_replacements[ref] = call
        for uf_p in self.next_ufs:
            ref = uf_p.get_ref()
            s.add_variable(ref.add_prefix(BASE_PREFIX))
            if uf_p.free_arg:
                free_var = ref.add_prefix(FREE_PREFIX)
                s.add_variable(free_var)
            uf_replacements[ref] = ref.add_prefix(BASE_PREFIX)
        # Replace any UFs that have other UFs as args
        for k, t in uf_replacements.items():
            uf_replacements[k] = t.replace_vars(uf_replacements)
        rhs_replacements = {**base_dict, **uf_replacements}
        for k, term in self.logic.items():
            s.add_constraint(k.op_eq(term).replace_vars(rhs_replacements))
        for k, term in self.default_next.items():
            s.add_constraint(k.replace_vars(next_dict).op_eq(term.replace_vars(rhs_replacements)))
        # Add terms for instances
        for inst_name, instance in self.instances.items():
            # Add terms for input port bindings
            for i, term in instance.inputs.items():
                s.add_constraint(i.add_prefix(BASE_PREFIX).op_eq(term.replace_vars(rhs_replacements)))
            # Recursively add terms for instance state
            # TODO IMPORTANT make multiple instances of the same module share UFs
            # TODO to accomodate that, it may be prudent to prefix all UFs by module names
            # this will affect the replacement dict
            instance.model._to_solver_helper(s, inst_name + ".")
        return s

    # === LOGICAL TRANSFORMATIONS ===

    def _get_logic_or_transition(self, var):
        """
        Checks if a variable is referenced on the LHS of an assignment.
        This can either be a direct key, or as part of an array Select.

        If the variable is not found, returns None.
        """
        if var in self.logic:
            return self.logic[var]
        if var in self.default_next:
            return self.default_next[var]
        for k, t in self.logic.items():
            if isinstance(k, smt.OpTerm) and \
                (k.kind == smt.Kind.Select or k.kind == smt.Kind.BVExtract) and k.args[0] == var:
                    return t
        for k, t in self.default_next.items():
            if isinstance(k, smt.OpTerm) and \
                (k.kind == smt.Kind.Select or k.kind == smt.Kind.BVExtract) and k.args[0] == var:
                    return t
        return None

    def eliminate_dead_code(self):
        """
        Removes state variables, instances, and UFs that don't influence the output. Inputs and
        outputs are always preserved.

        This is run recursively on instances, but does not take into account inter-module
        connections when examining liveness of a signal.
        """
        # Maps SMT var to set of SMT var parents
        # Instance names are also added here as both keys and values
        # e.g. a connection of s0 -> inst.out -> s1 would produce dependencies
        # of inst: s0 and s1: inst
        dependencies = defaultdict(set)
        def normalize(vs):
            """Replaces instance fields by the instance name"""
            return tuple(v.name.split(".")[0] if "." in v.name else v.name for v in vs)
        # UFs already have parents encoded
        for u in self.ufs:
            dependencies[u.name].update({v.name for v in u.params})
        for u in self.next_ufs:
            dependencies[u.name].update({v.name for v in u.params})
        # Instances already have parents encoded
        for n, i in self.instances.items():
            i_deps = set()
            for term in i.inputs.values():
                i_deps.update(normalize(term.get_vars()))
            dependencies[n] = i_deps
        to_visit = self.outputs[:] # List of vars, where everything else is Set[str]
        visited = set()
        non_state_set = set(i.name for i in self.inputs)
        non_state_set.update(set(u.name for u in self.next_ufs))
        non_state_set.update(set(u.name for u in self.ufs))
        for v in to_visit:
            if v.name in visited or v.name in non_state_set or "." in v.name:
                # Parents of instance outputs are already handled
                continue
            visited.add(v.name)
            term = self._get_logic_or_transition(v)
            if term is None:
                raise Exception(f"{self.name}: signal {v} has no transition relation or logic")
            parent_vars = term.get_vars()
            parents = normalize(parent_vars)
            dependencies[v.name].update(set(parents))
            to_visit.extend(parent_vars)
        # Compute cone of influence from dependency graph
        coi = {}
        visited = set()
        def visit(v_name):
            if v_name in visited:
                return {}
            visited.add(v_name)
            parents = dependencies[v_name]
            if v_name not in coi:
                # Use empty dict to preserve insertion order
                coi[v_name] = {v_name: ()}
            for p in parents:
                if p not in visited:
                    if p not in coi:
                        coi[p] = {p: ()}
                    coi[p] |= visit(p)
                coi[v_name] |= coi[p]
            return coi[v_name]
        for v in self.outputs:
            visit(v.name)
        coi = {k: list(v.keys()) for k, v in coi.items()}
        all_parent_names = set()
        needed_instance_names = set()
        for v in self.outputs:
            all_parent_names.update(coi[v.name])
            for n in coi[v.name]:
                needed_instance_names.add(n)
        new_state = [s for s in self.state if s.name in all_parent_names]
        new_ufs = [u for u in self.ufs if u.name in all_parent_names]
        new_next_ufs = [u for u in self.next_ufs if u.name in all_parent_names]
        new_instances = {}
        for n, i in self.instances.items():
            if n not in needed_instance_names:
                continue
            # Recursively perform DCE on child instances as well
            new_instances[n] = Instance(i.model.eliminate_dead_code(), i.inputs)
        def maybe_name(t):
            if isinstance(t, smt.Variable):
                return t.name
            elif isinstance(t, smt.OpTerm) and t.kind == smt.Kind.Select:
                return t.args[0].name
            raise Exception(f"{self.name}: cannot get name for {t}")
        new_transitions = {v: term for v, term in self.default_next.items() if maybe_name(v) in all_parent_names}
        new_logic = {v: term for v, term in self.logic.items() if maybe_name(v) in all_parent_names}
        return Model(
            self.name,
            inputs=self.inputs,
            outputs=self.outputs,
            state=new_state,
            instances=new_instances,
            default_next=new_transitions,
            logic=new_logic,
            ufs=new_ufs,
            next_ufs=new_next_ufs,
            generated_by=self.generated_by,
        )

    def flatten_state(self):
        """
        Pushes all intermediate logic and state transitions into a submodule.
        # TODO deal with submodules
        """
        # The only state that should remain in the top module is state with clocked udpates
        NEXT_PREFIX = "__next__"
        new_state = list(self.default_next.keys())
        new_inst_name = f"__logic__{self.name}_inst"
        sub_logic = dict(self.logic)
        sub_logic.update({
            v.add_prefix(NEXT_PREFIX): r for v, r in self.default_next.items()
        })
        submodel = Model(
            f"__logic__{self.name}",
            # Current value of state variables is treated as inputs to new submodule...
            inputs=self.inputs + new_state + [u.get_ref() for u in self.next_ufs],
            # ... and new value of state variables is the output
            outputs=self.outputs + [s.add_prefix(NEXT_PREFIX) for s in new_state],
            logic=sub_logic,
            ufs=self.ufs,
            generated_by=self.generated_by | GeneratedBy.FLATTEN,
        )
        inst_bindings = {i: i for i in self.inputs}
        inst_bindings.update({s: s for s in new_state})
        inst_bindings.update({s.get_ref(): s.get_ref() for s in self.next_ufs})
        return Model(
            self.name,
            inputs=self.inputs,
            outputs=self.outputs,
            state=new_state,
            instances={
                new_inst_name: Instance(submodel, inst_bindings)
            },
            default_next={
                s: s.add_prefix(new_inst_name + "." + NEXT_PREFIX)
                for s in new_state
            },
            logic={
                o: o.add_prefix(new_inst_name + ".")
                for o in self.outputs
            },
            next_ufs=self.next_ufs,
            generated_by=self.generated_by | GeneratedBy.FLATTEN,
        )

    def case_split(self, var_name: str, possible_values: Optional[Collection[int]]=None) -> "Model":
        """
        Automatically case splits this model on different values of `var_name`.
        `var_name` must be a boolean or bitvector variable, and cannot be an output.

        `possible_values` specifies the list of values that `var_name` can take on.
        If not specified, then all values encompassed by `var_name`'s sort will be
        used instead (e.g. a bv3 would have values 0-8).
        """
        if self.is_stateful:
            # If this model is stateful, then we must case split on logic only
            top = self.flatten_state()
            new_instances = {}
            for n, i in top.instances.items():
                if n == f"__logic__{top.name}_inst":
                    new_instances[n] = Instance(
                        i.model.case_split(var_name, possible_values),
                        i.inputs,
                    )
                else:
                    new_instances[n] = i
            return Model(
                top.name,
                inputs=top.inputs,
                outputs=top.outputs,
                state=top.state,
                instances=new_instances,
                default_next=top.default_next,
                logic=top.logic,
                next_ufs=top.next_ufs,
                generated_by=top.generated_by,
            )
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
        for v in self.state:
            if isinstance(v, smt.Variable) and v.name == var_name:
                # TODO validate possible_values if provided
                if possible_values is None:
                    if isinstance(v.sort, smt.BoolSort):
                        possible_values = (True, False)
                    elif isinstance(v.sort, smt.BVSort):
                        possible_values = range(0, 2 ** v.sort.bitwidth)
                    else:
                        raise TypeError(f"cannot case split on input {v}: case splits can only be performed on bool/bv variables")
                return self._case_split_var(v, possible_values)
        raise KeyError(f"cannot case split on {var_name}: no such input or state variable")

    def _case_split_input(self, input_var: smt.Variable, possible_values: Collection[int]):
        inputs = self.inputs[:]
        inputs.remove(input_var)
        return self._do_case_split(input_var, inputs, self.state, possible_values)

    def _case_split_var(self, state_var: smt.Variable, possible_values: List[int]):
        state = self.state[:]
        state.remove(state_var)
        return self._do_case_split(state_var, self.inputs, state, possible_values)

    def _do_case_split(self, split_var, inputs, state, possible_values):
        # module/instance suffixes corresponding to possible_values
        varname = split_var.name
        if possible_values == (True, False):
            suffixes = [f"{varname}__TRUE", f"{varname}__FALSE"]
        else:
            suffixes = [f"{varname}__{n:0{split_var.sort.bitwidth}b}" for n in possible_values]
        instances = {}
        inst_names = [f"_{self.name}__{suffix}_inst" for suffix in suffixes]
        for i, cs_value in enumerate(possible_values):
            if isinstance(split_var.sort, smt.BoolSort):
                cs_value_t = smt.BoolConst.T if cs_value else smt.BoolConst.F
            else:
                cs_value_t = smt.BVConst(cs_value, split_var.sort.bitwidth)
            bindings = {i: i for i in inputs}
            new_model = Model(
                name=f"_{self.name}__{suffixes[i]}",
                inputs=inputs,
                outputs=self.outputs,
                state=state,
                ufs=self.ufs,
                instances={
                    name: Instance(
                        # Rewrite expressions for all input bindings
                        inst.model,
                        {
                            v: t.replace_vars({split_var: cs_value_t})
                            for v, t in inst.inputs.items()
                        }
                    )
                    for name, inst in self.instances.items()
                },
                # TODO may need to replace LHS of assignments too? in case of indexing and stuff
                logic={
                    k: t.replace_vars({split_var: cs_value_t}).optimize() for k, t in self.logic.items()
                },
                default_next={
                    k: t.replace_vars({split_var: cs_value_t}).optimize() for k, t in self.default_next.items()
                },
                generated_by=GeneratedBy.CASE_SPLIT,
            )
            new_model = new_model.eliminate_dead_code()
            instances[inst_names[i]] = Instance(new_model, bindings)
        if isinstance(split_var.sort, smt.BoolSort):
            new_logic = {
                o: split_var.ite(
                    smt.Variable(inst_names[0] + "." + o.name, o.sort),
                    smt.Variable(inst_names[1] + "." + o.name, o.sort)
                ) for o in self.outputs
            }
        else:
            new_logic = {
                o: split_var.match_const({
                    i: smt.Variable(inst_names[i] + o.name, o.sort)
                    for i, v in enumerate(possible_values)
                }) for o in self.outputs
            }
        # State variables can always be eliminated because their values are taken care of
        # by the submodules
        return Model(
            name=self.name,
            inputs=self.inputs,
            outputs=self.outputs,
            state=[],
            ufs=self.ufs,
            instances=instances,
            logic=new_logic,
            default_next={},
            generated_by=self.generated_by | GeneratedBy.CASE_SPLIT,
        )


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
