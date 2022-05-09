from abc import ABC, abstractmethod
import argparse
# import csv
from dataclasses import dataclass
import math
import os
import re
from subprocess import Popen, PIPE
import textwrap
from typing import List, Mapping, Set

from rtl2synth.common import *
from rtl2synth.guidance import Guidance
from rtl2synth.lynth import smt
import rtl2synth.lynth.oracleinterface as oi
from rtl2synth.model import *
from rtl2synth.profile import PROFILE, Segment
from rtl2synth.sketch import ConcreteProgram, ProgramSketch
from rtl2synth.verilog import VcdWrapper

@dataclass
class ProjectConfig:
    sby_dir: str
    clock_name: str="clk"
    verilator_top: Optional[str] = None
    # TODO figure out what other paths we need

    def __post_init__(self):
        os.makedirs(self.sby_dir, exist_ok=True)

def _typecheck_arg(v, exp_type):
    assert isinstance(v, exp_type), f"argument expected {exp_type}, got {type(v)}"

class ModelBuilder(ABC):
    """
    An abstract class used to perform synthesis to fill in holes in a partial `Model` object.

    Implement `build_sim` and `simulate_and_read_signals` to allow usage of I/O examples
    during synthesis.
    """

    config: ProjectConfig
    sketch: ProgramSketch
    model: Model
    input_vars: List[smt.Variable]
    output_refs: List[smt.Variable]
    """
    A list of function references (encoded as SMT variables) whose outputs are checked
    against a particular RTL signal.

    Note that not every single synthesis function will have its output checked directly.
    """
    sf_map: Mapping[Tuple[str, str], smt.SynthFun]
    """Maps pairs of `(MODEL_NAME, FUNCTION_NAME)` to `SynthFun` objects."""
    guidance: Guidance
    o_ctx: oi.OracleCtx
    value_sets: Mapping[smt.Variable, Set[int]]
    """
    Maps input variables to a set of possible values. These constraints are
    applied when the I/O oracle generates values, and generated as assumptions
    when BMC is run.

    If an input variable is not in this set, its value is not constrained.
    """

    def __init__(
        self,
        config: ProjectConfig,
        sketch: ProgramSketch,
        model: Model,
        synthfun_grammars: Mapping[Tuple[str, str], Optional[smt.Grammar]],
        guidance: Guidance,
        value_sets: Optional[Mapping[smt.Variable, Set[int]]]=None,
    ):
        """
        Initializes a ModelBuilder object, which is used to fill in interpretations
        for uninterpreted functions.

        :param config: a `ProjectConfig` object that identifies paths to files needed during synthesis.
        :param sketch: a `ProgramSketch` to verify the model agains.
        :param synthfun_grammars: a map of `(MODEL_NAME, FUNCTION_NAME)` pairs to an optional `Grammar`.
            If no grammar is provided for a particular function, then the solver default grammar is used.
        :param guidance: a `Guidance` object that identifies when to sample signals from RTL simulation.
        """
        _typecheck_arg(config, ProjectConfig)
        _typecheck_arg(sketch, ProgramSketch)
        _typecheck_arg(model, Model)
        _typecheck_arg(synthfun_grammars, Mapping)
        _typecheck_arg(guidance, Guidance)
        if value_sets is not None:
            _typecheck_arg(value_sets, Mapping)
        self.config = config
        self.sketch = sketch
        self.model = model
        submodels = model.get_all_defined_models()
        submodel_map = {m.name: m for m in submodels}
        synthfuns = {}
        for (sf_mod, sf_name), g in synthfun_grammars.items():
            g_binds = g.bound_vars
            maybe_uf = submodel_map[sf_mod].find_uf_p(sf_name)
            if maybe_uf is None:
                raise Exception(f"Could not find UF {sf_name} in module {sf_mod}")
            if g_binds != maybe_uf.params:
                print(f"***WARNING: grammar changes type signature of UF {sf_mod}.{sf_name}***")
                original_args_s = ", ".join(f"{v.name} : {v.sort}" for v in maybe_uf.params)
                new_args_s = ", ".join(f"{v.name} : {v.sort}" for v in g_binds)
                print(f"            original args: ({original_args_s}); new args: ({new_args_s})")
                sf = smt.SynthFun(sf_name, g_binds, maybe_uf.sort, g)
            else:
                sf = maybe_uf.to_synthfun(g)
            synthfuns[(sf_mod, sf_name)] = sf
        solver = smt.Solver(synthfuns=list(synthfuns.values()))
        PROFILE.add_model(model, len(synthfuns))
        self.input_vars = sketch.get_hole_vars()
        out_refs = []
        for out_ref, _, _ in guidance.get_outputs():
            out_refs.append(out_ref)
        self.output_refs = out_refs
        missing = []
        i_var_set = set(self.input_vars)
        o_var_set = set(out_refs)
        for (mod_name, _), sf in synthfuns.items():
            # Ensure that all synthfuns and their inputs
            for p in sf.bound_vars:
                if p not in i_var_set:
                    missing.append(f"{sf.name}: input {p} not in guidance inputs")
            if sf.get_ref().add_prefix(mod_name + ".") not in o_var_set:
                missing.append(f"{sf.name}: missing from guidance outputs")
        if missing:
            for m in missing:
                print(m)
            raise Exception("Some synth fun inputs or outputs were missing (see above).")
        self.sf_map = synthfuns
        self.guidance = guidance
        self.o_ctx = oi.OracleCtx(solver)
        self.value_sets = value_sets or {}

    @property
    def signals(self):
        return self.guidance.signals

    @property
    def cycle_count(self):
        return self.guidance.num_cycles

    @property
    def solver(self):
        return self.o_ctx.solver

    @abstractmethod
    def build_sim(self):
        """
        Compiles the simulation binary.
        """
        pass

    @abstractmethod
    def simulate_and_read_signals(self, program: ConcreteProgram) -> Tuple[Mapping[str, int], List[Mapping[str, int]]]:
        """
        Invokes the simulation binary and reads the resulting signals.

        The first returned value is a map of signal qualified name to all signal widths.
        The second is a list indexed on cycles, where values are a map of signal qualified names to
        signal values.
        """
        pass

    def generate_program(self, input_values: Mapping[str, int]) -> ConcreteProgram:
        """
        Generates a concrete program from this instance's `ProgramSketch`, with variables
        replaced by the specified `input_values`.
        """
        return self.sketch.fill(input_values)

    def sample(self, input_values: Mapping[str, int]) -> Mapping[str, int]:
        """
        Runs a simulation with the provided inputs, and returns sampled output values.
        """
        print("Beginning sample")
        tc = self.generate_program(input_values)
        widths, signal_values = self.simulate_and_read_signals(tc)
        # TODO less hacky way to set these
        self.widths = widths
        self.signal_values = signal_values
        output_sigs = self.guidance.get_outputs()
        sampled_outputs = set()
        output_vals = {}
        def q2b(qp):
            """Converts qualified signal path ("top->reset") to a base path ("reset")"""
            try:
                i = qp.rindex("->")
                return qp[i+2:] # i is location of -, need to cut off after >
            except ValueError:
                return qp
        for sf_ref, signame, cond_or_cycle in output_sigs:
            # TODO less hacky way to do this
            if isinstance(cond_or_cycle, smt.Term):
                # TODO sample each signal exactly once,
                # and error if a signal is never sampled
                for cc, values in enumerate(signal_values):
                    should_sample = cond_or_cycle.eval({q2b(sig): v for sig, v in values.items()})
                    if bool(should_sample):
                        sampled_outputs.add(signame)
                        val = signal_values[cc][signame]
                        print(f"Sampled {signame}@{cc}={val}")
                        output_vals[sf_ref.name] = val
            else:
                cc = cond_or_cycle
                sampled_outputs.add(signame)
                val = signal_values[cc][signame]
                print(f"Sampled {signame}@{cc}={val}")
                output_vals[sf_ref.name] = val
        if len(output_vals) != len(output_sigs):
            raise Exception("Failed to sample some signals (check output trace): " + str({t[1] for t in output_sigs} - sampled_outputs))
        return output_vals

    def generate_test_block_verilog(self, signal_values, signal_widths, funcs: Mapping[str, smt.LambdaTerm]):
        """
        Creates a block of verilog code to check correctness for the function body.

        Each element in funcs is a concrete SMT function object, representing a guess made by the synthesis loop.
        """
        guidance = self.guidance
        clock_name = self.config.clock_name
        ctr_width = int(math.ceil(math.log(guidance.num_cycles, 2)))
        signalnames = [qpath for s in self.signals for qpath in s.get_all_qp_instances()]
        basenames = [basename for s in self.signals for basename in s.get_all_bp_instances()]
        def get_width(qp):
            """Gets width of the signal corresponding to the provided qualified path."""
            return signal_widths[qp]

        def q2b(qp):
            """Converts qualified signal path ("top->reset") to a base path ("reset")"""
            try:
                i = qp.rindex("->")
                return qp[i+2:] # i is location of -, need to cut off after >
            except ValueError:
                return qp

        def func_anno(atype, qp_var):
            """
            Gets the expression for an output annotation.
            Also updates `out_exprs`.
            """
            assert atype.is_output(), atype
            vs = atype.expr.get_vars()
            assert len(vs) == 1, vs
            v = vs[0]
            if atype.bounds:
                raise NotImplementedError()
            func = funcs[v.get_base().name]
            out_exprs[v] = func.body.replace_vars(shadow_param_map)
            return out_vars[v].op_eq(qp_var)

        ctr = smt.bv_variable("__lift_cc", ctr_width)
        ctr_values = [smt.BVConst(i, ctr_width) for i in range(guidance.num_cycles)]
        ctr_cases = [] # Each item is a tuple of (iterator condition, assumptions, assertions)
        # Maps input variable to shadow
        shadow_param_map = {v: v.add_prefix("__shadow_") for v in self.input_vars}
        # Ensures variables are only sampled once
        sampled_vars = {v: smt.bool_variable("__sampled_" + v.name) for v in self.input_vars + self.output_refs}
        out_vars = {v: v.add_prefix("__hypothesis_") for v in self.output_refs}
        out_exprs = {}
        for stepnum in range(guidance.num_cycles):
            itercond = ctr.op_eq(ctr_values[stepnum])
            assumes = []
            asserts = []
            for signal in guidance.signals:
                # Iterate over all indices for vectors
                for qp in signal.get_all_qp_instances():
                    # TODO convert this into an index expression if necessary
                    qp_var = smt.bv_variable(q2b(qp), get_width(qp))
                    atype = guidance.get_annotation_at(qp, stepnum)
                    if atype is None or atype.is_dont_care():
                        continue
                    bounds = atype.bounds
                    qp_vars = []
                    if bounds:
                        for b in bounds:
                            qp_vars.append(qp_var[b[0]:b[1]])
                    else:
                        qp_vars = [qp_var]
                    for qp_var in qp_vars:
                        if atype.is_assume():
                            # Add assume statement
                            constval = smt.BVConst(signal_values[stepnum][qp], get_width(qp))
                            if bounds:
                                constval = constval[bounds[0]:bounds[1]].eval({})
                            assumes.append(qp_var.op_eq(constval))
                        elif atype.is_param():
                            # Add new shadow register
                            # TODO add comments to assumes somehow?
                            lhs = atype.expr.replace_vars(shadow_param_map)
                            if bounds:
                                lhs = lhs[bounds[0]:bounds[1]]
                            assumes.append(lhs.op_eq(qp_var))
                        elif atype.is_output():
                            # Assert output
                            asserts.append(func_anno(atype, qp_var))
                        else:
                            raise TypeError(f"invalid annotation {atype}")
            ctr_cases.append((itercond, assumes, asserts))

        pred_cases_l = []
        for signal in guidance.signals:
            for qp in signal.get_all_qp_instances():
                first = True
                # TODO convert this into an index expression if necessary
                qp_var = smt.bv_variable(q2b(qp), get_width(qp))
                for cond, anno_list in guidance.get_predicated_annotations(qp).items():
                    # Add condition
                    if first:
                        s = f"if ({cond.to_verilog_str()}) begin\n"
                        first = False
                    elif cond == smt.BoolConst.T:
                        s = f"else begin\n"
                    else:
                        s = f"else if ({cond.to_verilog_str()}) begin\n"
                    for anno in anno_list:
                        if anno.is_dont_care():
                            continue
                        bounds = anno.bounds
                        qp_expr = qp_var
                        # Add assume/assert
                        if anno.is_assume():
                            s += f"    case ({ctr.to_verilog_str()})\n"
                            # Add assume statements
                            for cc in ctr_values:
                                s += f"        {cc.to_verilog_str()}: begin\n"
                                constval = smt.BVConst(signal_values[cc.val][qp], get_width(qp))
                                if bounds:
                                    for b in bounds:
                                        c = constval[b[0]:b[1]].eval({})
                                        e = qp_expr[b[0]:b[1]]
                                        s += f"            assume ({e.op_eq(c).to_verilog_str()});\n"
                                else:
                                    s += f"            assume ({qp_expr.op_eq(constval).to_verilog_str()});\n"
                                s += "        end\n"
                            s += f"    endcase\n"
                        elif anno.is_param():
                            anno_var = anno.expr.get_vars()[0]
                            sample_var = sampled_vars[anno_var]
                            # TODO add comments to assumes somehow?
                            lhs = anno.expr.replace_vars(shadow_param_map)
                            s += f"    if (!{sample_var.to_verilog_str()}) begin\n"
                            if bounds:
                                for b in bounds:
                                    s += f"        assume ({lhs.op_eq(qp_expr[b[0]:b[1]]).to_verilog_str()});\n"
                            else:
                                s += f"        assume ({lhs.op_eq(qp_expr).to_verilog_str()});\n"
                            s += f"        {sample_var.to_verilog_str()} <= 1;\n"
                            s += f"    end\n"
                        elif anno.is_output():
                            # Assert output
                            # TODO allow for a more coherent mapping from synth funs to outputs
                            anno_var = anno.expr.get_vars()[0]
                            sample_var = sampled_vars[anno_var]
                            s += f"    if (!{sample_var.to_verilog_str()}) begin\n"
                            s += f"        assert ({func_anno(anno, qp_expr).to_verilog_str()});\n"
                            s += f"        {sample_var.to_verilog_str()} <= 1;\n"
                            s += f"    end\n"
                        else:
                            raise TypeError(f"invalid annotation {anno}")
                    s += "end"
                    pred_cases_l.append(s)

        shadow_decls = "\n".join(s.get_decl().to_verilog_str(is_reg=True, anyconst=True) for s in shadow_param_map.values())
        sampled_decls = "\n".join(s.get_decl(init_value=smt.BVConst(0, 1)).to_verilog_str(is_reg=True) for s in sampled_vars.values())
        out_decls = "\n".join(s.get_decl().to_verilog_str() for s in out_vars.values())
        out_assigns = "\n".join(f"assign __hypothesis_{v} = {expr.to_verilog_str()};" for v, expr in out_exprs.items())
        ctr_cases_l = []
        for itercond, assumes, asserts in ctr_cases:
            s = f"if ({itercond.to_verilog_str()}) begin\n"
            assumes_s = "\n".join(f"    assume ({a.to_verilog_str()});" for a in assumes)
            if asserts:
                asserts_s = "\n" + "\n".join(f"    assert ({a.to_verilog_str()});" for a in asserts)
            else:
                asserts_s = ""
            ctr_cases_l.append(s + assumes_s + asserts_s + "\nend")

        set_assumes = "\n".join("    assume(" + \
            " || ".join(f"{shadow_param_map[v].to_verilog_str()} == {i}" for i in vals) + \
            ");"
            for v, vals in self.value_sets.items()
        )

        return shadow_decls + "\n" + \
            sampled_decls + "\n" + \
            out_decls + "\n" + \
            out_assigns + "\n" + \
            textwrap.dedent(f"""\

            {ctr.get_decl(smt.BVConst(0, ctr_width)).to_verilog_str(is_reg=True)}
            always @(posedge {clock_name}) begin
                {ctr.to_verilog_str()} <= {ctr.to_verilog_str()} + 1;
            end
            """) + f"always @(posedge {clock_name}) begin\n" + \
            set_assumes + "\n" + \
            textwrap.indent("\n".join(ctr_cases_l), "    ") + \
            "\n\n" + textwrap.indent("\n".join(pred_cases_l), "    ") + \
            "\nend"

    def run_bmc(self, signal_values, signal_widths, hypothesis_funcs: Mapping[str, smt.LambdaTerm]) -> bool:
        """
        Runs BMC (hardcoded to be symbiyosys) and returns true on success.
        """
        formalblock = self.generate_test_block_verilog(
            signal_values,
            signal_widths,
            hypothesis_funcs,
        )
        # print(formalblock)
        # TODO it seems like we currently need an empty verilator.config file to be included by Tile.v
        with open(os.path.join(self.config.sby_dir, "Formal.v"), 'w') as f:
            f.write(formalblock)
        lines = self.run_proc(
            ["sby", "-f", "corr.sby", "taskBMC"],
            cwd=self.config.sby_dir,
            quiet=False,
            ok_rcs=(0, 1, 2)
        )
        ok = 'PASS' in lines[-1]
        if not ok:
            self.add_cex(*self._parse_sby_cex(lines))
        return ok

    def _parse_sby_cex(self, sby_lines) -> Mapping[smt.Variable, int]:
        """
        Parses a counterexample from symbiyosys output.

        Inputs (shadow variables) are read from stdout.
        Output is read from the VCD.
        (we could add a shadow variable to represent the output so it gets parsed back from stdout,
        but this adds a significant amount of time to the solver)
        """
        # Assume sby outputs variables in reverse order of declaration
        # (last input is first, etc.)
        in_map = {}
        in_var_name_map = {v.name: v for v in self.input_vars}
        shadow_re = re.compile("__shadow_([a-zA-Z0-9_]+)")
        for line in sby_lines:
            if "Value for anyconst" in line:
                var_name = shadow_re.findall(line)[0]
                # Value is always the last token in the line
                i_val = int(line.split()[-1])
                in_map[in_var_name_map[var_name]] = i_val
        if self.config.verilator_top:
            top_prefix = self.config.verilator_top + "."
        else:
            top_prefix = self.model.name + "."
        vcd_r = VcdWrapper(
            os.path.join(self.config.sby_dir, "corr_taskBMC/engine_0/trace.vcd"),
            top_prefix + self.config.clock_name
        )
        for v in self.input_vars:
            if v not in in_map:
                raise Exception(f"No value for variable {v.name} in sby counterexample")
        out_map = {}
        out_annos = self.guidance.get_outputs()
        for sf_ref, sig_name, cc_or_pred in out_annos:
            if isinstance(cc_or_pred, smt.Term):
                cond = cc_or_pred
                all_vars = cond.get_vars()
                for cc in range(self.guidance.num_cycles):
                    values = {
                        v.name: vcd_r.get_value_at(top_prefix + v.name, cc)
                        for v in all_vars
                    }
                    should_sample = cond.eval(values)
                    if should_sample:
                        out_map[sf_ref] = vcd_r.get_value_at(sig_name.replace("->", "."), cc)
            else:
                out_map[sf_ref] = vcd_r.get_value_at(sig_name, cc_or_pred)
        return in_map, out_map

    def verify(self, funcs: Mapping[str, smt.LambdaTerm]):
        # TODO make less hacky
        if not hasattr(self, "signal_values"):
            # Because the signal variable width may not match the width of the ISA-level input
            # to the program sketch, the max value of the signal may exceed the max allowable value
            self.sample({v.name: 0 for v in self.input_vars})
            # self.sample([random.randint(0, 2 ** v.c_bitwidth() - 1) for v in self.input_vars])
        signal_values = self.signal_values
        widths = self.widths
        return self.run_bmc(signal_values, widths, funcs)

    def run_proc(self, args: List[str], *, cwd: str, quiet=True, ok_rcs=(0,)) -> List[str]:
        """
        Runs the specified process, printing stdout live.
        Prints stderr and raises an exception if the return code is not in OK_RCS (only 0 by default).
        Returns stdout as a list of lines.
        """
        process = Popen(args, stdout=PIPE, stderr=PIPE, cwd=cwd)
        # https://stackoverflow.com/questions/4417546/
        lines = []
        assert process.stdout is not None
        assert process.stderr is not None
        for stdout_line in iter(process.stdout.readline, b""):
            line = stdout_line.decode("utf-8")[:-1] # strip newline char
            lines.append(line)
            if not quiet:
                print(line)
        process.stdout.close()
        rc = process.wait()
        if rc not in ok_rcs:
            print("===STDOUT===")
            print("\n".join(lines))
            print("===STDERR===")
            print(process.stderr.read().decode("utf-8"))
            raise Exception(f"Process executed with exit code {rc}, see full output above.")
        return lines

    def _add_io_oracle(self, io_replay_path=None, io_log_path=None):
        if io_replay_path is not None:
            io = oi.IOOracle.from_call_logs(
                "io",
                self.input_vars,
                self.output_refs,
                lambda *args: self.sample(*args),
                io_replay_path,
                new_log_path=io_log_path,
                value_sets=self.value_sets,
            )
        else:
            io = oi.IOOracle(
                "io",
                self.input_vars,
                self.output_refs,
                lambda *args: self.sample(*args),
                log_path=io_log_path,
                value_sets=self.value_sets,
            )
        self.o_ctx.add_oracle(io)

    def _add_correctness_oracle(self):
        corr = oi.CorrectnessOracle("corr", self.input_vars, self.output_refs, self.verify)
        self.o_ctx.add_oracle(corr)

    def add_cex(self, input_vals: Mapping[smt.Variable, int], output_vals: Mapping[smt.Variable, int]):
        print("Adding counterexample: (" + ", ".join(f"{k}={i}" for k, i in input_vals.items()) + \
                f") -> (" + ", ".join(f"{k.name}={i}" for k, i in output_vals.items()) + ")")
        self.o_ctx.oracles["io"].add_cex(input_vals, output_vals)

    def main_sygus_loop(self) -> Model:
        # parser = argparse.ArgumentParser(description="Run synthesis loop.")
        # parser.add_argument(
        #     "--io-replay-path",
        #     nargs="?",
        #     type=str,
        #     default=None,
        #     help="Log file from which to replay inputs to the I/O oracle."
        # )
        # parser.add_argument(
        #     "--io-log-path",
        #     nargs="?",
        #     type=str,
        #     default=None,
        #     help="Log file to which I/O inputs and outputs from this run are saved."
        # )
        # args = parser.parse_args()
        # self._add_io_oracle(io_replay_path=args.io_replay_path, io_log_path=args.io_log_path)
        self._add_io_oracle(io_replay_path=None, io_log_path=None)
        self._add_correctness_oracle()
        solver = self.solver
        prev_candidates = []
        self.build_sim()
        while True:
            print("Correctness oracle returned false, synthesizing new candidates")
            io_o = self.o_ctx.oracles["io"]
            replayed_inputs = io_o.next_replay_input()
            if replayed_inputs is not None:
                inputs = replayed_inputs
                print("REPLAYING INPUTS:")
                for i, v in enumerate(sf.bound_vars):
                    print(f"- {v.name} (input {i + 1}):", inputs[i])
            else:
                if len(io_o.cex_inputs) != 0:
                    inputs = io_o.cex_inputs[-1]
                else:
                    inputs = io_o.new_random_inputs()
                # inputs = []
                # for i, v in enumerate(sf.bound_vars):
                #     inputs.append(input(f"{v.name} (input {i + 1}): "))
                # inputs = tuple(inputs)
            # TODO add blocking constraint to prevent sygus from repeating guesses?
            solver.reinit_cvc5()
            self.o_ctx.call_oracle("io", {v.name: i for v, i in inputs.items()})
            io_o.save_call_logs()

            solver.clear_constraints()
            self.o_ctx.apply_all_constraints(solver, {
                "io": (self.model, self.sf_map),
            })
            print("Running synthesis...")
            PROFILE.push(Segment.SYNTH_ENGINE)
            sr = solver.check_synth()
            PROFILE.pop()
            if sr.is_unsat:
                print("Synthesis done, candidates are:")
                candidates = sr.solution
                for name, cand in candidates.items():
                    print("   ", name, "=", cand)
                prev_candidates.append(candidates)
                cr = self.o_ctx.call_oracle("corr", candidates)
                # Counterexample is implicitly added by the oracle function
                is_correct = cr.outputs
                if is_correct:
                    print("=== All oracles passed. Found a solution: ===")
                    for name, cand in candidates.items():
                        print("   ", name, "=", cand)
                        print("   ", name, "=", cand.to_sygus2())
                    io_o.save_call_logs()
                    model = self.model
                    for (mod_name, uf_name) in self.sf_map:
                        model = model.replace_mod_uf_transition(
                            mod_name,
                            uf_name,
                            candidates[uf_name].body,
                        )
                    return model
            else:
                print("No solution found. There is likely a bug in one of the oracles.")
                print("I/O history:")
                for call in io_o.calls:
                    print(call)
                print("BMC counterexamples:")
                for cex in io_o.cexs():
                    print(cex)
                return None
