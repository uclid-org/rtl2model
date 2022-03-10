from abc import ABC, abstractmethod
import argparse
# import csv
from dataclasses import dataclass
import math
import os
import random
from subprocess import Popen, PIPE
from typing import List

from easyila.common import *
from easyila.guidance import Guidance, AnnoType
from easyila.lynth import smt
from easyila.testcase import TestCase
import easyila.lynth.oracleinterface as oi
import easyila.verification as v

@dataclass
class ProjectConfig:
    sby_dir: str
    clock_name: str="clk"
    # TODO figure out what other paths we need

    def __post_init__(self):
        os.makedirs(self.sby_dir, exist_ok=True)

class HwModel(ABC):
    config: ProjectConfig
    # TODO come up with more explicit mappings for input name > width
    # rather than just ordinal position
    input_widths: List[int]
    output_width: int
    signals: List[SampledSignal]
    guidance: Guidance
    o_ctx: oi.OracleCtx

    def __init__(
        self,
        config: ProjectConfig,
        input_widths: List[int],
        output_width: int,
        solver: smt.Solver,
        signals: List[SampledSignal],
        guidance: Guidance
    ):
        self.config = config
        self.input_widths = input_widths
        self.output_width = output_width
        self.signals = signals
        self.guidance = guidance
        self.o_ctx = oi.OracleCtx(solver)

    @property
    def cycle_count(self):
        return self.guidance.num_cycles

    @property
    def solver(self):
        return self.o_ctx.solver

    @abstractmethod
    def build_binary(self):
        """
        Compiles the simulation binary.
        """
        pass

    @abstractmethod
    def generate_program(self, inputs) -> TestCase:
        """
        Produces a TestCase program to be run during simulation.
        INPUTS is a list of inputs to the model that may be used in constructing the program.
        """
        pass

    @abstractmethod
    def simulate_and_read_signals(self, testcase) -> Tuple[List[int], List[List[int]]]:
        """
        Invokes the simulation binary and reads the resulting signals.

        The first returned value is a list of all signal widths.
        The second is a 2D array of all signal values.
        TODO name these signals intead of just leaving them in a list
        """
        pass

    def sample(self, inputs) -> List[int]:
        """
        Runs a simulatiion with the provided inputs, and returns sampled output values.

        TODO name outputs instead of just ordering them
        """
        print("Beginning sample")
        tc = self.generate_program(inputs)
        widths, signal_values = self.simulate_and_read_signals(tc)
        # TODO less hacky way to set these
        self.widths = widths
        self.signal_values = signal_values
        output_sigs = self.guidance.get_outputs()
        output_vals = []
        for signame, cycle in output_sigs:
            # TODO less hacky way to do this
            sigidx = [i for i, s in enumerate(self.guidance.signals) if s.get_qualified_path() == signame][0]
            output_vals.append(signal_values[cycle][sigidx])
        return output_vals

    def generate_new_test(self, signal_values, signal_widths, func: smt.LambdaTerm):
        """
        Creates a new correctness check for the function body.

        func is a concrete SMT function object, representing a guess made by the synthesis loop.
        """
        guidance = self.guidance
        clock_name = self.config.clock_name
        width = int(math.ceil(math.log(guidance.num_cycles, 2)))
        signalnames = [qpath for s in self.signals for qpath in s.get_all_qp_instances()]
        basenames = [basename for s in self.signals for basename in s.get_all_bp_instances()]
        base_to_qualified = dict(zip(basenames, signalnames))
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

        ctr_block = v.counter("counter", width, trigger=v.SignalRef(clock_name))
        ctr_ref = v.RegRef("counter", width)
        ctr_values = [v.BVConst(i, width) for i in range(2 ** (width + 1))]
        ctr_cases = []
        shadow_decls = []
        numshadow = 0

        for stepnum in range(guidance.num_cycles):
            itercond = ctr_ref == ctr_values[stepnum]
            stmts: List[v.Statement] = []
            for ind, signal in enumerate(guidance.signals):
                # Iterate over all indices for vectors
                for qp in signal.get_all_qp_instances():
                    atype = guidance.get_annotation_at(qp, stepnum)
                    if atype == AnnoType.DC:
                        pass
                    elif atype == AnnoType.ASSM:
                        # Add assume statement
                        constval = v.BVConst(signal_values[stepnum][ind], get_width(qp), base=v.Base.HEX)
                        stmts.append(
                            v.Assume(v.SignalRef(q2b(qp)) == constval)
                        )
                    elif atype == AnnoType.PARAM:
                        # Add new shadow register
                        new_shadow = v.RegDecl(f"__shadow_{numshadow}", get_width(qp), anyconst=True)
                        shadow_decls.append(new_shadow)
                        stmts.append(
                            v.Assume(new_shadow.get_ref() == v.SignalRef(q2b(qp)), comment="synthfun parameter")
                        )
                        numshadow += 1
                    elif atype == AnnoType.OUTPUT:
                        # Assert output
                        # TODO allow for a more coherent mapping from synth funs to outputs
                        stmts.append(
                            v.Assert(func.body.to_verif_dsl() == v.SignalRef(q2b(qp)), comment="synthfun output")
                        )
                    else:
                        raise NotImplementedError()
            # TODO fix this lol
            if len(stmts) > 0:
                ite = v.IteStatement(itercond, v.StatementSeq(stmts), None)
            else:
                ite = v.IteStatement(itercond, v.StatementSeq([]), None)
            ctr_cases.append(ite)

        return v.StatementSeq(shadow_decls + [
            ctr_block,
            v.AlwaysAt(v.Edge.POS, v.SignalRef(clock_name), ctr_cases)
        ]).to_verilog()

    def run_bmc(self, signal_values, signal_widths, hypothesis_func: smt.LambdaTerm):
        """
        Runs BMC (for now, hardcoded to be symbiyosys) and returns true on success.
        """
        formalblock = self.generate_new_test(
            signal_values,
            signal_widths,
            hypothesis_func,
        )
        # print(formalblock)
        # TODO it seems like we currently need an empty verilator.config file to be included by Tile.v
        with open(os.path.join(self.config.sby_dir, "Formal.v"), 'w') as f:
            f.write(formalblock)
        lines = self.run_proc(["sby", "-f", "corr.sby", "taskBMC"], cwd=self.config.sby_dir, ok_rcs=(0, 1, 2))
        return 'PASS' in lines[-1]

    def verify(self, func: smt.LambdaTerm):
        # TODO make less hacky
        if not hasattr(self, "signal_values"):
            self.sample([random.randint(0, 100), random.randint(0, 100)])
        signal_values = self.signal_values
        widths = self.widths
        return self.run_bmc(signal_values, widths, func)

    def run_proc(self, args: List[str], cwd: str, ok_rcs=(0,)) -> List[str]:
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
            print(line)
        process.stdout.close()
        rc = process.wait()
        if rc not in ok_rcs:
            print("===STDERR===")
            print(process.stderr.read().decode("utf-8"))
            raise Exception(f"Process executed with exit code {rc}, see full output above.")
        return lines

    def _add_io_oracle(self, io_replay_path=None, io_log_path=None):
        if io_replay_path is not None:
            io = oi.IOOracle.from_call_logs(
                "io",
                self.input_widths,
                self.output_width,
                lambda *args: self.sample(*args)[0],
                io_replay_path,
                new_log_path=io_log_path
            )
        else:
            io = oi.IOOracle(
                "io",
                self.input_widths,
                self.output_width,
                lambda *args: self.sample(*args)[0],
                log_path=io_log_path
            )
        self.o_ctx.add_oracle(io)

    def _add_correctness_oracle(self):
        corr = oi.CorrectnessOracle("corr", self.verify)
        self.o_ctx.add_oracle(corr)

    def main_sygus_loop(self):
        parser = argparse.ArgumentParser(description="Run synthesis loop.")
        parser.add_argument(
            "--io-replay-path",
            nargs="?",
            type=str,
            default=None,
            help="Log file from which to replay inputs to the I/O oracle."
        )
        parser.add_argument(
            "--io-log-path",
            nargs="?",
            type=str,
            default=None,
            help="Log file to which I/O inputs and outputs from this run are saved."
        )
        args = parser.parse_args()
        self._add_io_oracle(io_replay_path=args.io_replay_path, io_log_path=args.io_log_path)
        self._add_correctness_oracle()
        solver = self.solver
        sf = solver.synthfuns[0]
        while True:
            print("Correctness oracle returned false, please provide more constraints: ")
            # TODO key on names instead of just by order
            io_o = self.o_ctx.oracles["io"]
            replayed_inputs = io_o.next_replay_input()
            # TODO prompt for input before anything else
            if replayed_inputs is not None:
                inputs = replayed_inputs
                print("REPLAYING INPUTS:")
                for i, v in enumerate(sf.bound_vars):
                    print(f"- {v.name} (input {i + 1}):", inputs[i])
            else:
                inputs = []
                for i, v in enumerate(sf.bound_vars):
                    inputs.append(input(f"{v.name} (input {i + 1}): "))
            solver.reinit_cvc5()
            self.o_ctx.call_oracle("io", inputs)
            self.o_ctx.oracles["io"].save_call_logs()

            self.o_ctx.apply_all_constraints(solver, {"io": sf})
            sr = solver.check_synth()
            if sr.is_unsat:
                solution = sr.solution
                # pycvc5_utils.print_synth_solutions(terms, solution)
                print(solution.to_sygus2())
                cr = self.o_ctx.call_oracle("corr", solution)
                is_correct = cr.output
                if is_correct:
                    print("All oracles passed. Found a solution: ")
                    print(solution.to_sygus2())
                    self.o_ctx.oracles["io"].save_call_logs()
                    break

            else:
                print("Sorry, no solution found!")
                break

