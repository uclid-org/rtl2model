"""
Tests higher-level components of the synthesis loop.
"""

import unittest
import os
import subprocess
from subprocess import Popen, PIPE

import easyila
from easyila.guidance import Guidance, AnnoType
from easyila.synthesis_template import *
from easyila.testcase import *
import easyila.gen_config as gen_config
import easyila.lynth.smt as smt

REPO_BASE_DIR = subprocess.run(
        "git rev-parse --show-toplevel",
        shell=True,
        capture_output=True,
        check=True
    ).stdout.decode("utf-8").strip()

BASEDIR = os.path.join(REPO_BASE_DIR, "processors/riscv-mini/")


class RvMiniModel(HwModel):
    def build_binary(self):
        gen_config.generate_config(
            signals=self.signals,
            target_sim_dir=os.path.join(BASEDIR, "src/main/cc/"),
            target_verilog_dir=BASEDIR,
            root="Tile"
        )
        process = Popen(["make", "verilatorM"], stdout=PIPE, cwd=BASEDIR)
        (out, err) = process.communicate()
        rc = process.wait()
        if rc != 0:
            print("FAILED TO BUILD BINARY")
            print("*** STDOUT ***")
            print(out.decode("utf-8"))
            if err:
                print("*** STDERR ***")
                print(err.decode("utf-8"))
            sys.exit(1)

    def generate_program(self, inputs) -> TestCase:
        return TestCase(
            xInstrWord(0, 8) * (31 * 4),    # @000 496 bytes of 0s
            xInstrWord('00000013'),         # @496 nop
            xInstrWord(0, 8) * 3,           # @500 through 511:  more 0s
            xInstrWord('00c586b3') * 2,     # @512 add a3, a1, a2
            bInstrWord(f"{int(inputs[0]):0{12}b}00000000011000010011"), # @516 addi a2, x0, ???
            bInstrWord(f"{int(inputs[1]):0{12}b}00000000010110010011"), # @520 addi a1, x0, ???
            xInstrWord('00c586b3') * 20     # @524 (and later) add a3, a1, a2
            # a1 is x11, a2 is x12, a3 is x13
            # remember that instructions don't commit until they reach the last stage, making
            # cycle 14 (IF_PC=532) the minimum -- we can overshoot safely though since there
            # are just more of the same instruction over and over after
            # the trace seems to stall for some reason though? TODO ask adwait about that
            # for now, the pattern seems to be that 4 adds retire successfully, then the next add
            # stalls for an additional 3 cycles
        )

    def simulate_and_read_signals(self, testcase):
        l = testcase._inject(BinaryRepr.HEX)
        print("Generated hexfile!")
        with open(os.path.join(BASEDIR, "src/test/resources/rv32ui-p-add2.hex"), 'w') as src_file:
            for i in range(int(len(l)/4)):
                src_file.write(''.join(l[4*i:4*i+4]) +'\n')
        process = Popen(["./VTileM", "src/test/resources/rv32ui-p-add2.hex"], stdout=PIPE, cwd=BASEDIR)
        (_, _) = process.communicate()
        _ = process.wait()
        ### CHANGE ME
        # should be 14 + some multiple of 7 i guess
        cycle_count = 14 + 7
        ###
        widths, signalvalues = read_csv(os.path.join(BASEDIR, "sample2.csv"), cycle_count)
        return widths, signalvalues


class TestIntegration:
    def test_can_import_cvc5(self):
        """
        Tests that necessary dependencies etc. have installed properly, and the library can be initialized.
        """
        import pycvc5 as cvc5
        cvc5.Solver()

    def init_model(self):
        cycle_count = 21
        SIGNALS = [
            S("Tile", "reset", 1),
            S("Tile", "clock", 1),
            S("Tile", "lft_tile_pc", 32),
            S("Tile", "lft_tile_fe_pc", 32),
            S("Tile", "lft_tile_ew_pc", 32),
            S("Tile", "lft_tile_fe_inst", 32),
            S("Tile", "lft_tile_regFile_io_waddr", 5),
            S("Tile", "lft_tile_regFile_io_wdata", 32),
            S("Tile", "lft_tile_regFile_io_raddr1", 5),
            S("Tile", "lft_tile_regFile_io_raddr2", 5),
            S("Tile", "lft_tile_regFile_io_rdata1", 32),
            S("Tile", "lft_tile_regFile_io_rdata2", 32),
            S("Tile", "lft_tile_alu_io_A", 32),
            S("Tile", "lft_tile_alu_io_B", 32),
            S("Tile", "lft_tile_alu_io_alu_op", 32),
            S("Tile", "lft_tile_alu_io_out", 32),
            S("Tile", "lft_tile_alu_io_sum", 32),
            S("Tile", "lft_tile_regs_10", 32),
            S("Tile", "lft_tile_regs_11", 32),
            S("Tile", "lft_tile_regs_12", 32),
            S("Tile", "lft_tile_regs_13", 32),
        ]
        guidance = Guidance(SIGNALS, cycle_count)
        for sig in ["reset", "lft_tile_pc", "lft_tile_fe_pc", "lft_tile_ew_pc", "lft_tile_fe_inst",]:
            guidance.annotate(sig, AnnoType.ASSM)
        # a1 (shadow var)
        guidance.annotate("lft_tile_regs_11", {12: AnnoType.PARAM})
        # a2 (shadow var)
        guidance.annotate("lft_tile_regs_12", {12: AnnoType.PARAM})
        # a3 (output)
        guidance.annotate("lft_tile_regs_13", {13: AnnoType.OUTPUT})

        model = RvMiniModel(
            ProjectConfig(os.path.join(BASEDIR, "symbiyosys")),
            [32, 32],
            32,
            None,
            SIGNALS,
            guidance
        )
        model.build_binary()
        return model

    def test_sample(self):
        model = self.init_model()
        r = model.sample([1, 2])
        assert len(r) > 0
        assert r is not None

    def test_generate_new_test(self):
        model = self.init_model()
        model.sample([1, 2])
        widths, signalvalues = read_csv(os.path.join(BASEDIR, "sample2.csv"), model.cycle_count)
        formalblock = model.generate_new_test(
            signalvalues,
            widths,
            smt.LambdaTerm(
                (smt.Variable("x", smt.BVSort(32)), smt.Variable("y", smt.BVSort(32))),
                smt.OpTerm(
                    smt.Kind.BVAdd,
                    [smt.Variable("x", smt.BVSort(32)), smt.Variable("y", smt.BVSort(32))],
                )
            )
        )
        assert isinstance(formalblock, str)

    """
    def test_run_bmc(self):
        model = self.init_model()
        model.sample([1, 2])
        widths, signalvalues = read_csv(os.path.join(BASEDIR, "sample2.csv"), model.cycle_count)
        r = model.run_bmc(
            signalvalues,
            widths,
            smt.LambdaTerm(
                (smt.Variable("x", smt.BVSort(32)), smt.Variable("y", smt.BVSort(32))),
                smt.OpTerm(
                    smt.Kind.BVAdd,
                    [smt.Variable("x", smt.BVSort(32)), smt.Variable("y", smt.BVSort(32))],
                )
            )
        )
        assert isinstance(r, bool)
    """
