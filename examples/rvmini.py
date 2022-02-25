import os
import subprocess
from subprocess import Popen, PIPE
import sys

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
        self.run_proc(["make", "verilatorM"], cwd=BASEDIR)

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
        with open(os.path.join(BASEDIR, "src/test/resources/rv32ui-p-add2.hex"), 'w') as src_file:
            for i in range(int(len(l)/4)):
                src_file.write(''.join(l[4*i:4*i+4]) +'\n')
        print("Generated hexfile!")
        self.run_proc(["./VTileM", "src/test/resources/rv32ui-p-add2.hex"], cwd=BASEDIR, ok_rcs=[0, 1])
        return read_csv(os.path.join(BASEDIR, "sample2.csv"), self.cycle_count)


def main():
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

    bv32 = smt.BVSort(32)
    x = smt.Variable("__shadow_0", bv32)
    y = smt.Variable("__shadow_1", bv32)
    start = smt.Variable("start", bv32)
    addbv = smt.OpTerm(smt.Kind.BVAdd, (start, start))
    subbv = smt.OpTerm(smt.Kind.BVSub, (start, start))
    orbv = smt.OpTerm(smt.Kind.BVOr, (start, start))
    solver = smt.SynthFun(
        "alu_add",
        (x, y),
        bv32,
        smt.Grammar(
            bound_vars=(x, y),
            input_vars=(start,),
            terms={start: (addbv, subbv, orbv),},
        )
    ).new_solver()

    model = RvMiniModel(
        ProjectConfig(os.path.join(BASEDIR, "symbiyosys"), clock_name="clock"),
        [32, 32],
        32,
        solver,
        SIGNALS,
        guidance
    )
    model.build_binary()
    model.main_sygus_loop()

if __name__ == '__main__':
    main()