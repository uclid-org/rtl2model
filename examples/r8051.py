import os
import subprocess

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

BASEDIR = os.path.join(REPO_BASE_DIR, "processors/R8051/")

class R8051Model(HwModel):
    def build_binary(self):
        gen_config.generate_config(
            signals=self.signals,
            target_sim_dir=BASEDIR,
            target_verilog_dir=BASEDIR,
            root="top"
        )
        self.run_proc(["make", "default"], cwd=BASEDIR)

    def generate_program(self, inputs) -> TestCase:
        i0 = hex(int(inputs[0]))[2:]
        i1 = hex(int(inputs[1]))[2:]
        # https://www.keil.com/support/man/docs/is51/is51_opcodes.htm
        return TestCase(
            xInstrWord('00'),       # nop
            xInstrWord('78'),       # MOV R0, imm
            xInstrWord(i0),         # (imm)
            xInstrWord('74'),       # MOV A, imm
            xInstrWord(i1),         # (imm)
            xInstrWord('28'),       # ADD A, R0
            xInstrWord('00'),       # NOP
            xInstrWord('00'),
            xInstrWord('00'),
            xInstrWord('31'),       # ACALL addr11
            xInstrWord('31'),
            xInstrWord('31'),
            xInstrWord('31'),
            xInstrWord('31'),
            xInstrWord('31'),
            xInstrWord('31')
        )

    def simulate_and_read_signals(self, testcase):
        with open(os.path.join(BASEDIR, "myhello"), "wb") as f:
            f.write(testcase._inject(BinaryRepr.BYTE))
        self.run_proc(["./obj_dir/Vtop"], cwd=BASEDIR)
        return read_csv(os.path.join(BASEDIR, "traces/tr.csv"), self.cycle_count)

def main():
    cycle_count = 10
    SIGNALS = [
        S("tb", "clk", 1),
        S("tb", "rst", 1),
        S("tb", "lft_pc", 16),
        S("tb", "lft_acc", 8),
        S("tb", "lft_psw_c", 1),
        S("tb", "lft_cmd0", 8),
        S("tb", "lft_cmd1", 8),
        S("tb", "lft_cmd2", 8),
        S("tb", "ram_wr_byte", 8),
        S("tb", "data", 8, bounds=(0, 7)),
    ]
    guidance = Guidance(SIGNALS, cycle_count)
    for sig in ("rst", "lft_pc", "lft_cmd2"):
        guidance.annotate(sig, AnnoType.ASSM)
    guidance.annotate("lft_cmd0", {ts: AnnoType.ASSM for ts in [0, 1, 2, 3, 5, 7, 8, 9]})
    guidance.annotate("lft_cmd1", {ts: AnnoType.ASSM for ts in [0, 1, 2, 3, 4, 6, 8, 9]})
    guidance.annotate("lft_pc", {ts: AnnoType.ASSM for ts in [0, 1, 2, 3, 4, 6, 8, 9]})
    guidance.annotate("data[0]",  {7: AnnoType.PARAM})
    guidance.annotate("lft_acc",  [AnnoType.ASSM]*7 + [AnnoType.PARAM, AnnoType.ASSM, AnnoType.OUTPUT])

    bv8 = smt.BVSort(8)
    # TODO create refinement mappings for smt variables to verilog names
    # or automatically map shadow vars to inputs
    x = smt.Variable("__shadow_0", bv8)
    y = smt.Variable("__shadow_1", bv8)
    start = smt.Variable("Start", bv8)
    substart = smt.Variable("BV8", bv8)
    boolterm = smt.Variable("B", smt.BoolSort())
    addbv = smt.OpTerm(smt.Kind.BVAdd, (start, start))
    subbv = smt.OpTerm(smt.Kind.BVSub, (start, start))
    orbv = smt.OpTerm(smt.Kind.BVOr, (start, start))
    andbool = smt.OpTerm(smt.Kind.And, (boolterm, boolterm))
    orbool = smt.OpTerm(smt.Kind.Or, (boolterm, boolterm))
    xorbool = smt.OpTerm(smt.Kind.Xor, (boolterm, boolterm))
    notbool = smt.OpTerm(smt.Kind.Not, (boolterm,))
    impliesbool = smt.OpTerm(smt.Kind.Implies, (boolterm, boolterm))
    itebv = smt.OpTerm(smt.Kind.Ite, (boolterm, substart, substart))
    # Synth function and grammar
    solver = smt.SynthFun(
        "alu_add",
        (x, y),
        bv8,
        smt.Grammar(
            (x, y),
            (start,),
            # Order of these terms matters
            # Python dicts preserve insertion/declaration order
            {
                start: (addbv, subbv, orbv, itebv),
                boolterm: (andbool, orbool, notbool, impliesbool, xorbool, smt.BoolConst.T),
                substart: (x, y),
            }
        )
    ).new_solver()

    model = R8051Model(
        ProjectConfig(os.path.join(BASEDIR, "symbiyosys")),
        [8, 8],
        8,
        solver,
        SIGNALS,
        guidance
    )
    model.build_binary()
    model.main_sygus_loop()

if __name__ == "__main__":
    main()
