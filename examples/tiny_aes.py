"""
Modeling script for the tiny_aes core: https://opencores.org/projects/tiny_aes

Huang et al. 2018 added additional code surrounding the original accelerator to make it
exchange data via DMA, and make the processor follow a more generalized state machine.
In Huang's ILA work, the AES contains these instructions (elaborated on by their tutorial
https://github.com/PrincetonUniversity/IMDb-Archive/tree/master/tutorials/aes):
- WRITE_ADDRESS:
- START_ENCRYPT: begin AES counter mode encryption (has child instructions)
    - LOAD
    - UPDATE
    - STORE
- READ_LENGTH
- READ_ADDRESS
- READ_KEY
- GET_STATUS
- WRITE_LENGTH
- WRITE_KEY
- WRITE_COUNTER
"""

import os
import pickle
import subprocess
import sys

import rtl2model.gen_config as gen_config
from rtl2model.guidance import Guidance, AnnoType
from rtl2model.synthesis_template import *
from rtl2model.sketch import *
import rtl2model.lynth.smt as smt
from rtl2model.model import *
from rtl2model.verilog import *

from tiny_aes_tables import s_table, xs_table

REPO_BASE_DIR = subprocess.run(
    "git rev-parse --show-toplevel",
    shell=True,
    capture_output=True,
    check=True
).stdout.decode("utf-8").strip()

BASEDIR = os.path.join(REPO_BASE_DIR, "designs/tiny_aes/")

class TinyAesModel(ModelBuilder):
    def build_sim(self):
        gen_config.generate_config(
            signals=self.signals,
            target_sim_dir=BASEDIR,
            target_verilog_dir=BASEDIR,
            root="top"
        )
        self.run_proc(["make", "default"], cwd=BASEDIR)

    def simulate_and_read_signals(self, program):
        with open(os.path.join(BASEDIR, "inputs.bin"), "wb") as f:
            f.write(program.to_bytearray())
        self.run_proc(["./obj_dir/Vtop", "inputs.bin"], cwd=BASEDIR)
        return read_csv(os.path.join(BASEDIR, "traces/tr.csv"), self.cycle_count)


def main():
    top = verilog_to_model(
        os.path.join(BASEDIR, "full_tableless.v"),
        "top",
        "clk",
        # defined_modules=[s_table, xs_table],
        important_signals=[
            "aes_reg_state",
            "cmd_word",
            "ack",
        ],
        pickle_path="tiny_aes.pickle",
        coi_conf=COIConf.UF_ARGS_COI,
    )
    top.print()
    assert top.validate()

    cmd_word = smt.bv_variable("cmd_word", 32)

    # Custom instruction encoding:
    # - (W * 8) | (D * 8) | (A * 16)
    # - wr      | data_in | addr
    # valid addresses:
    # 0xFF00: AES_REG_START (1B)
    # 0xFF01: AES_REG_STATE (1B)
    # 0xFF02: AES_REG_STATE (2B)
    # 0xFF04: AES_REG_LEN   (2B)
    # ...
    # 0xFF10: AES_REG_KEY0
    # 0xFF20: AES_REG_CTR
    sketch = ProgramSketch(
        Inst(cmd_word),
        # inst_word(0x0101FF00),
    )
    signals = [
        S("top", "rst", 1),
        S("top", "cmd_word", 32),
        S("top", "wr", 1),
        S("top", "addr", 16),
        S("top", "data_in", 8),
        S("top", "in_addr_range", 1),
        S("top", "data_out", 8),
        S("top", "aes_state", 2),
        S("top", "aes_addr", 16),
        S("top", "aes_len", 16),
        S("top", "aes_ctr", 16),
    ]
    guidance = Guidance(signals, 22)
    guidance.annotate("rst", AnnoType.ASSUME)
    guidance.annotate("cmd_word", {
        0: AnnoType.Param(cmd_word),
    })
    guidance.annotate("in_addr_range", {
        0: AnnoType.Output(smt.bv_variable("top.in_addr_range", 1)),
    })
    start = smt.bv_variable("start", 1)
    # Workaround for converting boolean expressions to BV1
    boolterm = smt.bool_variable("boolterm")
    bv16term = smt.bv_variable("bv16term", 16)
    grammar = smt.Grammar(
        bound_vars=(cmd_word,),
        nonterminals=(start, boolterm, bv16term),
        terms={
            start: (
                boolterm.ite(smt.BVConst(1, 1), smt.BVConst(0, 1)),
                smt.BVConst(1, 1),
            ),
            boolterm: (
                bv16term < bv16term,
                bv16term.op_eq(bv16term),
                smt.BoolConst.T,
                ~boolterm,
                boolterm & boolterm,
                boolterm | boolterm,
            ),
            bv16term: (
                cmd_word[15:0],
                # Making the range too large causes a segfault
                *list(smt.BVConst(n, 16) for n in range(0xFF00, 0xFFFF)),
            ),
        }
    )
    # for tlist in grammar.terms.values():
    #     for t in tlist:
    #         print(t.to_sygus2())
    model = TinyAesModel(
        ProjectConfig(os.path.join(BASEDIR, "symbiyosys")),
        sketch,
        top,
        {("top", "in_addr_range"): grammar},
        guidance,
    )

    import faulthandler
    faulthandler.enable()
    model.main_sygus_loop()

if __name__ == "__main__":
    main()
