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

import rtl2synth.gen_config as gen_config
from rtl2synth.guidance import Guidance, AnnoType
from rtl2synth.synthesis_template import *
from rtl2synth.sketch import *
import rtl2synth.lynth.smt as smt
from rtl2synth.model import *
from rtl2synth.verilog import *

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
        defined_modules=[s_table, xs_table],
        important_signals=[
            "aes_reg_state",
        ],
        pickle_path="tiny_aes.pickle",
    )
    top.print()
    assert top.validate()

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
        inst_word(0x0101FF00),
    )
    signals = [
        S("top", "rst", 1),
        S("top", "cmd_word", 8),
        S("top", "wr", 1),
        S("top", "addr", 16),
        S("top", "data_in", 8),
        S("top", "data_out", 8),
        S("top", "aes_state", 2),
        S("top", "aes_addr", 16),
        S("top", "aes_len", 16),
        S("top", "aes_ctr", 16),
    ]
    guidance = Guidance(signals, 22)
    for sig in ("rst",):
        guidance.annotate(sig, AnnoType.ASSUME)
    model = TinyAesModel(
        ProjectConfig(os.path.join(BASEDIR, "symbiyosys")),
        sketch,
        top,
        {},
        guidance,
    )

    import faulthandler
    faulthandler.enable()
    model.main_sygus_loop()

if __name__ == "__main__":
    main()
