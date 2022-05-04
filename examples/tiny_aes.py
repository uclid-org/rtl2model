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

def main():
    top = verilog_to_model(
        os.path.join(BASEDIR, "full_tableless.v"),
        "top",
        "clk",
        defined_modules=[s_table, xs_table],
        pickle_path="tiny_aes.pickle",
    )
    top.print()
    assert top.validate()

if __name__ == "__main__":
    main()
