`easyila` (name WIP) is a Python framework for modeling, synthesis, and verification of hardware designs.
It is an offshoot of a larger hardware lifting project: https://github.com/adwait/hwlifting/

## Installation
### Dependencies
The following pieces of software are used:
- [SymbiYosys](https://symbiyosys.readthedocs.io/en/latest/index.html) (tested with commit `5d19e46` with Yices 2 backend)
- [Verilator](https://verilator.org/guide/latest/install.html) (tested on versions 4.212 and 4.110)

#### Python packages
- [cvc5 1.0.0](https://cvc5.github.io/) (`pip3 install cvc5`)
- `pytest` (`pip3 install pytest`)
This project also uses custom forks of some packages to implement bugfixes and performance improvements.
Run `git submodule init --update --recursive` to get the source code for those forks.
- custom build of [pyverilog](https://github.com/PyHDI/Pyverilog/) (`pip3 install -e ./Pyverilog`)
- custom build of [pyvcd](https://github.com/westerndigitalcorporation/pyvcd) (`pip3 install -e ./pyvcd`)

Finally, run `pip3 install -e .` in this directory to install the `easyila` package. You can then run examples with `python3 examples/rvmini.py`.
