Main lifting repository: https://github.com/adwait/hwlifting/

## Installation
### Dependencies
symbiyosys and probably some other stuff

### Python packages
cvc5 1.0.0 (`pip3 install cvc5`), custom build of pyverilog (`git submodule init --update --recursive`, `pip3 install -e ./Pyverilog`), custom build of pyvcd (`pipe install -e ./pyvcd`).

Then, run `pip3 install -e .` in this directory. You can then run examples with `python3 examples/rvmini.py`.
