Main lifting repository: https://github.com/adwait/hwlifting/

## Installation
### Dependencies
symbiyosys and probably some other stuff

### Python
Follow the instructions to build [cvc5](https://cvc5.github.io/) version 0.0.7 with python bindings. You will probably need python=3.9.
I had to pip3 install the following libraries to build it:
- Cython
- scikit-build
- toml
- pytest

Then, run `pip3 install -e .` in this directory. You can then run examples with `python3 examples/rvmini.py`.
