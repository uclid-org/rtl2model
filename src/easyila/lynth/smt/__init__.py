"""
Provides in-memory representations of SMT expressions and grammars, which can then be translated
to solver backends like CVC5 and Z3.

TODO add str methods to everything
"""

from .sorts import *
from .terms import *
from .synth import *
