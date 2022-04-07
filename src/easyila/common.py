"""
Common utilities for tracing and verification scripts.
"""

import csv
from dataclasses import dataclass
# import getpass
from typing import *

import easyila.lynth.smt as smt

@dataclass
class SampledSignal:
    module_name: str
    signal_name: str
    width: int
    hierarchy: Optional[Tuple[str, ...]] = None
    bounds: Optional[Tuple[int, int]] = None # inclusive start and end

    def __post_init__(self):
        if self.hierarchy is None:
            self.hierarchy = tuple(self.module_name.split("."))

    # TODO this is weird
    def __hash__(self):
        return hash((self.module_name, self.signal_name, self.width, self.hierarchy, self.bounds))

    def to_variable(self):
        """
        Converts this to an SMT variable, ignoring hierarchy.
        """
        # TODO deal with arrays/bounds
        # and also booleans
        return smt.BVVariable(self.signal_name, self.width)

    def get_qualified_path(self):
        return "->".join(self.hierarchy) + "->" + self.signal_name

    def get_base_path(self):
        return self.signal_name

    def get_all_bp_instances(self):
        """
        If this signal is an array/vector, returns a list of all base paths,
        e.g. ['signal[0]', 'signal[1]'].
        If the signal is not an array/vector, then it returns a 1-element array
        of the fully qualified path.
        """
        if self.bounds:
            return [self.signal_name + '[{}]'.format(i)
                for i in range(self.bounds[0], self.bounds[1] + 1)]
        else:
            return [self.signal_name]

    def get_all_qp_instances(self):
        """
        If this signal is an array/vector, returns a list of all qualified paths,
        e.g. ['top->signal[0]', 'top->signal[1]'].
        If the signal is not an array/vector, then it returns a 1-element array
        of the fully qualified path.
        """
        if self.bounds:
            return ["->".join(self.hierarchy) + "->" + self.signal_name + '[{}]'.format(i)
                for i in range(self.bounds[0], self.bounds[1] + 1)]
        else:
            return [self.get_qualified_path()]


S = SampledSignal


def read_csv(filename, numlines):
    with open(filename, newline="") as csvfile:
        csvreader = csv.DictReader(csvfile)
        widths = {sig: int(w) for sig, w in next(csvreader).items()}
        values = []
        # Add first NUMLINES lines
        for _ in range(numlines):
            values.append({sig: int(v) for sig, v in next(csvreader).items()})
        return widths, values
