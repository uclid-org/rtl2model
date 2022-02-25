"""
Common utilities for tracing and verification scripts.
"""

import csv
from dataclasses import dataclass
# import getpass
from typing import *


@dataclass
class SampledSignal:
    module_name: str
    signal_name: str
    width: int
    hierarchy: Optional[Tuple[str, ...]] = None
    bounds: Optional[Tuple[int, int]] = None # inclusive start and end

    def __post_init__(self):
        if self.hierarchy is None:
            self.hierarchy = (self.module_name,)

    # TODO this is weird
    def __hash__(self):
        return hash((self.module_name, self.signal_name, self.width, self.hierarchy, self.bounds))

    def get_qualified_path(self):
        return "->".join(self.hierarchy) + "->" + self.signal_name

    def get_base_path(self):
        return self.signal_name

    def get_all_bp_instances(self):
        """
        If this signal is an array/vector, returns a list of all base paths,
        e.g. ['signal', 'signal[0]', 'signal[1]'].
        If the signal is not an array/vector, then it returns a 1-element array
        of the fully qualified path.
        """
        if self.bounds:
            return [self.get_base_path()] + [self.signal_name + '[{}]'.format(i)
                for i in range(self.bounds[0], self.bounds[1] + 1)]
        else:
            return [self.signal_name]

    def get_all_qp_instances(self):
        """
        If this signal is an array/vector, returns a list of all qualified paths,
        e.g. ['top->signal', 'top->signal[0]', 'top->signal[1]'].
        If the signal is not an array/vector, then it returns a 1-element array
        of the fully qualified path.
        """
        if self.bounds:
            return [self.get_qualified_path()] + ["->".join(self.hierarchy) + "->" + self.signal_name + '[{}]'.format(i)
                for i in range(self.bounds[0], self.bounds[1] + 1)]
        else:
            return [self.get_qualified_path()]


S = SampledSignal


def read_csv(filename, numlines):
    with open(filename, newline="") as csvfile:
        csvreader = csv.reader(csvfile, delimiter=",")
        # Trim the header
        signals = next(csvreader, None)[1:]
        # Trim the signal widths
        widths = dict(zip(signals, [int(w) for w in next(csvreader, None)[1:]]))
        values = []
        # Add first NUMLINES lines trimming the first (empty) column
        for _ in range(numlines):
            values.append([int(i) for i in next(csvreader)[1:]])
        return widths, values
