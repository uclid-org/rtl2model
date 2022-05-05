"""
Harness for collecting (coarse) timing information.
"""

import atexit
from enum import Enum, auto
import os
import time

from prettytable import PrettyTable

class Segment(Enum):
    PV_PARSE = auto()
    """Time spent in Pyverilog's parsing."""

    DF_TRAVERSE = auto()
    """Time spent traversing the dataflow graph/performing cone of influence analysis."""

    IO_ORACLE = auto()
    """Time spent invoking the I/O oracle."""

    CORR_ORACLE = auto()
    """Time spent invoking the correctness oracle."""

    SYNTH_ENGINE = auto()
    """Time spent in the synthesis engine."""

_segments = [
    Segment.PV_PARSE,
    Segment.DF_TRAVERSE,
    Segment.IO_ORACLE,
    Segment.CORR_ORACLE,
    Segment.SYNTH_ENGINE,
]

class _ProfileResults:
    def __init__(self):
        self.start_ns_stack = []
        self.curr_segment_stack = []
        # Each element is a list of (time start, time end)
        self.segments = {s: [] for s in _segments}
        self.init_ns = time.time_ns()
        if not "PYTEST_CURRENT_TEST" in os.environ:
            atexit.register(self.print)

    def push(self, segment: Segment):
        self.curr_segment_stack.append(segment)
        self.start_ns_stack.append(time.time_ns())

    def pop(self):
        end = time.time_ns()
        seg = self.curr_segment_stack.pop()
        start = self.start_ns_stack.pop()
        self.segments[seg].append((start, end))

    def print(self):
        final = time.time_ns()
        count_cols = [s.name + " counts" for s in _segments]
        tot_cols = [s.name + " seconds" for s in _segments]
        t = PrettyTable(count_cols + tot_cols)
        row = []
        for times in self.segments.values():
            row.append(len(times))
        for times in self.segments.values():
            tot_times = sum(end - start for start, end in times) / 1e6
            row.append(tot_times)
        t.add_row(row)
        print(t)
        print("Total runtime:", (final - self.init_ns) / 1e9)
        if self.curr_segment_stack:
            s = self.curr_segment_stack[-1]
            t = (final - self.start_ns_stack[-1]) / 1e9
            print(f"EXITED ABNORMALLY; last {s.name} ran for {t} seconds")

PROFILE = _ProfileResults()
