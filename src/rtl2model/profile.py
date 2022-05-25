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

    def description(self):
        if self == Segment.PV_PARSE:
            return "Dataflow parsing from Verilog"
        elif self == Segment.DF_TRAVERSE:
            return "Partial model construction from dataflow"
        elif self == Segment.IO_ORACLE:
            return "I/O oracle invocation"
        elif self == Segment.CORR_ORACLE:
            return "Correctness oracle invocation"
        elif self == Segment.SYNTH_ENGINE:
            return "Solver synthesis invocation"
        raise TypeError()


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
        self.model = None
        self.sf_count = 0
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

    def add_model(self, model, synthfun_count):
        self.model = model
        self.sf_count = synthfun_count

    def print(self):
        final = time.time_ns()
        count_cols = [s.name + " counts" for s in _segments]
        tot_cols = [s.name + " seconds" for s in _segments]
        t = PrettyTable(["operation", "counts", "total seconds", "avg seconds"])
        rows = []
        for s, times in self.segments.items():
            counts = len(times)
            tot_times = sum(end - start for start, end in times) / 1e9
            if counts == 0:
                avg = "--"
            else:
                avg = tot_times / counts
            row = [s.name, counts, tot_times, avg]
            t.add_row(row)
            rows.append(row)

        print(t)
        print("Total runtime:", (final - self.init_ns) / 1e9, "seconds")
        if self.curr_segment_stack:
            s = self.curr_segment_stack[-1]
            t = (final - self.start_ns_stack[-1]) / 1e9
            print(f"EXITED ABNORMALLY; last {s.name} ran for {t} seconds")
        m = self.model
        if m is not None:
            print(f"Model contained {m.state_var_count()} state variables and {m.uf_count()} UFs")
        print("=== CONVENIENCE LATEX BELOW ===")
        for s, row in zip(_segments, rows):
            _, counts, tot_times, avg = row
            avg_str = avg if avg == "--" else f"{avg:.3f}"
            print(f"{s.description()} & {counts} & {tot_times:.3f} & {avg_str} \\\\")

PROFILE = _ProfileResults()
