
from collections import defaultdict
import csv
import tempfile

from vcd.reader import tokenize, TokenKind

class VcdWrapper:
    DEFAULT_CLOCK_NAME = "Top.clk"

    def __init__(self, vcd_path, clock_name=DEFAULT_CLOCK_NAME):
        if clock_name is None:
            clock_name = VcdWrapper.DEFAULT_CLOCK_NAME
        self.timescale = None
        # maps variable fully qualified name to variable id
        var_dict = {}
        # maps variable ids to lists of (timestamp, new_value) pairs
        ts_change_dict = defaultdict(list)
        curr_ts = 0
        with open(vcd_path, 'rb') as vcd_f:
            toks = tokenize(vcd_f)
            curr_scope = []
            for tok in toks:
                if tok.kind is TokenKind.TIMESCALE:
                    self.timescale = (tok.timescale.magnitude.value, tok.timescale.unit.value)
                elif tok.kind is TokenKind.SCOPE:
                    curr_scope.append(tok.scope.ident)
                elif tok.kind is TokenKind.UPSCOPE:
                    curr_scope.pop()
                elif tok.kind is TokenKind.VAR:
                    var_dict[".".join(curr_scope + [tok.var.reference])] = tok.var.id_code
                elif tok.kind is TokenKind.CHANGE_TIME:
                    curr_ts = tok.time_change
                elif tok.kind is TokenKind.CHANGE_SCALAR:
                    # ignore x/z case for now
                    ts_change_dict[tok.scalar_change.id_code].append((curr_ts, int(tok.scalar_change.value)))
                elif tok.kind is TokenKind.CHANGE_VECTOR:
                    ts_change_dict[tok.vector_change.id_code].append((curr_ts, int(tok.vector_change.value)))
        if clock_name not in var_dict:
            raise KeyError("Clock signal '" + clock_name + "' not found in VCD file (did you mean to specify it as argument to the constructor?)")
        self.var_dict = var_dict
        self.ts_change_dict = ts_change_dict
        # identify clock period
        self.clock_start = None
        self.clock_pd = None
        # sample for high, low, high pattern
        clock_started = False
        went_low = False
        for ts, new_val in ts_change_dict[var_dict[clock_name]]:
            if not clock_started and new_val == 1:
                self.clock_start = ts
                clock_started = True
            if clock_started and new_val == 0:
                went_low = True
            if clock_started and went_low and new_val == 1:
                self.clock_pd = ts - self.clock_start
                break

    def get_value_at_or_none(self, var_name, cycle):
        """
        Attempts to get the value of VAR_NAME on cycle CYCLE from the VCD.

        Returns None if the variable is not present.
        """
        try:
            return self.get_value_at(var_name, cycle)
        except KeyError as e:
            return None

    def get_value_at(self, var_name, cycle):
        """
        Attempts to get the value of VAR_NAME on cycle CYCLE from the VCD.

        Raises KeyError if the variable is not present.
        """
        if var_name not in self.var_dict:
            # HACK: verilator seems to add an invisible "TOP" module, so attempt to look up the variable with "TOP" first
            if not var_name.startswith("TOP."):
                try:
                    print(f"looking up TOP.{var_name}")
                    return self.get_value_at(f"TOP.{var_name}", cycle)
                except KeyError as e:
                    pass
            if len(self.var_dict) < 5:
                e_msg = "Could not find variable " + var_name + " in VCD file (possible values: " + str(self.var_dict) + ")"
            else:
                e_msg = "Could not find variable " + var_name + " in VCD file"
            raise KeyError(e_msg)
        var_id = self.var_dict[var_name]
        changes = self.ts_change_dict[var_id]
        goal_ts = cycle * self.clock_pd + self.clock_start
        curr_val = None
        for ts, new_val in changes:
            if ts > goal_ts:
                break
            curr_val = new_val
        return curr_val

