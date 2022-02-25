from abc import ABC, abstractmethod
from dataclasses import dataclass
import logging
import os
from subprocess import Popen, PIPE
import sys
from typing import Dict, Callable, List, Union, Optional, Tuple

import easyila.lynth.smt as smt


@dataclass
class CallResult:
    inputs: List
    output: int

    def to_tuple(self):
        return (*self.inputs, self.output)


class OracleInterface(ABC):
    """
    Base class for oracle interfaces

    Parameters
    ----------
    oracle - Callable | str
        Either a callable Python function to use as the oracle (in which case its return value is
        used as output), or a path to an external binary to be executed as oracle (in which case 
        stdout is used as output).
    replay_inputs - Optional[List[Tuple[int, ...]]]=None
        A list of input values to be replayed. Instead of prompting the user for new input values,
        the oracle will use these inputs instead.
    log_path - Optional[str]=None
        File path where input/output results will be logged.
    """
    # The oracle can either be a python library function or an external binary
    def __init__(
        self,
        name: str,
        oracle: Union[Callable, str],
        replay_inputs: Optional[List[Tuple[int, ...]]]=None,
        log_path: Optional[str]=None
    ):
        if log_path is None:
            log_path = f"logs/oracle_{name}_call.log"
        self.log_path = log_path
        self.binpath = None
        self.lfun = None
        if callable(oracle):
            self.is_external_binary = False
            self.lfun = oracle
        elif isinstance(oracle, str):
            self.is_external_binary = True
            self.binpath = oracle
        else:
            raise Exception("oracle function must be callable or path to external binary, instead was " + str(type(oracle)))
        self.name = name
        self.calls: List[CallResult] = []
        self.replay_inputs = replay_inputs
        if replay_inputs:
            self._replay_iter = iter(replay_inputs)
        else:
            self._replay_iter = None

    def next_replay_input(self):
        if self._replay_iter is not None:
            return next(self._replay_iter, None)
        else:
            return None

    def invoke(self, args):
        if self.is_external_binary:
            process = Popen([self.binpath] + args, stdout=PIPE)
            (output, _) = process.communicate()
        else:
            output = self.lfun(args)
        output = int(output)
        result = CallResult(args, output)
        self.calls.append(result)
        return result

    @abstractmethod
    def apply_constraints(self, slv, fun):
        """
        Adds constraints on the specified function within the solver instance.
        """
        raise NotImplementedError

    def save_call_logs(self):
        with open(self.log_path, 'w') as logfile:
            logfile.write('\n'.join(str(" ".join([str(c) for c in call.to_tuple()])) for call in self.calls))


class IOOracle(OracleInterface):
    """
    Input/output oracle.

    Parameters
    ----------
    in_widths: list of widths of inputs
    out_width: width of output
    """

    def __init__(
        self,
        name: str,
        in_widths: list,
        out_width: int,
        oracle: Union[Callable, str],
        *,
        replay_inputs: Optional[List[Tuple[int, ...]]]=None,
        log_path: Optional[str]=None
    ):
        super().__init__(name, oracle, replay_inputs, log_path)
        self.in_widths = in_widths
        self.out_width = out_width

    @staticmethod
    def from_call_logs(name, in_widths, out_width, oracle, replay_log_path, *, new_log_path=None):
        inputs = []
        with open(replay_log_path) as f:
            for l in f.readlines():
                inputs.append([int(s) for s in l.split()[:-1]])
        return IOOracle(name, in_widths, out_width, oracle, replay_inputs=inputs, log_path=new_log_path)

    # Generate the term that enforce input output pair matches with uninterpreted function
    def apply_constraints(self, slv, fun):
        # TODO: make this more general?
        for call in self.calls:
            in_consts = [smt.BVConst(int(i_value), i_width) for i_width, i_value in zip(self.in_widths, call.inputs)]
            out_const = smt.BVConst(call.output, self.out_width)
            fn_apply = smt.ApplyUF(fun, tuple(in_consts))
            slv.add_sygus_constraint(smt.OpTerm(smt.Kind.Equal, (fn_apply, out_const)))


class CorrectnessOracle(OracleInterface):
    """
    Correctness oracle. The provided binary/function should perform BMC or some kind
    of equivalence checking.
    """

    # Correctness oracle does not apply any constraints
    def apply_constraints(self, slv, fun):
        pass


# class DistinguishingOracle(OracleInterface):
#     """
#     Distinguishing oracle. The provided binary/function should
#     see diagram on p10 of https://arxiv.org/pdf/2107.13477.pdf
#     perhaps the distinguishing oracle should contain a correctness and
#     i/o oracle as members?
#     """

#     def __init__(self, name: str, oracle) -> None:
#         super().__init__(name, oracle)

#     def invoke(self, args):
#         return super()._invoke(args)

#     # Require that function matches all existing I/O pairs
#     def apply_constraints(self, slv, args):
#         fun = args[self.name]
#         for call in self.calls:


class OracleCtx:
    """
    Class that maintains a collection of oracles.
    Also logs the sequence of oracle calls, respecting the order between them.
    """

    def __init__(self, solver):
        self.oracles: Dict[str, OracleInterface] = {}
        self.solver = solver
        # self.call_logs = []

    def add_oracle(self, oracle: OracleInterface):
        self.oracles[oracle.name] = oracle

    def call_oracle(self, oraclename: str, args):
        result = self.oracles[oraclename].invoke(args)
        if oraclename == "io":
            print(f"{oraclename} oracle result:", result)
        # self.call_logs.append(log_entry)
        return result

    # def print_call_logs(self, logfile="./logs/global_call.log"):
    #     with open(logfile, 'w') as fileh:
    #         fileh.write('\n'.join(self.call_logs))

    def apply_all_constraints(self, slv, oracle_map):
        for oraclename, fun in oracle_map.items():
            self.oracles[oraclename].apply_constraints(slv, fun)

