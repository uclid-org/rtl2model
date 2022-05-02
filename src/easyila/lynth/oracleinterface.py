from abc import ABC, abstractmethod
from dataclasses import dataclass
import os
import random
from subprocess import Popen, PIPE
from typing import Any, Dict, Callable, Iterator, Iterable, List, Union, Optional, Tuple

import easyila.lynth.smt as smt


@dataclass
class CallResult:
    inputs: Any
    outputs: Any

    def to_tuple(self):
        if isinstance(self.inputs, Dict):
            i_list = list(self.inputs.values())
        elif isinstance(self.inputs, Iterable):
            i_list = list(self.inputs)
        else:
            i_list = [self.inputs]
        if isinstance(self.outputs, Dict):
            return (*i_list, *list(self.outputs.values()))
        elif isinstance(self.outputs, Iterable):
            return (*i_list, *list(self.outputs))
        else:
            return (*i_list, self.outputs)

    def __str__(self):
        if isinstance(self.inputs, List):
            s = "inputs: " + ", ".join(f"{i:#x}" for i in self.inputs)
        elif isinstance(self.inputs, Dict):
            s = "inputs: " + ", ".join(f"{k}={i:#x}" for k, i in self.inputs.items())
        else:
            return str(self.to_tuple())
        if isinstance(self.outputs, int):
            return s + "; outputs: " + f"{self.outputs:#x}"
        elif isinstance(self.outputs, List):
            return s + "; outputs: " + ", ".join(f"{v:#x}" for v in self.outputs)
        elif isinstance(self.inputs, Dict):
            return s + "; outputs: " + ", ".join(f"{k}={i:#x}" for k, i in self.outputs.items())
        else:
            return str(self.to_tuple())


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
        os.makedirs(os.path.dirname(log_path), exist_ok=True)
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
        self.replay_inputs = replay_inputs
        self._replay_iter: Optional[Iterator[Dict[str, int]]]
        if replay_inputs:
            self._replay_iter = iter(replay_inputs)
        else:
            self._replay_iter = None
        self.i_history = []
        self.o_history = []

    @property
    def calls(self) -> List[CallResult]:
        return [CallResult(i, o) for i, o in zip(self.i_history, self.o_history)]

    def next_replay_input(self):
        if self._replay_iter is not None:
            return next(self._replay_iter, None)
        else:
            return None

    def invoke(self, args: Dict[str, int]):
        # args is a mapping of smt var name -> value
        assert isinstance(args, Dict), args
        assert isinstance(list(args.keys())[0], str), args
        assert isinstance(list(args.values())[0], int), args
        if self.is_external_binary:
            process = Popen([self.binpath] + args, stdout=PIPE)
            (output, _) = process.communicate()
        else:
            output = self.lfun(args)
        i_map = {v: args[v.name] for v in self.in_vars}
        o_map = {v: output[v.name] for v in self.out_vars}
        self.i_history.append(i_map)
        self.o_history.append(o_map)
        return CallResult(args, o_map)

    @abstractmethod
    def apply_constraints(self, slv, fun):
        """
        Adds constraints on the specified candidate function within the solver instance.
        """
        raise NotImplementedError()

    def save_call_logs(self):
        with open(self.log_path, 'w') as logfile:
            logfile.write('\n'.join(str(" ".join([str(c) for c in call.to_tuple()])) for call in self.calls))


class IOOracle(OracleInterface):
    """
    Input/output oracle.
    """

    def __init__(
        self,
        name: str,
        in_vars: List[smt.Variable],
        out_vars: List[smt.Variable],
        oracle: Union[Callable, str],
        *,
        replay_inputs: Optional[List[Dict[str, int]]]=None,
        log_path: Optional[str]=None,
        seed: Optional[int]=None,
    ):
        super().__init__(name, oracle, replay_inputs, log_path)
        self.in_vars = in_vars
        self.out_vars = out_vars
        self.rng = random.Random(seed)

    @staticmethod
    def from_call_logs(name, in_vars, out_vars, oracle, replay_log_path, *, new_log_path=None):
        inputs = []
        with open(replay_log_path) as f:
            for l in f.readlines():
                inputs.append({v.name: int(s) for v, s in zip(in_vars, l.split())})
        return IOOracle(name, in_vars, out_vars, oracle, replay_inputs=inputs, log_path=new_log_path)

    def new_random_inputs(self):
        """
        Returns a set of uniformly sampled, new random inputs.
        """
        repeated = True
        while repeated:
            new_inputs = tuple(self.rng.randint(0, 2 ** v.c_bitwidth() - 1) for v in self.in_vars)
            repeated = new_inputs in self.i_history
        return new_inputs

    def get_constraints(self, synthfun):
        """
        Applies constraints requiring that the result of calling the function
        on previous inputs matches the correct outputs.
        """
        constraints = []
        refs = synthfun.get_refs()
        # TODO reconcile sketch inputs with synthfun inputs
        for call in self.calls:
            in_consts = [smt.BVConst(i_value, i_var.c_bitwidth()) for i_var, i_value in call.inputs.items()]
            out_consts = [smt.BVConst(o_value, o_var.c_bitwidth()) for o_var, o_value in call.outputs.items()]
            # fn_apply = synthfun.to_uf().apply(*in_consts)
            constraints.append(fn_apply.op_eq(out_const))
        return constraints

    def apply_constraints(self, slv, synthfun):
        for constraint in self.get_constraints(synthfun):
            slv.add_constraint(constraint)

class CorrectnessOracle(OracleInterface):
    """
    Correctness oracle. The provided binary/function should perform BMC or some kind
    of equivalence checking.
    """

    def __init__(
        self,
        name: str,
        in_vars: List[smt.Variable],
        out_vars: List[smt.Variable],
        oracle: Union[Callable, str],
        replay_inputs: Optional[List[Tuple[int, ...]]]=None,
        log_path: Optional[str]=None
    ):
        super().__init__(name, oracle, replay_inputs, log_path)
        self.in_vars = in_vars
        self.out_vars = out_vars
        self.cex_inputs = []
        self.cex_outputs = []

    def cexs(self) -> List[CallResult]:
        """
        Returns a list of CallResults representing counterexamples.
        """
        return [CallResult(i, o) for i, o in zip(self.cex_inputs, self.cex_outputs)]

    def add_cex(self, input_vals, output_vals):
        self.cex_inputs.append(input_vals)
        self.cex_outputs.append(output_val)

    def get_constraints(self, synthfun):
        """
        Constraints requiring that the result of calling the function
        on previous inputs is equal to the CORRECT output.
        """
        constraints = []
        for call in self.cexs():
            in_consts = [smt.BVConst(i_value, i_var.c_bitwidth()) for i_var, i_value in zip(self.in_vars, call.inputs)]
            out_const = smt.BVConst(call.output, self.out_width)
            fn_apply = synthfun.to_uf().apply(*in_consts)
            constraints.append(fn_apply.op_eq(out_const))
        return constraints

    def apply_constraints(self, slv, synthfun):
        for constraint in self.get_constraints(synthfun):
            slv.add_constraint(constraint)


# class DistinguishingOracle(OracleInterface):
#     """
#     Distinguishing oracle. Given a history of I/O inputs and a candidate
#     function, produce an input on which the candidate function defers from
#     some other function.
#     """

#     def __init__(
#         self,
#         name: str,
#         in_widths: List[int],
#         out_width: int,
#         io_oracle_name: str,
#         *,
#         replay_inputs: Optional[List[Tuple[int, ...]]]=None,
#         log_path: Optional[str]=None
#     ):
#         def oracle_fun(args):

#         super().__init__(name, oracle)

#     def invoke(self, args):
#         return super()._invoke(args)

#     def apply_constraints(self, slv, fun):
#         """
#         Pseudocode for the distinguishing constraint is:
#         exists (f', O, O') . (Behave(f') and f(I) == O and f'(I) == O' and O != O'
#         That is, there exists some other function f' that matches candidate function f
#         on all existing inputs but differs on some input set I.
#         """
#         in_sorts = tuple([smt.BVSort(i) for i in self.in_widths])
#         out_sort = smt.BVSort(self.out_width)
#         synth_inputs = tuple([smt.Variable(f"__dist_in_{i}", s) for i, s in enumerate(in_sort)])
#         other_fn = smt.Variable("__other_fn", smt.FunctionSort(in_sorts, out_sort))
#         cand_out = smt.Variable("__cand_out", out_sort)
#         other_out = smt.Variable("__other_out", out_sort)
#         eq_terms = []
#         for call in self.calls:
#             in_consts = [smt.BVConst(int(i_value), i_width) for i_width, i_value in zip(self.in_widths, call.inputs)]
#             out_const = smt.BVConst(call.output, self.out_width)
#             fn_apply = smt.ApplyUF(other_fn, tuple(in_consts))
#             # TODO allow python operators
#             eq_terms.append(smt.OpTerm(smt.Kind.Equal, (fn_apply, out_const)))
#         behave_constraint = smt.OpTerm(smt.Kind.And, tuple(eq_terms))
#         out_neq = smt.OpTerm(smt.Kind.Not, smt.OpTerm(smt.Kind.Equal, (cand_out, other_out)))
#         cand_call = smt.OpTerm(smt.Kind.Equal, (smt.ApplyUf(fun, synth_inputs), cand_out))
#         other_call = smt.OpTerm(smt.Kind.Equal, (smt.ApplyUf(other_fn, synth_inputs), other_out))
#         exists = smt.QuantTerm(
#             smt.Kind.Exists,
#             (other_fn, cand_out, other_out),
#             smt.OpTerm(smt.Kind.And, (behave_constraint, cand_call, other_call, out_neq))
#         )

#         slv.add_sygus_constraint()

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
        print(f"calling {oraclename} oracle")
        result = self.oracles[oraclename].invoke(args)
        if oraclename == "io":
            print(f"{oraclename} oracle result:", result)
        # self.call_logs.append(log_entry)
        return result

    # def print_call_logs(self, logfile="./logs/global_call.log"):
    #     with open(logfile, 'w') as fileh:
    #         fileh.write('\n'.join(self.call_logs))

    def apply_all_constraints(self, slv, oracle_map):
        for oraclename, args in oracle_map.items():
            self.oracles[oraclename].apply_constraints(slv, args)

