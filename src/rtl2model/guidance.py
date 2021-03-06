"""
Annotations that provide guidance for oracles.
"""

from collections import defaultdict
from dataclasses import dataclass, field
from enum import Enum
from typing import Dict, List, Tuple, Set, Optional, Union

import rtl2model.lynth.smt as smt


@dataclass(frozen=True)
class AnnoType:
    """
    Guidance annotations to represent the refinement relation between RTL signals
    and synthesis formula expressions.
    """

    val: int
    bounds: List[Tuple[int, int]] = field(default_factory=list)
    expr: smt.Term = None

    def __post_init__(self):
        if self.val < 0 or self.val > 3:
            raise TypeError(f"invalid value for AnnoType: {self.val}")

    def __str__(self):
        if self.val == 0:
            return "DONT_CARE"
        elif self.val == 1:
            return "ASSUME"
        elif self.val == 2:
            return f"Param({self.expr}, {self.bounds})"
        elif self.val == 3:
            return f"Output({self.expr}, {self.bounds})"
        else:
            raise TypeError(f"invalid AnnoType with val {self.val}")

    def is_dont_care(self):
        return self.val == 0

    def is_assume(self):
        return self.val == 1

    def is_param(self):
        return self.val == 2

    def is_output(self):
        return self.val == 3

# These fields must be declared afterwards in order to resolve the AnnoType name

AnnoType.DONT_CARE = AnnoType(0)
"""The value of this signal is not relevant."""

AnnoType.ASSUME = AnnoType(1)
AnnoType.AssumeIndexed = lambda *b: AnnoType(1, b)
"""The value of this signal should be assumed to match the value during simulation."""

AnnoType.Param = lambda v: AnnoType(2, expr=v)
"""
This signal represents a synthesis function parameter.
The program sketch variable or index expression whose value is sampled is specified
as argument.
"""
AnnoType.ParamIndexed = lambda b, v: AnnoType(2, [b], v)

AnnoType.Output = lambda v: AnnoType(3, expr=v)
"""
This signal represents a synthesis function output.
A variable with the name of the synthesis function whose output is being asserted
is passed as argument. The path of all variables here is assumed to be of the form
"MODULE_NAME.FUNCTION_NAME"; if module name is omitted, then the function is assumed
to exist in the top level module.
"""
AnnoType.OutputIndexed = lambda b, v: AnnoType(3, [b], v)


class Guidance:
    """
    Allows the user to provide guidance for whether or not a value at a particular clock cycle
    is `DONT_CARE` ("Don't Care"), `ASSUME` ("Assumed" to be the value read during simulation),
    `Param` ("Parameter" of a synthesis function), or `Output` ("Output" of the synthesis function).
    """

    def __init__(self, signals, num_cycles: int):
        self.signals = signals
        self.signal_names = [qpath for s in self.signals for qpath in s.get_all_qp_instances()]
        self.base_names = [basename for s in self.signals for basename in s.get_all_bp_instances()]
        self.base_to_qualified = dict(zip(self.base_names, self.signal_names))
        self.num_cycles = num_cycles
        # Maps qualified signal names to maps of cycle -> AnnoType
        # OR maps of smt.Term -> AnnoType
        self._guide_dict: Dict[str, Union[Dict[int, AnnoType], Dict[smt.Term, AnnoType]]] = defaultdict(lambda: defaultdict(lambda: AnnoType.DONT_CARE))

    def _validate_signame(self, signal):
        if not isinstance(signal, str):
            raise TypeError(f"Guidances are keyed by signal name, instead got {signal}")
        if signal not in self.signal_names:
            signal = self.base_to_qualified[signal]
            if signal not in self.signal_names:
                raise KeyError(signal)
        return signal

    def annotate(self, signal, annotation):
        """
        Specify annotations.

        If the argument is a list, then treat it as a cycle-by-cycle description
        of annotations.

        If the argument is a dict of ints, then just copy it.

        If the argument is a dict mapping `rtl2model.lynth.smt.Term` to `AnnoType`, it is copied as well.
        These predicates will be turned into an "if/elseif" tree, so if two conditions
        are true, only the first will matter.

        If the argument is an `AnnoType`, then apply that `AnnoType` for every cycle,
        overwriting any existing annotations.
        """
        signal = self._validate_signame(signal)
        if isinstance(annotation, list):
            for t, g in enumerate(annotation):
                self._guide_dict[signal][t] = g
        elif isinstance(annotation, dict):
            first_key = list(annotation.keys())[0]
            own_dict = self._guide_dict[signal]
            if isinstance(first_key, int):
                if len(own_dict) and isinstance(list(own_dict.keys())[0], smt.Term):
                    raise Exception("Cannot update guidance for predicated signal with cycle count")
                own_dict.update(annotation)
            elif isinstance(first_key, smt.Term):
                if len(own_dict) and isinstance(list(own_dict.keys())[0], int):
                    raise Exception("Cannot update guidance for cycle count sampled signal with predicate")
                new_anno_dict = {}
                for k, v in annotation.items():
                    if not isinstance(v, list):
                        new_anno_dict[k] = [v]
                    else:
                        new_anno_dict[k] = v
                own_dict.update(new_anno_dict)
            else:
                raise Exception(f"Cannot interpret annotation: {annotation}")
        elif isinstance(annotation, AnnoType):
            self._guide_dict[signal] = defaultdict(lambda: annotation)
        else:
            raise Exception(f"Cannot interpret annotation: {annotation}")

    def get_annotation_at(self, signal, cycle) -> Optional[AnnoType]:
        """
        Gets the appropriate annotation for `signal` on the corresponding `cycle`.
        If the signal's annotations are instead specified by predicates, then `None` is returned.
        """
        signal = self._validate_signame(signal)
        if cycle >= self.num_cycles:
            raise IndexError(f"cycle {cycle} exceeds num_cycles {self.num_cycles}")
        own_dict = self._guide_dict[signal]
        if len(own_dict) and isinstance(list(own_dict.keys())[0], smt.Term):
            return None
        return own_dict[cycle]

    def get_predicated_annotations(self, signal) -> Dict[smt.Term, List[AnnoType]]:
        """
        Returns a dict of all predicate-based annotations for this signal.
        """
        signal = self._validate_signame(signal)
        own_dict = self._guide_dict[signal]
        if len(own_dict) and isinstance(list(own_dict.keys())[0], smt.Term):
            return own_dict
        else:
            return {}

    def get_outputs(self) -> Set[Tuple[smt.Variable, str, Union[int, smt.Term]]]:
        """
        Returns (output ref, signal name | condition, cycle number) pairs
        representing all annotated outputs.
        """
        outputs = set()
        for signal, cycles in self._guide_dict.items():
            for n in cycles:
                # HACK: assumes only one output thing in predicate list
                if isinstance(cycles[n], list):
                    t = cycles[n][0]
                else:
                    t = cycles[n]
                if t.is_output():
                    outputs.add((t.expr, signal, n))
        return outputs
