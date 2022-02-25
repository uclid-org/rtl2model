"""
Annotations that provide guidance for oracles.
"""

from collections import defaultdict
from enum import Enum
from typing import Dict, List, Tuple, Set

class AnnoType(Enum):
    """
    Types of annotations
    """
    DC = 0
    ASSM = 1
    PARAM = 2
    OUTPUT = 3

class Guidance:
    """
    Allows the user to provide guidance for whether or not a value at a particular clock cycle
    is DC ("Don't Care"), ASSM ("Assumed" to be the value read during simulation), PARAM
    ("Parameter" of the synthesis function), or OUTPUT ("Output" of the synthesis function).
    """

    def __init__(self, signals, num_cycles: int):
        self.signals = signals
        self.signal_names = [qpath for s in self.signals for qpath in s.get_all_qp_instances()]
        self.base_names = [basename for s in self.signals for basename in s.get_all_bp_instances()]
        self.base_to_qualified = dict(zip(self.base_names, self.signal_names))
        self.num_cycles = num_cycles
        # Maps signals to maps of cycle -> AnnoType
        self._guide_dict: Dict[str, Dict[int, AnnoType]] = defaultdict(lambda: defaultdict(lambda: AnnoType.DC))

    def annotate(self, signal, annotation):
        """
        Specify annotations.

        If the argument is a list, then treat it as a cycle-by-cycle description
        of annotations.

        If the argument is a dict, then just copy it.

        If the argument is an AnnoType, then apply that AnnoType for every cycle,
        overwriting any existing annotations.
        """
        if not isinstance(signal, str):
            raise TypeError("Guidances are keyed by signal name")
        if signal not in self.signal_names:
            signal = self.base_to_qualified[signal]
            if signal not in self.signal_names:
                raise KeyError(signal)
        if isinstance(annotation, list):
            for t, g in enumerate(annotation):
                self._guide_dict[signal][t] = g
        elif isinstance(annotation, dict):
            self._guide_dict[signal].update(annotation)
        elif isinstance(annotation, AnnoType):
            self._guide_dict[signal] = defaultdict(lambda: annotation)
        else:
            raise Exception(f"Cannot interpret annotation: {annotation}")

    def get_annotation_at(self, signal, cycle) -> AnnoType:
        if not isinstance(signal, str):
            raise TypeError("Guidances are keyed by signal name")
        if signal not in self.signal_names:
            signal = self.base_to_qualified[signal]
            if signal not in self.signal_names:
                raise KeyError(signal)
        if cycle >= self.num_cycles:
            raise IndexError(f"cycle {cycle} exceeds num_cycles {self.num_cycles}")
        return self._guide_dict[signal][cycle]

    def get_outputs(self) -> Set[Tuple[str, int]]:
        """
        Returns (signal name, cycle number) pairs representing all annotated outputs.
        """
        outputs = set()
        for signal, cycles in self._guide_dict.items():
            outputs.update({(signal, n) for n in cycles if cycles[n] == AnnoType.OUTPUT})
        return outputs
