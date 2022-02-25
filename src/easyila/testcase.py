from enum import Enum
import itertools
import logging
import random
from typing import List

import numpy as np

class BinaryRepr(Enum):
    HEX = 0
    BYTE = 1


class InstrWord:
    def __init__(self, word, base, padding=0) -> None:
        if isinstance(word, str):
            self.word = word.split('_')
        elif isinstance(word, list):
            self.word = word
        elif isinstance(word, int):
            self.word = [f"{word:0{padding}x}"]
        self.parameter = [True if 'x' in elem else False for elem in self.word]
        self.base = base

    def __mul__(self, val) -> List:
        """Generates `val` many copies of the ego instruction"""
        if not isinstance(val, int):
            logging.error("__mul__ must have integer second argument")
        return [self]*val

    def _inject(self, sampling_policy):
        """Inject always returns a hex output"""
        raise NotImplementedError


class bInstrWord(InstrWord):
    """
    Subclass for instructions passed as strings of binary digits.
    """
    def __init__(self, word, padding=0) -> None:
        super().__init__(word, 2, padding=padding)

    def _inject(self, sampling_policy=None):
        if sampling_policy is None:
            # compute a string so that it can be joined
            terms = [elem[1] if not elem[0] else random.randint(0, pow(2, len(elem[1]))) for elem in zip(self.parameter, self.word)]
            terms_stringified = [val if isinstance(val, str) else f"{val:0{w}b}" for (val, w) in zip(terms, [len(w) for w in self.word])]
            print(terms_stringified)
            value = int(''.join(terms_stringified), 2)
            width = int(sum([len(w) for w in self.word])/4)
            # join string
            return f"{value:0{width}x}"


class xInstrWord(InstrWord):
    """
    Subclass for instructions passed as strings of hexadecimal digits.
    """

    def __init__(self, word, padding=0) -> None:
        super().__init__(word, 16, padding=padding)

    def _inject(self, sampling_policy=None):
        if sampling_policy is None:
            # compute a string so that it can be joined
            terms = [elem[1] if not elem[0] else random.randint(0, pow(self.base, len(elem[1]))) for elem in zip(self.parameter, self.word)]
            terms_stringified = [val if isinstance(val, str) else f"{val:0{w}x}" for (val, w) in zip(terms, [len(w) for w in self.word])]
            # join string
            return ''.join(terms_stringified)
        else:
            logging.error("Support for non-default sampling strategies has not been implemented yet")


class TestCase:
    __test__ = False # Prevent pytest from thinking this is a runnable test

    def __init__(self, *args) -> None:
        unif_args = [item if isinstance(item, list) else [item] for item in args]
        self.instrs = itertools.chain.from_iterable(unif_args)

    def _inject(self, op_format: BinaryRepr):
        if op_format == BinaryRepr.BYTE:
            logging.warn("Currently not checked: Need to ensure that the instructions are at most single byte")
            return bytearray([int(instr._inject(), 16) for instr in self.instrs])
        elif op_format == BinaryRepr.HEX:
            return [instr._inject() for instr in self.instrs]

