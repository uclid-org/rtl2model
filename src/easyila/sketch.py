"""
Facilities for generating a low-level program sketch.

(note: this was called TestCase instead in our 263 project)
"""

from dataclasses import dataclass
from typing import Dict, Tuple, Union, Optional


@dataclass(frozen=True)
class SketchHole:
    """Represents a hole within an instruction of a program sketch."""
    name: str
    bitwidth: int


@dataclass(frozen=True)
class SketchValue:
    """Represents a concrete set of bits in an instruction in a program sketch."""
    value: int
    bitwidth: int


def inst_word(value):
    assert value <= 0xFFFFFFFF
    return Inst(SketchValue(value, 32))


def inst_byte(value):
    assert value <= 0xFF
    return Inst(SketchValue(value, 8))


_InstField = Union[SketchValue, SketchHole]


@dataclass
class Inst:
    value: Tuple[_InstField, ...]

    def __init__(self, *args):
        for arg in args:
            assert isinstance(arg, SketchHole) or isinstance(arg, SketchValue), arg
        self.value = tuple(args)

    def __mul__(self, other):
        if not isinstance(other, int):
            raise TypeError(f"can only multiply Inst by int (got {repr(other)})")
        return Inst(*(self.value * other))

    def to_bit_str(self):
        """
        Returns an array of bits representing this instruction. Any SketchHole bits
        are replaced with "X".
        """
        # In order to make sure everything is properly aligned, first generate
        # an array of bits (with Xs for unknown) and
        bits = ""
        for field in self.value:
            if isinstance(field, SketchHole):
                bits += "X" * field.bitwidth
            else:
                bits += f"{field.value:0{field.bitwidth}b}"
        return bits

    def to_hex_str(self):
        bits = self.to_bit_str()
        i = len(bits)
        hex_digits = []
        # Traverse over groups of 4 bits starting from the end of the bit string
        while i > 0:
            if i - 4 < 0:
                nibble_s = bits[0:i]
            else:
                nibble_s = bits[i - 4:i]
            if "X" in nibble_s:
                nibble = "X"
            else:
                nibble = "{:1X}".format(int("".join(nibble_s), 2))
            hex_digits.append(nibble)
            i -= 4
        return "".join(reversed(hex_digits))

    def to_bytearray(self):
        bits = self.to_bit_str()
        ba = bytearray(len(bits) // 8)
        # Traverse over groups of 8 bits starting from the end
        i = len(bits)
        while i > 0:
            if i - 8 < 0:
                byte_s = bits[0:i]
            else:
                byte_s = bits[i - 8:i]
            if "X" in byte_s:
                raise Exception("cannot convert Instruction with holes into bytearray")
            ba[(i - 8) // 8] = int("".join(byte_s), 2)
            i -= 8
        return ba


class ConcreteProgram:
    insts: Tuple[Inst]

    def __init__(self, *args):
        self.insts = tuple(args)

    def to_hex_str_array(self):
        return [inst.to_hex_str() for inst in self.insts]

    def to_bytearray(self):
        ba = bytearray()
        for inst in self.insts:
            ba.extend(inst.to_bytearray())
        return ba


class ProgramSketch:
    insts: Tuple[Inst]

    def __init__(self, *args):
        self.insts = tuple(args)

    def fill(self, mappings: Optional[Dict[str, int]]=None) -> ConcreteProgram:
        new_insts = []
        for inst in self.insts:
            lst = list(inst.value)
            for i, field in enumerate(lst):
                if isinstance(field, SketchHole):
                    lst[i] = SketchValue(mappings[field.name], field.bitwidth)
            new_insts.append(Inst(*lst))
        return ConcreteProgram(*new_insts)
