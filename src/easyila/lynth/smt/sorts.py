
from abc import ABC
from dataclasses import dataclass
from typing import Tuple

from .common import Translatable, TargetFormat

# === BEGIN SMT Sorts ===

class Sort(Translatable, ABC):
    @staticmethod
    def from_cvc5(cvc5_sort):
        if cvc5_sort.isBitVector():
            return BVSort(cvc5_sort.getBitVectorSize())
        elif cvc5_sort.isBoolean():
            return BoolSort()
        elif cvc5_sort.isFunction():
            return FunctionSort.from_cvc5(cvc5_sort)
        elif cvc5_sort.isUninterpretedSort():
            return UninterpretedSort.from_cvc5(cvc5_sort)
        elif cvc5_sort.isArray():
            return ArraySort.from_cvc5(cvc5_sort)
        raise NotImplementedError(f"Cannot convert from CVC5 sort {cvc5_sort}")


@dataclass(frozen=True)
class BVSort(Sort):
    bitwidth: int

    def __str__(self):
        return f"bv{self.bitwidth}"

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            # No need to memoize, since the context already memoizes sorts
            # In fact, memoizing on this class is incorrect in case the context is cleared
            return cvc5_ctx.solver.mkBitVectorSort(self.bitwidth)
        elif tgt == TargetFormat.SYGUS2:
            return f"(_ BitVec {self.bitwidth})"
        elif tgt == TargetFormat.VERILOG:
            return f"[{int(self.bitwidth) - 1}:0]"
        elif tgt == TargetFormat.UCLID:
            return f"bv{self.bitwidth}"
        raise NotImplementedError("cannot convert bvsort to " + str(tgt))


@dataclass(frozen=True)
class BoolSort(Sort):
    @property
    def bitwidth(self):
        return 1

    def __str__(self):
        return "bool"

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            return cvc5_ctx.solver.getBooleanSort()
        elif tgt == TargetFormat.SYGUS2:
            return "Bool"
        elif tgt == TargetFormat.VERILOG:
            return ""
        elif tgt == TargetFormat.UCLID:
            return "boolean"
        raise NotImplementedError("cannot convert boolsort to " + str(tgt))


@dataclass(frozen=True)
class ArraySort(Sort):
    idx_sort: Sort
    elem_sort: Sort

    def __str__(self):
        return f"[{self.idx_sort}]{self.elem_sort}"

    @staticmethod
    def from_cvc5(cvc5_sort):
        assert cvc5_sort.isArray()
        return ArraySort(
            Sort.from_cvc5(cvc5_sort.getArrayIndexSort()),
            Sort.from_cvc5(cvc5_sort.getArrayElementSort())
        )

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            return cvc5_ctx.solver.mkArraySort(self.idx_sort.to_cvc5(cvc5_ctx), self.elem_sort.to_cvc5(cvc5_ctx))
        # elif tgt == TargetFormat.SYGUS2:
        # elif tgt == TargetFormat.VERILOG:
        # elif tgt == TargetFormat.UCLID:
        raise NotImplementedError("cannot convert boolsort to " + str(tgt))


@dataclass(frozen=True)
class FunctionSort(Sort):
    args: Tuple[Sort, ...] # argument sorts
    codomain: Sort # return sort

    def __str__(self):
        return f"({','.join(str(a) for a in self.args)}) -> {self.codomain}"

    @staticmethod
    def from_cvc5(cvc5_sort):
        assert cvc5_sort.isFunction()
        return FunctionSort(
            [Sort.from_cvc5(s) for s in cvc5_sort.getFunctionDomainSorts()],
            Sort.from_cvc5(cvc5_sort.getFunctionCodomainSort())
        )

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            return cvc5_ctx.solver.mkFunctionSort([a.to_cvc5(cvc5_ctx) for a in self.args], self.codomain.to_cvc5(cvc5_ctx))
        elif tgt == TargetFormat.SYGUS2:
            return "(-> " + " ".join([a.to_sygus2() for a in self.args]) + self.codomain.to_sygus2() + ")"
        raise NotImplementedError("cannot convert FunctionSort to " + str(tgt))

@dataclass(frozen=True)
class UninterpretedSort(Sort):
    name: str

    def __str__(self):
        return self.name

    @staticmethod
    def from_cvc5(cvc5_sort):
        assert cvc5_sort.isUninterpretedSort()
        return UninterpretedSort(cvc5_sort.getUninterpretedSortName())

    def to_target_format(self, tgt: TargetFormat, **kwargs):
        if tgt == TargetFormat.CVC5:
            cvc5_ctx = kwargs["cvc5_ctx"]
            # TODO need to memoize?
            return cvc5_ctx.solver.mkUninterpretedSort(self.name)
        elif tgt == TargetFormat.SYGUS2:
            return self.name
        raise NotImplementedError("cannot convert FunctionSort to " + str(tgt))


# === END SMT Sorts ===
