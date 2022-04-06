
from abc import ABC, abstractmethod
from enum import Enum, auto
import json

class TargetFormat(Enum):
    """
    Represents a format to translate objects in this file to different representations.
    """
    CVC5 = auto()
    SYGUS2 = auto()
    VERILOG = auto()
    UCLID = auto()
    JSON = auto()

class Translatable(ABC):
    """
    Mixin to define common methods for translating to other representations.
    """

    # @abstractmethod
    @staticmethod
    def from_json(fp):
        raise NotImplementedError()

    @abstractmethod
    def to_target_format(self, tgt: TargetFormat, **kwargs):
        raise NotImplementedError()

    def to_cvc5(self, cvc5_ctx):
        return self.to_target_format(TargetFormat.CVC5, cvc5_ctx=cvc5_ctx)

    def to_sygus2(self):
        return self.to_target_format(TargetFormat.SYGUS2)

    def to_verilog_str(self, *, is_reg=False, anyconst=False):
        return self.to_target_format(TargetFormat.VERILOG, is_reg=is_reg, anyconst=anyconst)

    def to_uclid(self):
        return self.to_target_format(TargetFormat.UCLID)

    def to_json(self):
        return self.to_target_format(TargetFormat.JSON)
