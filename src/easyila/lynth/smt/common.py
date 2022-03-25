
from abc import ABC, abstractmethod
from enum import Enum, auto

class TargetFormat(Enum):
    """
    Represents a format to translate objects in this file to different representations.
    """
    CVC5 = auto()
    SYGUS2 = auto()
    VERILOG = auto()
    UCLID = auto()
    VERIF_DSL = auto()

class Translatable(ABC):
    """
    Mixin to define common methods for translating to other representations.
    """

    @abstractmethod
    def to_target_format(self, tgt: TargetFormat, **kwargs):
        raise NotImplementedError()

    def to_cvc5(self, cvc5_ctx):
        return self.to_target_format(TargetFormat.CVC5, cvc5_ctx=cvc5_ctx)

    def to_sygus2(self):
        return self.to_target_format(TargetFormat.SYGUS2)

    def to_verilog_str(self):
        return self.to_target_format(TargetFormat.VERILOG)

    def to_uclid(self):
        return self.to_target_format(TargetFormat.UCLID)

    def to_verif_dsl(self):
        return self.to_target_format(TargetFormat.VERIF_DSL)
