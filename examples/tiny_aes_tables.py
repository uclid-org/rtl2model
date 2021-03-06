"""
Manually constructed models for AES lookup tables to circumvent pyverilog performance issues.
"""

import rtl2model.lynth.smt as smt
from rtl2model.model import Model

__all__ = ["s_table", "xs_table"]

v = smt.Variable
bv8 = smt.BVSort(8)
bv8_c = lambda n: smt.BVConst(n, 8)
in_ = v("in", bv8)
out = v("out", bv8)
s_table = Model(
    "S",
    inputs=[in_],
    outputs=[out],
    transition={
        out: in_.match_const({
            0x00: bv8_c(0x63),
            0x01: bv8_c(0x7c),
            0x02: bv8_c(0x77),
            0x03: bv8_c(0x7b),
            0x04: bv8_c(0xf2),
            0x05: bv8_c(0x6b),
            0x06: bv8_c(0x6f),
            0x07: bv8_c(0xc5),
            0x08: bv8_c(0x30),
            0x09: bv8_c(0x01),
            0x0a: bv8_c(0x67),
            0x0b: bv8_c(0x2b),
            0x0c: bv8_c(0xfe),
            0x0d: bv8_c(0xd7),
            0x0e: bv8_c(0xab),
            0x0f: bv8_c(0x76),
            0x10: bv8_c(0xca),
            0x11: bv8_c(0x82),
            0x12: bv8_c(0xc9),
            0x13: bv8_c(0x7d),
            0x14: bv8_c(0xfa),
            0x15: bv8_c(0x59),
            0x16: bv8_c(0x47),
            0x17: bv8_c(0xf0),
            0x18: bv8_c(0xad),
            0x19: bv8_c(0xd4),
            0x1a: bv8_c(0xa2),
            0x1b: bv8_c(0xaf),
            0x1c: bv8_c(0x9c),
            0x1d: bv8_c(0xa4),
            0x1e: bv8_c(0x72),
            0x1f: bv8_c(0xc0),
            0x20: bv8_c(0xb7),
            0x21: bv8_c(0xfd),
            0x22: bv8_c(0x93),
            0x23: bv8_c(0x26),
            0x24: bv8_c(0x36),
            0x25: bv8_c(0x3f),
            0x26: bv8_c(0xf7),
            0x27: bv8_c(0xcc),
            0x28: bv8_c(0x34),
            0x29: bv8_c(0xa5),
            0x2a: bv8_c(0xe5),
            0x2b: bv8_c(0xf1),
            0x2c: bv8_c(0x71),
            0x2d: bv8_c(0xd8),
            0x2e: bv8_c(0x31),
            0x2f: bv8_c(0x15),
            0x30: bv8_c(0x04),
            0x31: bv8_c(0xc7),
            0x32: bv8_c(0x23),
            0x33: bv8_c(0xc3),
            0x34: bv8_c(0x18),
            0x35: bv8_c(0x96),
            0x36: bv8_c(0x05),
            0x37: bv8_c(0x9a),
            0x38: bv8_c(0x07),
            0x39: bv8_c(0x12),
            0x3a: bv8_c(0x80),
            0x3b: bv8_c(0xe2),
            0x3c: bv8_c(0xeb),
            0x3d: bv8_c(0x27),
            0x3e: bv8_c(0xb2),
            0x3f: bv8_c(0x75),
            0x40: bv8_c(0x09),
            0x41: bv8_c(0x83),
            0x42: bv8_c(0x2c),
            0x43: bv8_c(0x1a),
            0x44: bv8_c(0x1b),
            0x45: bv8_c(0x6e),
            0x46: bv8_c(0x5a),
            0x47: bv8_c(0xa0),
            0x48: bv8_c(0x52),
            0x49: bv8_c(0x3b),
            0x4a: bv8_c(0xd6),
            0x4b: bv8_c(0xb3),
            0x4c: bv8_c(0x29),
            0x4d: bv8_c(0xe3),
            0x4e: bv8_c(0x2f),
            0x4f: bv8_c(0x84),
            0x50: bv8_c(0x53),
            0x51: bv8_c(0xd1),
            0x52: bv8_c(0x00),
            0x53: bv8_c(0xed),
            0x54: bv8_c(0x20),
            0x55: bv8_c(0xfc),
            0x56: bv8_c(0xb1),
            0x57: bv8_c(0x5b),
            0x58: bv8_c(0x6a),
            0x59: bv8_c(0xcb),
            0x5a: bv8_c(0xbe),
            0x5b: bv8_c(0x39),
            0x5c: bv8_c(0x4a),
            0x5d: bv8_c(0x4c),
            0x5e: bv8_c(0x58),
            0x5f: bv8_c(0xcf),
            0x60: bv8_c(0xd0),
            0x61: bv8_c(0xef),
            0x62: bv8_c(0xaa),
            0x63: bv8_c(0xfb),
            0x64: bv8_c(0x43),
            0x65: bv8_c(0x4d),
            0x66: bv8_c(0x33),
            0x67: bv8_c(0x85),
            0x68: bv8_c(0x45),
            0x69: bv8_c(0xf9),
            0x6a: bv8_c(0x02),
            0x6b: bv8_c(0x7f),
            0x6c: bv8_c(0x50),
            0x6d: bv8_c(0x3c),
            0x6e: bv8_c(0x9f),
            0x6f: bv8_c(0xa8),
            0x70: bv8_c(0x51),
            0x71: bv8_c(0xa3),
            0x72: bv8_c(0x40),
            0x73: bv8_c(0x8f),
            0x74: bv8_c(0x92),
            0x75: bv8_c(0x9d),
            0x76: bv8_c(0x38),
            0x77: bv8_c(0xf5),
            0x78: bv8_c(0xbc),
            0x79: bv8_c(0xb6),
            0x7a: bv8_c(0xda),
            0x7b: bv8_c(0x21),
            0x7c: bv8_c(0x10),
            0x7d: bv8_c(0xff),
            0x7e: bv8_c(0xf3),
            0x7f: bv8_c(0xd2),
            0x80: bv8_c(0xcd),
            0x81: bv8_c(0x0c),
            0x82: bv8_c(0x13),
            0x83: bv8_c(0xec),
            0x84: bv8_c(0x5f),
            0x85: bv8_c(0x97),
            0x86: bv8_c(0x44),
            0x87: bv8_c(0x17),
            0x88: bv8_c(0xc4),
            0x89: bv8_c(0xa7),
            0x8a: bv8_c(0x7e),
            0x8b: bv8_c(0x3d),
            0x8c: bv8_c(0x64),
            0x8d: bv8_c(0x5d),
            0x8e: bv8_c(0x19),
            0x8f: bv8_c(0x73),
            0x90: bv8_c(0x60),
            0x91: bv8_c(0x81),
            0x92: bv8_c(0x4f),
            0x93: bv8_c(0xdc),
            0x94: bv8_c(0x22),
            0x95: bv8_c(0x2a),
            0x96: bv8_c(0x90),
            0x97: bv8_c(0x88),
            0x98: bv8_c(0x46),
            0x99: bv8_c(0xee),
            0x9a: bv8_c(0xb8),
            0x9b: bv8_c(0x14),
            0x9c: bv8_c(0xde),
            0x9d: bv8_c(0x5e),
            0x9e: bv8_c(0x0b),
            0x9f: bv8_c(0xdb),
            0xa0: bv8_c(0xe0),
            0xa1: bv8_c(0x32),
            0xa2: bv8_c(0x3a),
            0xa3: bv8_c(0x0a),
            0xa4: bv8_c(0x49),
            0xa5: bv8_c(0x06),
            0xa6: bv8_c(0x24),
            0xa7: bv8_c(0x5c),
            0xa8: bv8_c(0xc2),
            0xa9: bv8_c(0xd3),
            0xaa: bv8_c(0xac),
            0xab: bv8_c(0x62),
            0xac: bv8_c(0x91),
            0xad: bv8_c(0x95),
            0xae: bv8_c(0xe4),
            0xaf: bv8_c(0x79),
            0xb0: bv8_c(0xe7),
            0xb1: bv8_c(0xc8),
            0xb2: bv8_c(0x37),
            0xb3: bv8_c(0x6d),
            0xb4: bv8_c(0x8d),
            0xb5: bv8_c(0xd5),
            0xb6: bv8_c(0x4e),
            0xb7: bv8_c(0xa9),
            0xb8: bv8_c(0x6c),
            0xb9: bv8_c(0x56),
            0xba: bv8_c(0xf4),
            0xbb: bv8_c(0xea),
            0xbc: bv8_c(0x65),
            0xbd: bv8_c(0x7a),
            0xbe: bv8_c(0xae),
            0xbf: bv8_c(0x08),
            0xc0: bv8_c(0xba),
            0xc1: bv8_c(0x78),
            0xc2: bv8_c(0x25),
            0xc3: bv8_c(0x2e),
            0xc4: bv8_c(0x1c),
            0xc5: bv8_c(0xa6),
            0xc6: bv8_c(0xb4),
            0xc7: bv8_c(0xc6),
            0xc8: bv8_c(0xe8),
            0xc9: bv8_c(0xdd),
            0xca: bv8_c(0x74),
            0xcb: bv8_c(0x1f),
            0xcc: bv8_c(0x4b),
            0xcd: bv8_c(0xbd),
            0xce: bv8_c(0x8b),
            0xcf: bv8_c(0x8a),
            0xd0: bv8_c(0x70),
            0xd1: bv8_c(0x3e),
            0xd2: bv8_c(0xb5),
            0xd3: bv8_c(0x66),
            0xd4: bv8_c(0x48),
            0xd5: bv8_c(0x03),
            0xd6: bv8_c(0xf6),
            0xd7: bv8_c(0x0e),
            0xd8: bv8_c(0x61),
            0xd9: bv8_c(0x35),
            0xda: bv8_c(0x57),
            0xdb: bv8_c(0xb9),
            0xdc: bv8_c(0x86),
            0xdd: bv8_c(0xc1),
            0xde: bv8_c(0x1d),
            0xdf: bv8_c(0x9e),
            0xe0: bv8_c(0xe1),
            0xe1: bv8_c(0xf8),
            0xe2: bv8_c(0x98),
            0xe3: bv8_c(0x11),
            0xe4: bv8_c(0x69),
            0xe5: bv8_c(0xd9),
            0xe6: bv8_c(0x8e),
            0xe7: bv8_c(0x94),
            0xe8: bv8_c(0x9b),
            0xe9: bv8_c(0x1e),
            0xea: bv8_c(0x87),
            0xeb: bv8_c(0xe9),
            0xec: bv8_c(0xce),
            0xed: bv8_c(0x55),
            0xee: bv8_c(0x28),
            0xef: bv8_c(0xdf),
            0xf0: bv8_c(0x8c),
            0xf1: bv8_c(0xa1),
            0xf2: bv8_c(0x89),
            0xf3: bv8_c(0x0d),
            0xf4: bv8_c(0xbf),
            0xf5: bv8_c(0xe6),
            0xf6: bv8_c(0x42),
            0xf7: bv8_c(0x68),
            0xf8: bv8_c(0x41),
            0xf9: bv8_c(0x99),
            0xfa: bv8_c(0x2d),
            0xfb: bv8_c(0x0f),
            0xfc: bv8_c(0xb0),
            0xfd: bv8_c(0x54),
            0xfe: bv8_c(0xbb),
            0xff: bv8_c(0x16),
        })
    }
)
xs_table = Model(
    "xS",
    inputs=[in_],
    outputs=[out],
    transition={
        out: in_.match_const({
            0x00: bv8_c(0xc6),
            0x01: bv8_c(0xf8),
            0x02: bv8_c(0xee),
            0x03: bv8_c(0xf6),
            0x04: bv8_c(0xff),
            0x05: bv8_c(0xd6),
            0x06: bv8_c(0xde),
            0x07: bv8_c(0x91),
            0x08: bv8_c(0x60),
            0x09: bv8_c(0x02),
            0x0a: bv8_c(0xce),
            0x0b: bv8_c(0x56),
            0x0c: bv8_c(0xe7),
            0x0d: bv8_c(0xb5),
            0x0e: bv8_c(0x4d),
            0x0f: bv8_c(0xec),
            0x10: bv8_c(0x8f),
            0x11: bv8_c(0x1f),
            0x12: bv8_c(0x89),
            0x13: bv8_c(0xfa),
            0x14: bv8_c(0xef),
            0x15: bv8_c(0xb2),
            0x16: bv8_c(0x8e),
            0x17: bv8_c(0xfb),
            0x18: bv8_c(0x41),
            0x19: bv8_c(0xb3),
            0x1a: bv8_c(0x5f),
            0x1b: bv8_c(0x45),
            0x1c: bv8_c(0x23),
            0x1d: bv8_c(0x53),
            0x1e: bv8_c(0xe4),
            0x1f: bv8_c(0x9b),
            0x20: bv8_c(0x75),
            0x21: bv8_c(0xe1),
            0x22: bv8_c(0x3d),
            0x23: bv8_c(0x4c),
            0x24: bv8_c(0x6c),
            0x25: bv8_c(0x7e),
            0x26: bv8_c(0xf5),
            0x27: bv8_c(0x83),
            0x28: bv8_c(0x68),
            0x29: bv8_c(0x51),
            0x2a: bv8_c(0xd1),
            0x2b: bv8_c(0xf9),
            0x2c: bv8_c(0xe2),
            0x2d: bv8_c(0xab),
            0x2e: bv8_c(0x62),
            0x2f: bv8_c(0x2a),
            0x30: bv8_c(0x08),
            0x31: bv8_c(0x95),
            0x32: bv8_c(0x46),
            0x33: bv8_c(0x9d),
            0x34: bv8_c(0x30),
            0x35: bv8_c(0x37),
            0x36: bv8_c(0x0a),
            0x37: bv8_c(0x2f),
            0x38: bv8_c(0x0e),
            0x39: bv8_c(0x24),
            0x3a: bv8_c(0x1b),
            0x3b: bv8_c(0xdf),
            0x3c: bv8_c(0xcd),
            0x3d: bv8_c(0x4e),
            0x3e: bv8_c(0x7f),
            0x3f: bv8_c(0xea),
            0x40: bv8_c(0x12),
            0x41: bv8_c(0x1d),
            0x42: bv8_c(0x58),
            0x43: bv8_c(0x34),
            0x44: bv8_c(0x36),
            0x45: bv8_c(0xdc),
            0x46: bv8_c(0xb4),
            0x47: bv8_c(0x5b),
            0x48: bv8_c(0xa4),
            0x49: bv8_c(0x76),
            0x4a: bv8_c(0xb7),
            0x4b: bv8_c(0x7d),
            0x4c: bv8_c(0x52),
            0x4d: bv8_c(0xdd),
            0x4e: bv8_c(0x5e),
            0x4f: bv8_c(0x13),
            0x50: bv8_c(0xa6),
            0x51: bv8_c(0xb9),
            0x52: bv8_c(0x00),
            0x53: bv8_c(0xc1),
            0x54: bv8_c(0x40),
            0x55: bv8_c(0xe3),
            0x56: bv8_c(0x79),
            0x57: bv8_c(0xb6),
            0x58: bv8_c(0xd4),
            0x59: bv8_c(0x8d),
            0x5a: bv8_c(0x67),
            0x5b: bv8_c(0x72),
            0x5c: bv8_c(0x94),
            0x5d: bv8_c(0x98),
            0x5e: bv8_c(0xb0),
            0x5f: bv8_c(0x85),
            0x60: bv8_c(0xbb),
            0x61: bv8_c(0xc5),
            0x62: bv8_c(0x4f),
            0x63: bv8_c(0xed),
            0x64: bv8_c(0x86),
            0x65: bv8_c(0x9a),
            0x66: bv8_c(0x66),
            0x67: bv8_c(0x11),
            0x68: bv8_c(0x8a),
            0x69: bv8_c(0xe9),
            0x6a: bv8_c(0x04),
            0x6b: bv8_c(0xfe),
            0x6c: bv8_c(0xa0),
            0x6d: bv8_c(0x78),
            0x6e: bv8_c(0x25),
            0x6f: bv8_c(0x4b),
            0x70: bv8_c(0xa2),
            0x71: bv8_c(0x5d),
            0x72: bv8_c(0x80),
            0x73: bv8_c(0x05),
            0x74: bv8_c(0x3f),
            0x75: bv8_c(0x21),
            0x76: bv8_c(0x70),
            0x77: bv8_c(0xf1),
            0x78: bv8_c(0x63),
            0x79: bv8_c(0x77),
            0x7a: bv8_c(0xaf),
            0x7b: bv8_c(0x42),
            0x7c: bv8_c(0x20),
            0x7d: bv8_c(0xe5),
            0x7e: bv8_c(0xfd),
            0x7f: bv8_c(0xbf),
            0x80: bv8_c(0x81),
            0x81: bv8_c(0x18),
            0x82: bv8_c(0x26),
            0x83: bv8_c(0xc3),
            0x84: bv8_c(0xbe),
            0x85: bv8_c(0x35),
            0x86: bv8_c(0x88),
            0x87: bv8_c(0x2e),
            0x88: bv8_c(0x93),
            0x89: bv8_c(0x55),
            0x8a: bv8_c(0xfc),
            0x8b: bv8_c(0x7a),
            0x8c: bv8_c(0xc8),
            0x8d: bv8_c(0xba),
            0x8e: bv8_c(0x32),
            0x8f: bv8_c(0xe6),
            0x90: bv8_c(0xc0),
            0x91: bv8_c(0x19),
            0x92: bv8_c(0x9e),
            0x93: bv8_c(0xa3),
            0x94: bv8_c(0x44),
            0x95: bv8_c(0x54),
            0x96: bv8_c(0x3b),
            0x97: bv8_c(0x0b),
            0x98: bv8_c(0x8c),
            0x99: bv8_c(0xc7),
            0x9a: bv8_c(0x6b),
            0x9b: bv8_c(0x28),
            0x9c: bv8_c(0xa7),
            0x9d: bv8_c(0xbc),
            0x9e: bv8_c(0x16),
            0x9f: bv8_c(0xad),
            0xa0: bv8_c(0xdb),
            0xa1: bv8_c(0x64),
            0xa2: bv8_c(0x74),
            0xa3: bv8_c(0x14),
            0xa4: bv8_c(0x92),
            0xa5: bv8_c(0x0c),
            0xa6: bv8_c(0x48),
            0xa7: bv8_c(0xb8),
            0xa8: bv8_c(0x9f),
            0xa9: bv8_c(0xbd),
            0xaa: bv8_c(0x43),
            0xab: bv8_c(0xc4),
            0xac: bv8_c(0x39),
            0xad: bv8_c(0x31),
            0xae: bv8_c(0xd3),
            0xaf: bv8_c(0xf2),
            0xb0: bv8_c(0xd5),
            0xb1: bv8_c(0x8b),
            0xb2: bv8_c(0x6e),
            0xb3: bv8_c(0xda),
            0xb4: bv8_c(0x01),
            0xb5: bv8_c(0xb1),
            0xb6: bv8_c(0x9c),
            0xb7: bv8_c(0x49),
            0xb8: bv8_c(0xd8),
            0xb9: bv8_c(0xac),
            0xba: bv8_c(0xf3),
            0xbb: bv8_c(0xcf),
            0xbc: bv8_c(0xca),
            0xbd: bv8_c(0xf4),
            0xbe: bv8_c(0x47),
            0xbf: bv8_c(0x10),
            0xc0: bv8_c(0x6f),
            0xc1: bv8_c(0xf0),
            0xc2: bv8_c(0x4a),
            0xc3: bv8_c(0x5c),
            0xc4: bv8_c(0x38),
            0xc5: bv8_c(0x57),
            0xc6: bv8_c(0x73),
            0xc7: bv8_c(0x97),
            0xc8: bv8_c(0xcb),
            0xc9: bv8_c(0xa1),
            0xca: bv8_c(0xe8),
            0xcb: bv8_c(0x3e),
            0xcc: bv8_c(0x96),
            0xcd: bv8_c(0x61),
            0xce: bv8_c(0x0d),
            0xcf: bv8_c(0x0f),
            0xd0: bv8_c(0xe0),
            0xd1: bv8_c(0x7c),
            0xd2: bv8_c(0x71),
            0xd3: bv8_c(0xcc),
            0xd4: bv8_c(0x90),
            0xd5: bv8_c(0x06),
            0xd6: bv8_c(0xf7),
            0xd7: bv8_c(0x1c),
            0xd8: bv8_c(0xc2),
            0xd9: bv8_c(0x6a),
            0xda: bv8_c(0xae),
            0xdb: bv8_c(0x69),
            0xdc: bv8_c(0x17),
            0xdd: bv8_c(0x99),
            0xde: bv8_c(0x3a),
            0xdf: bv8_c(0x27),
            0xe0: bv8_c(0xd9),
            0xe1: bv8_c(0xeb),
            0xe2: bv8_c(0x2b),
            0xe3: bv8_c(0x22),
            0xe4: bv8_c(0xd2),
            0xe5: bv8_c(0xa9),
            0xe6: bv8_c(0x07),
            0xe7: bv8_c(0x33),
            0xe8: bv8_c(0x2d),
            0xe9: bv8_c(0x3c),
            0xea: bv8_c(0x15),
            0xeb: bv8_c(0xc9),
            0xec: bv8_c(0x87),
            0xed: bv8_c(0xaa),
            0xee: bv8_c(0x50),
            0xef: bv8_c(0xa5),
            0xf0: bv8_c(0x03),
            0xf1: bv8_c(0x59),
            0xf2: bv8_c(0x09),
            0xf3: bv8_c(0x1a),
            0xf4: bv8_c(0x65),
            0xf5: bv8_c(0xd7),
            0xf6: bv8_c(0x84),
            0xf7: bv8_c(0xd0),
            0xf8: bv8_c(0x82),
            0xf9: bv8_c(0x29),
            0xfa: bv8_c(0x5a),
            0xfb: bv8_c(0x1e),
            0xfc: bv8_c(0x7b),
            0xfd: bv8_c(0xa8),
            0xfe: bv8_c(0x6d),
            0xff: bv8_c(0x2c),
        }),
    }
)