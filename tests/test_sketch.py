from rtl2synth.sketch import *

class TestSketch:

    def test_concrete_program_to_hex_str_array(self):
        p = ProgramSketch(
            inst_byte(0xAB),
            inst_word(0xFFFC),
            inst_byte(0x12),
            inst_word(0xEE33),
        ).fill()
        assert p.to_hex_str_array() == ["ab", "0000fffc", "12", "0000ee33"]

    def test_concrete_program_to_bytearray(self):
        p = ProgramSketch(
            inst_byte(0xAB),
            inst_word(0xFFFC),
            inst_byte(0x12),
            inst_word(0xEE33),
        ).fill()
        assert p.to_bytearray() == bytearray(b"\xab\x00\x00\xff\xfc\x12\x00\x00\xee\x33")