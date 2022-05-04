"""
Tests wrapper for reading from a VCD file.
"""

from rtl2synth.verilog import VcdWrapper

vcdtext = """\
$date 2022-02-14 15:54:18.657260 $end
$timescale 1 ns $end
$scope module Tile $end
$var wire 1 ! clk $end
$var wire 1 " r $end
$var reg 4 # ctr $end
$var reg 2 $ s $end
$var wire 2 % t $end
$upscope $end
$enddefinitions $end
#0
$dumpvars
1!
0"
b0 #
b0 $
b0 %
$end
b1 $
b11 %
1"
#1
0!
#2
1!
b10 $
b0 %
0"
b1 #
#3
0!
#4
1!
b11 $
b1 %
b10 #
#5
0!
#6
1!
b0 $
b10 %
1"
b11 #
#7
0!
#8
1!
b1 $
b11 %
b100 #
#9
0!
#10
1!
b10 $
b0 %
0"
b101 #
#11
0!
#12
1!
b11 $
b1 %
b110 #
#13
0!
#14
1!
b0 $
b10 %
1"
b111 #
#15
0!
#16
1!
b1 $
b11 %
b1000 #
#17
0!
#18
1!
b10 $
b0 %
0"
b1001 #
#19
0!
#20
1!
"""

class TestVcdWrapper:
    def test_vcd_read(self, tmp_path):
        tmp_file = tmp_path / "test.vcd"
        with open(tmp_file, "w") as f:
            f.write(vcdtext)
        r = VcdWrapper(tmp_file, "Tile.clk")
        assert r.get_value_at("Tile.ctr", 0) == 0
        assert r.get_value_at("Tile.ctr", 1) == 1
