
import textwrap

import pytest

from easyila.verilog.pipeline_partition import *
import easyila.lynth.smt as smt
from easyila.model import Model

class TestPartition:
    """
    Tests the Verilog pipeline partitioning algorithm.
    """

    def test_partition_sequential(self):
        """
        Verifies pipeline decomposition for a simple module with a sequential assignment.

        Because the assignment in the always@ block is sequential, v2 and v1 should belong
        to the same pipeline stage.
        """
        rtl = textwrap.dedent("""\
            module pipe(input clk, input in, output out);
                reg v1 = 0;
                reg v2 = 0;
                always @(posedge clk) begin
                    v1 = in;
                    v2 = v1;
                end
                assign out = v1 | v2;
            endmodule
            """
        )
        partitions = partition(rtl, "pipe")
        print("partitions:")
        for p in partitions:
            p.print()
        bv1 = smt.BVSort(1)
        v = lambda s: smt.Variable(s, bv1)
        assert partitions == \
            Model(
                "pipe",
                inputs=[v("in")],      # inputs
                outputs=[v("out")],     # outputs
                submodules={               # submodules
                    "p0": Model(
                        inputs=[v("in")],
                        outputs=[v("v1"), v("v2")], # TODO should this also have the next value somewhere?
                        instructions={
                            "NEXT": [
                                # TODO distinguish variable declarations and references
                                # order here matters!
                                {"v1": v("in"), "__next_v1": v("v1")},
                                {"v2": v("v1"), "__next_v2": v("v2")}
                            ]
                        },
                    ),
                },
                instructions={               # instructions
                    "NEXT": [
                        {"out": smt.OpTerm(smt.Kind.BVAdd, (v("p0.v1"), v("p1.v2")))}
                    ]
                }
            )

    # @pytest.mark.skip()
    def test_partition_self_reference(self):
        """
        Tests behavior for when a register's next value depends on its old value.
        """
        rtl = textwrap.dedent("""\
            module pipe(input clk, input in, output out);
                reg v1 = 0;
                always @(posedge clk) begin
                    v1 = in | v1;
                end
                assign out = v1;
            endmodule
        """)
        partitions = partition(rtl, "pipe")
        bv1 = smt.BVSort(1)
        v = lambda s: smt.Variable(s, bv1)
        print("partitions:")
        for p in partitions:
            p.print()
        assert partitions == \
            Model(
                "pipe",
                inputs=[v("in")],      # inputs
                outputs=[v("out")],     # outputs
                submodules={               # submodules
                    "p0": Model(
                        inputs=[v("in")],
                        outputs=[v("v1")],
                        state=[v("__next_v1")],
                        instructions={
                            "NEXT": [
                                {"__next_v1": v("in"), "v1": v("__next_v1")},
                            ]
                        },
                    ),
                },
                instructions={               # instructions
                    "NEXT": [
                        {"out": v("p0.v1")}
                    ]
                }
            )

    # @pytest.mark.skip()
    def test_partition_multiple_reassign(self):
        """
        Tests behavior for when a signal is reassigned multiple times in the same cycle.

        The last _rnN_ signal will always be the value of the signal on the next clock cycle.
        Everything else should probably be inlined.
        """
        rtl = textwrap.dedent("""\
            module pipe(input clk, input in, output out);
                reg v1 = 0;
                reg v2 = 0;
                always @(posedge clk) begin
                    v1 = in ^ v2;
                    v2 = v1;
                    v1 = v2 ^ in;
                end
                assign out = v1 | v2;
            endmodule
            """
        )
        partitions = partition(rtl, "pipe")
        print("partitions:")
        for p in partitions:
            p.print()
        assert False

    def test_partition_s_pipe(pc):
        # For simplicity, we have 8-bit instructions and an 8-bit memory
        # Register file contains 4 8-bit entries
        rtl = textwrap.dedent("""\
            module pipe(input clk, input [7:0] pc, output [7:0] out);
                reg [7:0] imem [0:7];
                reg [1:0] rf [0:7];
                wire [7:0] inst = imem[pc];
                reg [7:0] fe_pc;
                reg [7:0] fe_inst;
                reg [7:0] ew_pc;
                reg [7:0] ew_inst;
                wire [7:0] rs1_v = rf[inst[1:0]];
                wire [7:0] rs2_v = rf[inst[3:2]];
                wire [1:0] rd = inst[5:4];
                reg [7:0] fe_rs1_v;
                reg [7:0] fe_rs2_v;
                reg [1:0] fe_rd;
                reg [7:0] ew_val;
                reg [7:0] ew_rd;

                always @(posedge clk) begin
                    fe_pc <= pc;
                    ew_pc <= fe_pc;
                    fe_inst <= inst;
                    ew_inst <= fe_inst;
                    fe_rs1_v <= rs1_v;
                    fe_rs2_v <= rs2_v;
                    fe_rd <= rd;
                    ew_val <= fe_rs1_v + fe_rs2_v;
                    ew_rd <= fe_rd;
                    rf[ew_rd] <= ew_val;
                end
                assign out = rf[ew_rd];
            endmodule
            """)
        partitions = partition(rtl, "pipe")
        print("partitions:")
        for p in partitions:
            p.print()
        assert False

    def test_partition_combinatorial(self):
        """
        Verifies pipeline decomposition for a simple module with combinatorial assignment.

        Because v2 and v1 are assigned with the <= operator, they now belong to 2 separate
        pipeline stages.
        """
        rtl = textwrap.dedent("""\
            module pipe(input clk, input in, output out);
                reg v1 = 0;
                reg v2 = 0;
                always @(posedge clk) begin
                    v1 <= in;
                    v2 <= v1;
                end
                assign out = v1 | v2;
            endmodule
            """
        )
        partitions = partition(rtl, "pipe")
        print("partitions:")
        for p in partitions:
            p.print()
        bv1 = smt.BVSort(1)
        v = lambda s: smt.Variable(s, bv1)
        assert partitions == \
            Model(
                "pipe",
                inputs=[v("in")],      # inputs
                outputs=[v("out")],     # outputs
                submodules={               # submodules
                    "p0": Model(
                        inputs=[v("in")],
                        outputs=[v("v1")],
                        instructions={
                            "NEXT": [
                                # TODO distinguish variable declarations and references
                                {"v1": v("in")}
                            ]
                        },
                    ),
                    "p1": Model(
                        inputs=[v("v1")],
                        outputs=[v("v2")],
                        instructions={
                            "NEXT": [
                                {"v2": v("v1")}
                            ]
                        },
                    ),

                },
                logic={
                    v("out"): smt.OpTerm(smt.Kind.BVAdd, (v("p0.v1"), v("p1.v2"))),
                },
                instructions={               # instructions
                    "NEXT": [
                        "p0.next"
                    ]
                }
            )
