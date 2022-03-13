
import textwrap

import pytest

from easyila.verilog.pipeline_partition import *
import easyila.lynth.smt as smt
from easyila.model import Model

class TestPartition:
    """
    Tests the Verilog pipeline partitioning algorithm.
    """

    def test_sequential(self):
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
        bv1 = smt.BVSort(1)
        v = lambda s: smt.Variable(s, bv1)
        assert partitions == \
            Model(
                [v("in")],      # inputs
                [v("out")],     # outputs
                [],             # internal state
                {               # submodules
                    "p0": Model(
                        [v("in")],
                        [v("v1"), v("v2")], # TODO should this also have the next value somewhere?
                        [],
                        {},
                        {
                            "NEXT": [
                                # TODO distinguish variable declarations and references
                                # order here matters!
                                {"v1": v("in"), "__next_v1": v("v1")},
                                {"v2": v("v1"), "__next_v2": v("v2")}
                            ]
                        },
                    ),
                },
                {               # instructions
                    "NEXT": [
                        {"out": smt.BinOpExpr(smt.Kind.BVAdd, v("p0.v1"), v("p1.v2"))}
                    ]
                }
            )

    # @pytest.mark.skip()
    def test_self_reference(self):
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
                [v("in")],      # inputs
                [v("out")],     # outputs
                [],             # internal state
                {               # submodules
                    "p0": Model(
                        [v("in")],
                        [v("v1")],
                        [v("__next_v1")],
                        {},
                        {
                            "NEXT": [
                                {"__next_v1": v("in"), "v1": v("__next_v1")},
                            ]
                        },
                    ),
                },
                {               # instructions
                    "NEXT": [
                        {"out": v("p0.v1")}
                    ]
                }
            )

    # @pytest.mark.skip()
    def test_multiple_reassign(self):
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

    def test_combinatorial(self):
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
                [v("in")],      # inputs
                [v("out")],     # outputs
                [],             # state
                {               # submodules
                    "p0": Model(
                        [v("in")],
                        [v("v1")],
                        [],
                        {
                            "NEXT": [
                                # TODO distinguish variable declarations and references
                                {"v1": v("in")}
                            ]
                        },
                    ),
                    "p1": Model(
                        [v("v1")],
                        [v("v2")],
                        [],
                        {
                            "NEXT": [
                                {"v2": v("v1")}
                            ]
                        },
                    ),

                },
                {               # instructions
                    "NEXT": [
                        {"out": smt.BinOpExpr(smt.Kind.BVAdd, v("p0.v1"), v("p1.v2"))}
                    ]
                }
            )
