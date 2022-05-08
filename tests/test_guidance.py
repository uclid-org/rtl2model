
from rtl2synth.guidance import Guidance, AnnoType
from rtl2synth.synthesis_template import *
import rtl2synth.lynth.smt as smt

class TestGuidance:

    def test_guard_annotation(self):
        pc_sig = S("Tile","pc", 32)
        a_sig = S("Tile", "a", 32)
        a_var = a_sig.to_variable()
        b_var = smt.bv_variable("b", 32)
        o_var = smt.bv_variable("o", 32)
        signals = [
            S("Tile", "reset", 1),
            pc_sig,
            a_sig,
            S("Tile", "b", 32),
        ]
        guidance = Guidance(signals, 10)
        guidance.annotate("reset", AnnoType.ASSUME)
        # Maps predicates to corresponding AnnoType
        guidance.annotate("a", {
            pc_sig.to_variable().op_eq(6): AnnoType.Param(a_var),
            smt.BoolConst.T: AnnoType.DONT_CARE,
        })
        guidance.annotate("b", {
            pc_sig.to_variable().op_eq(6): AnnoType.ASSUME,
            pc_sig.to_variable().op_eq(7): AnnoType.Param(b_var),
            pc_sig.to_variable().op_eq(8): AnnoType.Output(o_var),
            smt.BoolConst.T: AnnoType.ASSUME,
        })
        assert guidance.get_annotation_at("a", 4) is None
        assert guidance.get_predicated_annotations("a") == {
            pc_sig.to_variable().op_eq(6): [AnnoType.Param(a_var)],
            smt.BoolConst.T: [AnnoType.DONT_CARE],
        }
        assert guidance.get_outputs() == {
            (o_var, "Tile->b", pc_sig.to_variable().op_eq(8))
        }

    def test_output_annotations(self):
        signals = [
            S("Tile", "reset", 1),
            S("Tile", "clk", 1),
            S("Tile", "a", 32),
            S("Tile", "b", 32),
            S("Tile", "c", 32),
        ]
        guidance = Guidance(signals, 10)
        b_var = smt.bv_variable("b", 32)
        c_var = smt.bv_variable("c", 32)
        guidance.annotate("b", {8: AnnoType.Output(b_var)})
        guidance.annotate("c", {9: AnnoType.Output(c_var)})
        outputs = guidance.get_outputs()
        assert outputs == {(b_var, "Tile->b", 8), (c_var, "Tile->c", 9)}

    def test_subscript_annotations(self):
        signals = [
            S("tb", "reset", 1),
            S("tb", "clk", 1),
            S("tb", "data", 8, bounds=(0, 7)),
        ]
        d0 = smt.bv_variable("d0", 8)
        d1 = smt.bv_variable("d1", 8)
        guidance = Guidance(signals, 10)
        guidance.annotate("data[0]", {7: AnnoType.Param(d0)})
        guidance.annotate("data[3]", {3: AnnoType.Param(d1)})
        assert guidance.get_annotation_at("data[0]", 7) == AnnoType.Param(d0)
        assert guidance.get_annotation_at("data[0]", 6) == AnnoType.DONT_CARE
        assert guidance.get_annotation_at("data[0]", 8) == AnnoType.DONT_CARE
        assert guidance.get_annotation_at("data[3]", 3) == AnnoType.Param(d1)
        assert guidance.get_annotation_at("data[3]", 2) == AnnoType.DONT_CARE
        assert guidance.get_annotation_at("data[3]", 4) == AnnoType.DONT_CARE
        assert guidance.get_annotation_at("data[1]", 7) == AnnoType.DONT_CARE

    def test_guidance_iterate(self):
        signals = [
            S("tb", "reset", 1),
            S("tb", "clk", 1),
            S("tb", "data", 8, bounds=(0, 7)),
            S("tb", "a", 8),
            S("tb", "b", 8)
        ]
        guidance = Guidance(signals, 10)
        found_params = set()
        found_assumes = set()
        found_outputs = set()
        guidance.annotate("reset", {0: AnnoType.ASSUME})
        a_var = smt.bv_variable("a", 8)
        d0_var = smt.bv_variable("d0", 8)
        d1_var = smt.bv_variable("d1", 8)
        o_var = smt.bv_variable("o", 32)
        guidance.annotate("a", {3: AnnoType.ASSUME, 7: AnnoType.Param(a_var)})
        guidance.annotate("b", {8: AnnoType.Output(o_var)})
        guidance.annotate("data[0]", {7: AnnoType.Param(d0_var)})
        guidance.annotate("data[3]", {3: AnnoType.Param(d1_var)})
        for cycle in range(guidance.num_cycles):
            for ind, signal in enumerate(guidance.signals):
                for qp in signal.get_all_qp_instances():
                    atype = guidance.get_annotation_at(qp, cycle)
                    if atype.is_dont_care():
                        pass
                    elif atype.is_assume():
                        found_assumes.add((qp, cycle))
                    elif atype.is_param():
                        found_params.add((qp, cycle))
                    elif atype.is_output():
                        found_outputs.add((qp, cycle))
                    else:
                        raise TypeError("invalid AnnoType: " + str(atype))
        assert found_params == {("tb->a", 7), ("tb->data[0]", 7), ("tb->data[3]", 3)}
        assert found_assumes == {("tb->reset", 0), ("tb->a", 3)}
        assert found_outputs == {("tb->b", 8)}

    def test_guidance_indexed(self):
        signals = [
            S("tb", "reset", 1),
            S("tb", "clk", 1),
            S("tb", "data", 8, bounds=(0, 7)),
            S("tb", "a", 8),
            S("tb", "b", 8)
        ]
        guidance = Guidance(signals, 10)
        found_params = set()
        found_assumes = set()
        found_outputs = set()
        a_var = smt.bv_variable("a", 8)
        d0_var = smt.bv_variable("d0", 8)
        b_var = smt.bv_variable("b", 32)
        b_eqz = b_var.op_eq(0)
        guidance.annotate("a", {
            b_eqz: [
                AnnoType.AssumeIndexed((5, 4), (1, 0)),
                AnnoType.ParamIndexed((3, 2), d0_var),
            ],
            smt.BoolConst.T: AnnoType.ASSUME,
        })
        found_assumes = list()
        found_params = list()
        for cond, annolist in guidance.get_predicated_annotations("a").items():
            for anno in annolist:
                if anno.is_assume():
                    found_assumes.append((cond, anno.bounds))
                elif anno.is_param():
                    found_params.append((cond, anno.expr, anno.bounds))
                else:
                    raise TypeError("invalid AnnoType: " + str(anno))
        assert found_assumes == [(b_eqz, ((5, 4), (1, 0))), (smt.BoolConst.T, [])]
        print(found_params[0]   )
        assert found_params == [(b_eqz, d0_var, [(3, 2)])]
