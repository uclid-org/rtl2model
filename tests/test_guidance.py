from easyila.guidance import Guidance, AnnoType
from easyila.synthesis_template import *

class TestGuidance:
    def test_output_annotations(self):
        signals = [
            S("Tile", "reset", 1),
            S("Tile", "clk", 1),
            S("Tile", "a", 32),
            S("Tile", "b", 32),
            S("Tile", "c", 32),
        ]
        guidance = Guidance(signals, 10)
        guidance.annotate("b", {8: AnnoType.OUTPUT})
        guidance.annotate("c", {9: AnnoType.OUTPUT})
        outputs = guidance.get_outputs()
        assert outputs == {("Tile->b", 8), ("Tile->c", 9)}

    def test_subscript_annotations(self):
        signals = [
            S("tb", "reset", 1),
            S("tb", "clk", 1),
            S("tb", "data", 8, bounds=(0, 7)),
        ]
        guidance = Guidance(signals, 10)
        guidance.annotate("data[0]", {7: AnnoType.PARAM})
        guidance.annotate("data[3]", {3: AnnoType.PARAM})
        assert guidance.get_annotation_at("data[0]", 7) == AnnoType.PARAM
        assert guidance.get_annotation_at("data[0]", 6) == AnnoType.DC
        assert guidance.get_annotation_at("data[0]", 8) == AnnoType.DC
        assert guidance.get_annotation_at("data[3]", 3) == AnnoType.PARAM
        assert guidance.get_annotation_at("data[3]", 2) == AnnoType.DC
        assert guidance.get_annotation_at("data[3]", 4) == AnnoType.DC
        assert guidance.get_annotation_at("data[1]", 7) == AnnoType.DC

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
        guidance.annotate("reset", {0: AnnoType.ASSM})
        guidance.annotate("a", {3: AnnoType.ASSM, 7: AnnoType.PARAM})
        guidance.annotate("b", {8: AnnoType.OUTPUT})
        guidance.annotate("data[0]", {7: AnnoType.PARAM})
        guidance.annotate("data[3]", {3: AnnoType.PARAM})
        for cycle in range(guidance.num_cycles):
            for ind, signal in enumerate(guidance.signals):
                for qp in signal.get_all_qp_instances():
                    atype = guidance.get_annotation_at(qp, cycle)
                    if atype == AnnoType.DC:
                        pass
                    elif atype == AnnoType.ASSM:
                        found_assumes.add((qp, cycle))
                    elif atype == AnnoType.PARAM:
                        found_params.add((qp, cycle))
                    elif atype == AnnoType.OUTPUT:
                        found_outputs.add((qp, cycle))
                    else:
                        raise TypeError("invalid AnnoType: " + str(atype))
        assert found_params == {("tb->a", 7), ("tb->data[0]", 7), ("tb->data[3]", 3)}
        assert found_assumes == {("tb->reset", 0), ("tb->a", 3)}
        assert found_outputs == {("tb->b", 8)}
