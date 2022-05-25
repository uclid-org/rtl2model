
import cvc5

from rtl2model.lynth import smt

class TestSmtCvc5Conversion:
    """
    Tests conversion of objects in our SMT library to the corresponding CVC5 type, and vice versa.
    """

    def test_array_to_cvc5(self):
        c_slv = cvc5.Solver()
        c_slv.setOption("lang", "sygus2")
        c_slv.setOption("incremental", "false")
        c_slv.setLogic("BV")
        bv32 = c_slv.mkBitVectorSort(32)
        bv5 = c_slv.mkBitVectorSort(5)
        exp_arr = c_slv.mkArraySort(bv5, bv32)
        ctx = smt.Solver(backend="cvc5")._cvc5_wrapper
        assert smt.ArraySort(smt.BVSort(5), smt.BVSort(32)).to_cvc5(ctx) == exp_arr

    def test_array_from_cvc5(self):
        c_slv = cvc5.Solver()
        c_slv.setOption("lang", "sygus2")
        c_slv.setOption("incremental", "false")
        c_slv.setLogic("BV")
        bv32 = c_slv.mkBitVectorSort(32)
        bv5 = c_slv.mkBitVectorSort(5)
        arr = c_slv.mkArraySort(bv5, bv32)
        exp_arr = smt.ArraySort(smt.BVSort(5), smt.BVSort(32))
        assert smt.Sort.from_cvc5(arr) == exp_arr
