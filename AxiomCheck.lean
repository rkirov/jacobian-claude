/-
Verify the port: `ContMDiff.degree` and `Jacobians.degreeFiber` should
depend only on `[propext, Classical.choice, Quot.sound]`, never `sorryAx`.
Run with `lake env lean AxiomCheck.lean`.

This file is not part of the library — it's a one-off audit script.
-/
import Jacobians

#print axioms ContMDiff.degree
#print axioms Jacobians.degreeFiber
#print axioms Jacobians.RegularValueWitnessReg.card
#print axioms Jacobians.degreeFiber_const
#print axioms Jacobians.degreeFiber_eq_zero_of_no_witness
