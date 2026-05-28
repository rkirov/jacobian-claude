/-
Verify the discharge port: every key declaration depends only on
[propext, Classical.choice, Quot.sound] — no sorryAx. Run:
  lake env lean AxiomCheck.lean
-/
import Jacobians
import Jacobians.Discharge.Manifold.RegularValueExistsRegUnconditional

#print axioms ContMDiff.degree
#print axioms Jacobians.degreeFiber
#print axioms Jacobians.RegularValueWitnessReg
#print axioms Jacobians.regularValueWitnessReg_nonempty_of_nonConstantMap
#print axioms Jacobians.Discharge.ContMDiff.degreeFiber
#print axioms Jacobians.Discharge.ContMDiff.Owed.degree.regular_value_exists_reg_holds_unconditional
#print axioms Jacobians.Discharge.ContMDiff.Owed.degree.regular_value_exists_statement_holds_unconditional

-- Newly-closed local theorems (3 sorries → 0):
#print axioms Jacobians.isClosed_criticalSet
#print axioms Jacobians.criticalSet_ne_univ_of_nonconstant
#print axioms Jacobians.finite_criticalSet_of_nonconstant
#print axioms Jacobians.finite_branchLocus_of_nonconstant
-- Note: `ramificationSumEqualsDegree_holds_unconditional` lives in the
-- Brsanch repo's `NearbyRegularWitnessUnconditional.lean` chain, not in
-- the 42-file closure we ported. Audit confirmed it clean upstream; not
-- needed for our local `pushforward_pullback`, which goes via
-- `ambientPhi_ambientPsi_eq` (still sorry'd in `HolomorphicForms.lean`).
