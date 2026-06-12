import Submission.ResidueTheorem.OmegaFactorization
import Submission.ResidueTheorem.PairFormResidueTheorem
import Submission.ResidueTheorem.ResidueLedgerTransport
import Submission.ResidueTheorem.ResidueStokesCoverPoU
import Submission.ResidueTheorem.ResidueStokesPoleBump
import Submission.ResidueTheorem.ResidueTheoremFormFn
import Submission.ResidueTheorem.ResidueTheoremStokes

/-!
# Residue Theorem (`Jacobians/ResidueTheorem/`)

The unconditional residue theorem `∑_p Res_p(h·dg₀) = 0` for meromorphic pair forms on a compact surface, any genus, via partition of unity + planar Stokes.

**Keystones:** `residueSum_pairForm_eq_zero_unconditional`

**Builds on units:** canonical-forms, cech-cohomology, dbar-solvability, finiteness-and-chi, holomorphic-forms, meromorphic-and-divisors, planar-stokes-atoms, residue-calculus
-/
