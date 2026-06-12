import Submission.PeriodLattice.JacobiBasePoints
import Submission.PeriodLattice.JacobiLocalMap
import Submission.PeriodLattice.OfCurveAnalyticitySkeleton
import Submission.PeriodLattice.PeriodLatticeBasis
import Submission.PeriodLattice.PeriodLatticeDiscrete
import Submission.PeriodLattice.PeriodLatticeNondegenerate

/-!
# Period Lattice Rank (`Jacobians/PeriodLattice/`)

The period lattice has a real basis of rank 2g (Forster 21.4, dissection-free): discreteness via the local Jacobi map, nondegeneracy, and the real basis.

**Keystones:** `exists_periodLattice_realBasis`

**Builds on units:** abel-theorem, abel-weak-solutions, holomorphic-forms, jacobian-construction, paths-and-integrals, residue-calculus, residue-theorem, surfaces-and-charts
-/
