import Jacobians.PeriodLattice.JacobiBasePoints
import Jacobians.PeriodLattice.JacobiLocalMap
import Jacobians.PeriodLattice.OfCurveAnalyticitySkeleton
import Jacobians.PeriodLattice.PeriodLatticeBasis
import Jacobians.PeriodLattice.PeriodLatticeDiscrete
import Jacobians.PeriodLattice.PeriodLatticeNondegenerate

/-!
# Period Lattice Rank (`Jacobians/PeriodLattice/`)

The period lattice has a real basis of rank 2g (Forster 21.4, dissection-free): discreteness via the local Jacobi map, nondegeneracy, and the real basis.

**Keystones:** `exists_periodLattice_realBasis`

**Builds on units:** abel-theorem, abel-weak-solutions, holomorphic-forms, jacobian-construction, paths-and-integrals, residue-calculus, residue-theorem, surfaces-and-charts
-/
