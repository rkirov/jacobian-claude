import Jacobians.Abel.AbelDbarKill
import Jacobians.Abel.AbelEngineMeromorphic
import Jacobians.Abel.AbelEngineSigma
import Jacobians.Abel.AbelFinal
import Jacobians.Abel.AbelFormRead
import Jacobians.Abel.AbelLogDbar
import Jacobians.Abel.AbelPairing
import Jacobians.Abel.AbelPairingPositivity
import Jacobians.Abel.AbelPairingStokes

/-!
# Abel Theorem (`Jacobians/Abel/`)

Abel's theorem (Forster 20.7, dissection-free): the two-point Abel–Jacobi value is nonzero for distinct points on genus ≥ 1, hence `ofCurve` is injective.

**Keystones:** `abelJacobi_twoPoint_ne_zero`

**Builds on units:** abel-weak-solutions, cech-h1-genus, dolbeault-comparison, finiteness-and-chi, form-trace-tower, planar-stokes-atoms, proper-map-degree, residue-theorem
-/
