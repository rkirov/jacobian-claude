import Submission.Abel.AbelDbarKill
import Submission.Abel.AbelEngineMeromorphic
import Submission.Abel.AbelEngineSigma
import Submission.Abel.AbelFinal
import Submission.Abel.AbelFormRead
import Submission.Abel.AbelLogDbar
import Submission.Abel.AbelPairing
import Submission.Abel.AbelPairingPositivity
import Submission.Abel.AbelPairingStokes

/-!
# Abel Theorem (`Jacobians/Abel/`)

Abel's theorem (Forster 20.7, dissection-free): the two-point Abel–Jacobi value is nonzero for distinct points on genus ≥ 1, hence `ofCurve` is injective.

**Keystones:** `abelJacobi_twoPoint_ne_zero`

**Builds on units:** abel-weak-solutions, cech-h1-genus, dolbeault-comparison, finiteness-and-chi, form-trace-tower, planar-stokes-atoms, proper-map-degree, residue-theorem
-/
