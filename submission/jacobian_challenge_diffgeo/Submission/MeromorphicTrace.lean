import Submission.MeromorphicTrace.MeromorphicTrace
import Submission.MeromorphicTrace.TraceForm
import Submission.MeromorphicTrace.TracePullback
import Submission.MeromorphicTrace.TraceResidue

/-!
# Meromorphic Trace (`Jacobians/MeromorphicTrace/`)

Surface-level trace of meromorphic functions/forms along a degree-d map and the argument principle on `X` (zeros = poles for `div f = 0` log-derivative traces).

**Keystones:** `ResidueTheoremX.zerosCount_eq_polesCount_of_logDerivTrace`; `residue change of variables`

**Builds on units:** jacobian-construction, mapping-degree, paths-and-integrals, residue-calculus
-/
