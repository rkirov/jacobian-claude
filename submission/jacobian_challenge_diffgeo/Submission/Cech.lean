import Submission.Cech.CechComplex
import Submission.Cech.CechH0
import Submission.Cech.CechRefinement
import Submission.Cech.CechRefinementHomotopy
import Submission.Cech.CechSection
import Submission.Cech.ChartDiskCover
import Submission.Cech.ChartDiskRefinement
import Submission.Cech.MeromorphicAnalyticBadSet

/-!
# Cech Cohomology (`Jacobians/Cech/`)

Čech theory for `𝒪_D`: junk-free germ cochains over `codiscreteWithin`, the complex, refinements, chart-disk covers, and `H⁰ = L(D)`.

**Keystones:** `CechH0.h0Dim_eq_lDim`; `CechComplex / MGerm cochains`

**Builds on units:** meromorphic-and-divisors
-/
