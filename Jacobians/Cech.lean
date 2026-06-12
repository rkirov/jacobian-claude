import Jacobians.Cech.CechComplex
import Jacobians.Cech.CechH0
import Jacobians.Cech.CechRefinement
import Jacobians.Cech.CechRefinementHomotopy
import Jacobians.Cech.CechSection
import Jacobians.Cech.ChartDiskCover
import Jacobians.Cech.ChartDiskRefinement
import Jacobians.Cech.MeromorphicAnalyticBadSet

/-!
# Cech Cohomology (`Jacobians/Cech/`)

Čech theory for `𝒪_D`: junk-free germ cochains over `codiscreteWithin`, the complex, refinements, chart-disk covers, and `H⁰ = L(D)`.

**Keystones:** `CechH0.h0Dim_eq_lDim`; `CechComplex / MGerm cochains`

**Builds on units:** meromorphic-and-divisors
-/
