import Submission.Finiteness.BddHol
import Submission.Finiteness.CechFiniteness
import Submission.Finiteness.CechFinitenessAbstract
import Submission.Finiteness.CechFinitenessAssembly
import Submission.Finiteness.CechFinitenessDtwist
import Submission.Finiteness.CechFinitenessWiring
import Submission.Finiteness.CechModelArtificial
import Submission.Finiteness.CechModelBase
import Submission.Finiteness.CechModelBridge
import Submission.Finiteness.CechModelDelta
import Submission.Finiteness.CechModelDifferential
import Submission.Finiteness.CechModelGeometry
import Submission.Finiteness.CechModelHolomorphic
import Submission.Finiteness.CechModelHolomorphicDelta
import Submission.Finiteness.CechModelManifold
import Submission.Finiteness.CechRefinementInjective
import Submission.Finiteness.CechRefinementLeray
import Submission.Finiteness.ChartDiskFiniteness
import Submission.Finiteness.ChartDiskFinitenessComplete
import Submission.Finiteness.ChartDiskLeray
import Submission.Finiteness.CohomologicalH0Finiteness
import Submission.Finiteness.CohomologicalRR
import Submission.Finiteness.CohomologicalRRChartDisk
import Submission.Finiteness.SchwartzFiniteness
import Submission.Finiteness.SkyscraperArrow
import Submission.Finiteness.SkyscraperAssembly
import Submission.Finiteness.SkyscraperConeRealization
import Submission.Finiteness.SkyscraperLESBase
import Submission.Finiteness.SkyscraperProductWitness
import Submission.Finiteness.SkyscraperSnake

/-!
# Finiteness And Chi (`Jacobians/Finiteness/`)

Finite-dimensionality of `H¹(X, 𝒪_D)` (Forster §14, Schwartz + Montel functional-analysis spine) and the Euler-characteristic / cohomological Riemann–Roch bookkeeping via skyscraper sequences.

**Keystones:** `finiteDimensional_cechH1`; `exists_cechModel`; `cohomological χ(D) ledger`

**Builds on units:** cech-cohomology, dbar-solvability, dolbeault-comparison, holomorphic-forms
-/
