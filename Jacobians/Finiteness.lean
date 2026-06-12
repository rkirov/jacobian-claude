import Jacobians.Finiteness.BddHol
import Jacobians.Finiteness.CechFiniteness
import Jacobians.Finiteness.CechFinitenessAbstract
import Jacobians.Finiteness.CechFinitenessAssembly
import Jacobians.Finiteness.CechFinitenessDtwist
import Jacobians.Finiteness.CechFinitenessWiring
import Jacobians.Finiteness.CechModelArtificial
import Jacobians.Finiteness.CechModelBase
import Jacobians.Finiteness.CechModelBridge
import Jacobians.Finiteness.CechModelDelta
import Jacobians.Finiteness.CechModelDifferential
import Jacobians.Finiteness.CechModelGeometry
import Jacobians.Finiteness.CechModelHolomorphic
import Jacobians.Finiteness.CechModelHolomorphicDelta
import Jacobians.Finiteness.CechModelManifold
import Jacobians.Finiteness.CechRefinementInjective
import Jacobians.Finiteness.CechRefinementLeray
import Jacobians.Finiteness.ChartDiskFiniteness
import Jacobians.Finiteness.ChartDiskFinitenessComplete
import Jacobians.Finiteness.ChartDiskLeray
import Jacobians.Finiteness.CohomologicalH0Finiteness
import Jacobians.Finiteness.CohomologicalRR
import Jacobians.Finiteness.CohomologicalRRChartDisk
import Jacobians.Finiteness.SchwartzFiniteness
import Jacobians.Finiteness.SkyscraperArrow
import Jacobians.Finiteness.SkyscraperAssembly
import Jacobians.Finiteness.SkyscraperConeRealization
import Jacobians.Finiteness.SkyscraperLESBase
import Jacobians.Finiteness.SkyscraperProductWitness
import Jacobians.Finiteness.SkyscraperSnake

/-!
# Finiteness And Chi (`Jacobians/Finiteness/`)

Finite-dimensionality of `H¹(X, 𝒪_D)` (Forster §14, Schwartz + Montel functional-analysis spine) and the Euler-characteristic / cohomological Riemann–Roch bookkeeping via skyscraper sequences.

**Keystones:** `finiteDimensional_cechH1`; `exists_cechModel`; `cohomological χ(D) ledger`

**Builds on units:** cech-cohomology, dbar-solvability, dolbeault-comparison, holomorphic-forms
-/
