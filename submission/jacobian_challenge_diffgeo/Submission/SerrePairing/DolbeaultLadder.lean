/-
  The Čech finiteness headline.

  Riemann–Roch (`Jacobians.exists_riemannRoch_divisor`) is proven via the Miranda Laurent-tail
  route (`LaurentTail.exists_riemannRoch_divisor_unconditional`, wired in `RiemannRoch.lean`), so
  this file carries only the load-bearing finiteness headline:

    * `finiteDimensional_cechH1` — finiteness (Forster 14.9): disk-Montel +
      Schwartz/Riesz–Schauder (`finiteDimensional_cechH1_wired`).

  The Čech tower imported here (cohomological RR / skyscraper LES / `h0Dim_eq_lDim`) feeds the
  Riemann inequality and `exists_nonconstant_meromorphic`, which the tail route's pole-budget
  bound consumes.
-/
import Submission.Finiteness.CechFinitenessWiring
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Finiteness (Forster Thm 14.9).** `H¹(𝔘, 𝒪_D)` is finite-dimensional. Engine: the cochain
restriction between a cover and a relatively-compact shrinking is *compact* (disk-Montel: Mathlib
`Analysis.Complex.LocallyUniformLimit` + Arzelà–Ascoli), and a compact perturbation has
finite-codimensional image (Schwartz / Riesz–Schauder, via Mathlib `IsCompactOperator` +
`RieszLemma`). -/
theorem finiteDimensional_cechH1 (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.cechH1 D) :=
  finiteDimensional_cechH1_wired 𝔘 D

/- **Cohomological Riemann–Roch (χ-additivity, Forster §16)** is in `CohomologicalRR.lean`
(imported above); `cohomological_riemannRoch` is in scope here via the import.  Serre duality at
the Čech level (`arithmeticGenus_eq_genus`, `serre_h1_eq`) is delivered, genus-uniformly, by
`LaurentTail.h1TailDim_zero_eq_genus_unconditional`,
`LaurentTail.h1TailDim_eq_lDim_pairCanonical_sub`, and
`LaurentTail.exists_riemannRoch_divisor_unconditional` (on the Mittag-Leffler tail `H¹`). -/

end Jacobians.Dolbeault
