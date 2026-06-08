/-
  Dolbeault ladder — local realizability of the canonical chart-disk cover (the product witness /
  local Mittag–Leffler), the single analytic input the cone skyscraper construction
  (`SkyscraperConeRealization`) consumes.

  ## What this file is for

  `SkyscraperConeRealization` reduces the skyscraper local-realization datum (and hence the whole
  χ-side of cohomological Riemann–Roch) to one hypothesis on the cover, `LocallyRealizable 𝔘`: the
  order-`(−D(P)−1)` principal-part coefficient `coeffGermLin` is *surjective* at every cover-set
  `U j ∋ P`, for every divisor `D`.  Equivalently (`coeffGermLin` is ℂ-linear into `ℂ`): there is a
  section `g ∈ 𝒪_{D+P}(U j)` whose order at `P` is *exactly* `k = −(D P) − 1`, so its top Laurent
  coefficient is nonzero.

  This holds for the **canonical chart-disk cover** `chartDiskCover` because each cover-set `U j` sits
  inside the source of a single chart `φ = chartAt (center j)` (`ChartDiskCover.subset_chart_source`),
  on which the **product witness**

      `g = ∏_{Q ∈ supp(D+P) ∩ U j} (φ − φ(Q))^{−(D+P)(Q)}`

  is meromorphic with `ord_Q g = −(D+P)(Q)` at each support point `Q` (the other factors being analytic
  and nonzero there) and `ord_x g = 0 ≥ −(D+P)(x)` elsewhere.  In particular `ord_P g = −(D+P)(P) = k`
  exactly, so `coeffGermLin [g] ≠ 0` and `coeffGermLin` is onto `ℂ`.

  ## Status

  The product witness is the genuine local-analytic core (a finite-product order computation plus the
  chart-change relating the center chart `φ` to the open-submanifold chart at `P` that `ordU`/`coeffGermLin`
  use).  It is isolated here as the single named obligation `locallyRealizable_chartDiskCover`; closing
  it makes the entire χ-side (`cohomological_riemannRoch`) fully sorry-free on the canonical cover.
-/
import Jacobians.Dolbeault.SkyscraperConeRealization
import Jacobians.Dolbeault.LerayCoverExists

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Local realizability of the canonical chart-disk cover** (the product witness / local
Mittag–Leffler).  At every chart-disk cover-set `U j ∋ P`, the order-`(−D(P)−1)` principal-part
coefficient `coeffGermLin` is surjective onto `ℂ`, for every divisor `D`.

THE SINGLE NAMED ANALYTIC OBLIGATION of the χ-side.  The witness is the product
`∏_{Q ∈ supp(D+P) ∩ U j} (φ − φ(Q))^{−(D+P)(Q)}` in the center chart `φ` of `U j`
(`ChartDiskCover.subset_chart_source` gives `U j ⊆ φ.source`); its order at `P` is exactly
`k = −(D P) − 1` (forced poles/zeros at the other support points handle a general `D`), so its top
Laurent coefficient is nonzero, hence `coeffGermLin` — ℂ-linear into `ℂ` — is onto. -/
theorem locallyRealizable_chartDiskCover :
    (chartDiskCover (X := X)).toFiniteCover.LocallyRealizable :=
  sorry

/-- **A realizable Leray cover exists** — the canonical chart-disk cover is both Leray (simply
connected sets, `chartDiskCover_simplyConnected`) and locally realizable
(`locallyRealizable_chartDiskCover`).  This unlocks the ladder→headline wiring with the cone
skyscraper construction. -/
theorem exists_realizableLerayCover :
    ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray ∧ 𝔘.LocallyRealizable :=
  ⟨(chartDiskCover (X := X)).toFiniteCover,
    ⟨fun i => by simpa using chartDiskCover_simplyConnected (X := X) i,
      locallyRealizable_chartDiskCover⟩⟩

end Jacobians.Dolbeault
