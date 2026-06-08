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
import Mathlib.Analysis.Meromorphic.FactorizedRational

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Filter

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Surjectivity of `coeffGermLin` from a single nonzero coefficient

`coeffGermLin` is ℂ-linear into `ℂ`; if some germ has nonzero coefficient, scaling realises every
value, so the map is onto. -/

/-- **`coeffGermLin` is surjective once it is nonzero.**  Given `γ₀ ∈ 𝒪_{D+P}(W)` with
`coeffGermLin γ₀ = c ≠ 0`, every `a : ℂ` is `coeffGermLin ((a/c) • γ₀)`. -/
theorem coeffGermLin_surjective_of_ne_zero {W : Opens X} {D : Divisor X} {P : X} (hP : P ∈ W)
    {γ₀ : OmegaDGerm (D + Finsupp.single P 1) W} (hc : coeffGermLin hP (D := D) γ₀ ≠ 0) :
    Function.Surjective (coeffGermLin hP (D := D)) := by
  intro a
  refine ⟨(a / coeffGermLin hP (D := D) γ₀) • γ₀, ?_⟩
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hc]

/-- **A section of order *exactly* `−(D P)−1` at `P` has nonzero coefficient.**  For
`g ∈ 𝒪_{D+P}(W)` with `ordU g ⟨P,hP⟩ = −(D P)−1` (the minimal allowed order, a genuine pole of that
exact order), the order-`(−D(P)−1)` coefficient is nonzero (`coeffWFn_eq_zero_iff`: it vanishes iff
the order is *strictly* larger). -/
theorem coeffGermLin_ne_zero_of_ordU_eq {W : Opens X} {D : Divisor X} {P : X} (hP : P ∈ W)
    {g : W → ℂ} (hg : g ∈ OmegaD (D + Finsupp.single P 1) W)
    (hord : ordU g ⟨P, hP⟩ = ((-(D P) - 1 : ℤ) : WithTop ℤ)) :
    coeffGermLin hP (D := D) ⟨toGerm W g, ⟨g, hg, rfl⟩⟩ ≠ 0 := by
  show coeffGermFn (-(D P) - 1) ⟨P, hP⟩ (toGerm W g) ≠ 0
  rw [coeffGermFn_coe, Ne, coeffWFn_eq_zero_iff hg.1 (le_of_eq hord.symm)]
  -- `¬ (k < ordU g P)` since `ordU g P = k`.
  rw [hord]
  exact lt_irrefl _

/-- **Per-cover-set realizability from a witness of exact order.**  If for every `D` and `P ∈ W` there
is a section of `𝒪_{D+P}(W)` of order *exactly* `−(D P)−1` at `P`, then `coeffGermLin` is surjective at
`W` (the local Mittag–Leffler condition).  The product witness supplies such a section on a chart-disk. -/
theorem coeffGermLin_surjective_of_exists_witness {W : Opens X} {D : Divisor X} {P : X} (hP : P ∈ W)
    (hwit : ∃ g : W → ℂ, ∃ hg : g ∈ OmegaD (D + Finsupp.single P 1) W,
      ordU g ⟨P, hP⟩ = ((-(D P) - 1 : ℤ) : WithTop ℤ)) :
    Function.Surjective (coeffGermLin hP (D := D)) := by
  obtain ⟨g, hg, hord⟩ := hwit
  exact coeffGermLin_surjective_of_ne_zero hP (coeffGermLin_ne_zero_of_ordU_eq hP hg hord)

/-! ### The product-witness existence (the single remaining analytic obligation)

The cover-set-level input the surjectivity reduction (`coeffGermLin_surjective_of_exists_witness`)
needs: on a chart-disk cover-set `U j`, a section of `𝒪_{D+P}` of order *exactly* `−(D P)−1` at `P`.
This is the **product witness / local Mittag–Leffler** and is the genuine local-analytic core. -/

/-- **Existence of an exact-order witness on each chart-disk cover-set** — THE SINGLE REMAINING NAMED
ANALYTIC OBLIGATION of the χ-side.

For each chart-disk cover-set `U j ∋ P` and divisor `D`, there is a section `g ∈ 𝒪_{D+P}(U j)` of order
*exactly* `−(D P)−1` at `P`.

The witness is the **product** `g = (∏ᶠ u, (· − u)^{dz u}) ∘ φ` read through the *center* chart
`φ = chartAt ℂ (center j)` (`ChartDiskCover.subset_chart_source` gives `U j ⊆ φ.source`), where
`dz (φ Q) = −(D+P)(Q)` for the support points `Q ∈ supp(D+P) ∩ U j` (and `0` else).  The Mathlib
`Mathlib.Analysis.Meromorphic.FactorizedRational` API computes this:
  * `FactorizedRational.meromorphicNFOn_univ` — the product is meromorphic everywhere on `ℂ`;
  * `FactorizedRational.meromorphicOrderAt_eq` — its order at `φ Q` is exactly `dz (φ Q) = −(D+P)(Q)`.
Transferring those to `↥(U j)` is the **chart-change** at each point: `CechH0.ordU_eq_orderAt_Gext`
reads `ordU` in the ambient chart `chartAt ℂ Q`, and `meromorphicOrderAt_comp_of_deriv_ne_zero` (with
the analytic chart-transition `φ ∘ (chartAt ℂ Q).symm`, whose derivative is nonzero since it is a
biholomorphism) identifies its order there with `meromorphicOrderAt (∏ᶠ …) (φ Q)`.  Then:
  * at `P`: order `= −(D+P)(P) = −(D P)−1` (the claimed exact order);
  * at any `Q ∈ U j`: order `= −(D+P)(Q) ≥ −(D+P)(Q)`, so `g ∈ 𝒪_{D+P}(U j)`.

Isolated as a `sorry` — the only remaining χ-side gap.  The construction is standard but the full
finprod-divisor bookkeeping (`dz`, `φ`-injectivity on `U j`) plus the chart-transition `deriv ≠ 0` is a
substantial self-contained analytic development.  Everything *downstream*
(`coeffGermLin_surjective_of_exists_witness`, the cone realization, the χ-induction,
`cohomological_riemannRoch`) is proven axiom-clean. -/
theorem exists_orderExact_witness_chartDisk (D : Divisor X)
    (j : (chartDiskCover (X := X)).ι) (P : X) (hP : P ∈ (chartDiskCover (X := X)).U j) :
    ∃ g : (chartDiskCover (X := X)).U j → ℂ,
      ∃ _ : g ∈ OmegaD (D + Finsupp.single P 1) ((chartDiskCover (X := X)).U j),
      ordU g ⟨P, hP⟩ = ((-(D P) - 1 : ℤ) : WithTop ℤ) :=
  sorry

/-- **Local realizability of the canonical chart-disk cover** (the product witness / local
Mittag–Leffler).  At every chart-disk cover-set `U j ∋ P`, the order-`(−D(P)−1)` principal-part
coefficient `coeffGermLin` is surjective onto `ℂ`, for every divisor `D` — the single analytic input
the cone skyscraper construction consumes.  PROVEN from the exact-order witness
(`exists_orderExact_witness_chartDisk`) via `coeffGermLin_surjective_of_exists_witness`. -/
theorem locallyRealizable_chartDiskCover :
    (chartDiskCover (X := X)).toFiniteCover.LocallyRealizable := by
  intro D P j hP
  exact coeffGermLin_surjective_of_exists_witness hP
    (exists_orderExact_witness_chartDisk D j P hP)

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
