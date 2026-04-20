import Jacobians.Montel.SupNorm
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Montel path — compactness of the closed unit ball (work in progress)

This file is the step-B decomposition of the single content sorry
`HolomorphicOneForms.closedBall_isCompact` in `Jacobians/Montel.lean`.
The classical outline (Ahlfors–Sario Ch II §5, Rudin Ch 14) proceeds:

1. `HOF X` embeds into `Π K ∈ chartCover, C(shrunkChart K, ℂ)` via
   `localRep`, continuous-linear with operator norm `≤ 1` under
   `supNormK` thanks to `norm_localRep_le_supNormK`.
2. Image of the unit ball is bounded by definition.
3. **Cauchy estimates**: `localRep α x₀` is analytic in chart
   coordinates ⇒ derivatives are bounded on slightly smaller sets.
4. **Arzelà–Ascoli**: bounded + equicontinuous + compact base
   ⇒ closed ball image relatively compact in `C(shrunkChart K, ℂ)`.
5. **Completeness / closedness**: uniform limits of holomorphic
   sections are holomorphic (via `TendstoLocallyUniformlyOn.analyticOn`).
6. Assembly: the closed unit ball is closed (under the sup-norm) and
   its image is relatively compact, hence compact.

This file lands step 1 — the continuous-map bundling of `localRep` on
the compact shrunk chart — as clean, sorry-free API. The remaining
steps (3)–(6) are separately scheduled.
-/

namespace Jacobians.Montel

open scoped Manifold ContDiff
open Bundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Step B.1 — `localRep` as a `ContinuousMap` on the shrunk chart

For `x₀ ∈ chartCover`, `shrunkChart x₀` is a compact subset of
`(chartAt ℂ x₀).source = (trivializationAt …).baseSet`, so
`localRep α x₀` is continuous there (via `localRep_continuousOn`).
We bundle this as `C(shrunkChart x₀, ℂ)` for downstream Arzelà–Ascoli.
-/

omit [ConnectedSpace X] [Nonempty X] in
/-- `shrunkChart x₀` is contained in the trivialization base set at `x₀`,
provided `x₀ ∈ chartCover`. -/
theorem shrunkChart_subset_baseSet (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    shrunkChart (X := X) x₀ ⊆
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
  rw [TangentBundle.trivializationAt_baseSet]
  exact shrunkChart_subset_source x₀ hx₀

omit [ConnectedSpace X] [Nonempty X] in
/-- `localRep α x₀` is continuous on the compact `shrunkChart x₀` for
`x₀ ∈ chartCover`. -/
theorem localRep_continuousOn_shrunkChart
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    ContinuousOn (localRep α x₀) (shrunkChart (X := X) x₀) :=
  (localRep_continuousOn α x₀).mono (shrunkChart_subset_baseSet x₀ hx₀)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- The compact subtype `shrunkChart x₀` is a compact topological space
(automatic from `shrunkChart_isCompact`). -/
theorem shrunkChart_compactSpace (x₀ : X) :
    CompactSpace (shrunkChart (X := X) x₀) :=
  isCompact_iff_compactSpace.mp (shrunkChart_isCompact x₀)

/-- `localRep α x₀` bundled as a continuous map on the compact
`shrunkChart x₀`. Requires `x₀ ∈ chartCover` so that the shrunk chart
sits inside the trivialization base set where `localRep` is continuous.

For `x₀ ∉ chartCover`, `shrunkChart x₀ = ∅` (see `shrunkChart_eq_empty`),
so any continuous map out of it is vacuous; we still return a genuine
`C(shrunkChart x₀, ℂ)` by taking the restriction of the constant-zero
map in that case. -/
noncomputable def localRepOnShrunk
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) : C(shrunkChart (X := X) x₀, ℂ) := by
  classical
  by_cases hx₀ : x₀ ∈ (chartCover : Finset X)
  · -- `localRep α x₀` is continuous on `shrunkChart x₀` — restrict to subtype.
    exact
      { toFun := fun y => localRep α x₀ (y : X)
        continuous_toFun := by
          have h := localRep_continuousOn_shrunkChart α x₀ hx₀
          exact h.restrict }
  · exact
      { toFun := fun _ => 0
        continuous_toFun := continuous_const }

omit [ConnectedSpace X] [Nonempty X] in
/-- On the shrunk chart (for `x₀ ∈ chartCover`), `localRepOnShrunk` agrees
pointwise with `localRep`. -/
theorem localRepOnShrunk_apply
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    (y : shrunkChart (X := X) x₀) :
    localRepOnShrunk α x₀ y = localRep α x₀ (y : X) := by
  unfold localRepOnShrunk
  simp [hx₀]

/-! ### Step B.2 — pointwise norm bound on `localRepOnShrunk`

Under the `ContinuousMap.norm = sSup` identity on a compact `CompactSpace`,
the bundled form `localRepOnShrunk α x₀` has norm exactly `chartNormK α x₀`
— it bounds above by `supNormK α = ‖α‖`, establishing the component-wise
uniform bound on the image of the closed unit ball.

We avoid packaging the full product embedding `HOF X →L[ℂ] Π …` here
because the component-wise bound is what downstream Arzelà–Ascoli
actually consumes; product-norm bookkeeping adds complexity without
unlocking new content. -/

omit [ConnectedSpace X] in
/-- Component-wise bound: for `x₀ ∈ chartCover`, the bundled continuous
map `localRepOnShrunk α x₀` on the compact shrunk chart has norm ≤ the
global Montel sup-norm `supNormK α`. -/
theorem norm_localRepOnShrunk_le_supNormK
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    letI := shrunkChart_compactSpace (X := X) x₀
    ‖localRepOnShrunk α x₀‖ ≤ HolomorphicOneForms.supNormK α := by
  letI := shrunkChart_compactSpace (X := X) x₀
  -- Non-empty vs empty shrunkChart split.
  by_cases hne : Nonempty (shrunkChart (X := X) x₀)
  · haveI := hne
    refine (ContinuousMap.norm_le_of_nonempty _).mpr ?_
    intro y
    have hy : (y : X) ∈ shrunkChart (X := X) x₀ := y.2
    calc ‖localRepOnShrunk α x₀ y‖
        = ‖localRep α x₀ (y : X)‖ := by
          rw [localRepOnShrunk_apply α hx₀ y]
      _ ≤ HolomorphicOneForms.supNormK α :=
          HolomorphicOneForms.norm_localRep_le_supNormK α hx₀ hy
  · -- Empty shrunk chart ⇒ ‖·‖ = 0 ≤ supNormK α.
    rw [not_nonempty_iff] at hne
    have h0 : localRepOnShrunk α x₀ = 0 := by
      ext y
      exact (hne.false y).elim
    rw [h0, norm_zero]
    exact HolomorphicOneForms.supNormK_nonneg α

/-! ### Next steps (scheduled, not implemented here)

**B.3 — the `ContMDiff ω ⇔ AnalyticOn ℂ` bridge (BLOCKING).**
The target statement is:
  `AnalyticOn ℂ (fun z : ℂ => localRep α x₀ ((chartAt ℂ x₀).symm z))
     (chartAt ℂ x₀).target`.
This is the bundle-section-level form of the classical
`C^ω ⇔ analytic` fact for ℂ-valued maps between open ℂ sets. It is
deferred here because it is a multi-step reduction, not a one-liner,
and filing it as a sub-sorry in this file would strictly grow the
repo's overall sorry count (the existing master sorry
`HolomorphicOneForms.closedBall_isCompact` in `Jacobians/Montel.lean`
already covers this content indirectly). Candidate Mathlib lemmas to
combine, in order of use:

- `Bundle.contMDiffAt_section` — characterizes smoothness of a section
  via smoothness of its trivialization representative.
- `contMDiffAt_iff_of_mem_source` / `contMDiffWithinAt_iff` — unfolds
  `ContMDiff` on a chart via `ContDiffOn` of the chart representative.
- `ContDiffOn.analyticOn` / `ContDiffWithinAt.analyticOn` — for
  complex target, `C^ω` ⇒ analytic (the core Mathlib bridge).
- `TangentBundle.trivializationAt` and the `symmL` apparatus, plus
  `OpenPartialHomeomorph` smoothness of the chart inverse.

**B.4** `cauchy_estimate` — derivative bound for analytic functions on
a compact shrinkage. Mathlib's key lemma:
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`:
  `0 < R → DiffContOnCl ℂ f (ball c R) → (∀ z ∈ sphere c R, ‖f z‖ ≤ C)
     → ‖deriv f c‖ ≤ C / R`.
From this, derive uniform Lipschitz bounds on the pullback over a
slightly-shrunk set, uniformly in α on the closed unit ball (using B.3).

**B.5** `equicontinuous_of_bounded` — combine B.3 + B.4. Pure complex
analysis: bounded derivative ⇒ locally Lipschitz ⇒ equicontinuous on
compacta.

**B.6** `closedBall_relativelyCompact` — Arzelà–Ascoli assembly on each
`C(shrunkChart x₀, ℂ)`, then finite product.

**B.7** `closedBall_isClosed` — via uniform limits of holomorphic
functions being holomorphic (`TendstoLocallyUniformlyOn.analyticOn`).

**Assembly** — discharge `HolomorphicOneForms.closedBall_isCompact` in
`Jacobians/Montel.lean`. -/

end Jacobians.Montel
