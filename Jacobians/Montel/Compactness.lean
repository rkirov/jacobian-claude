import Jacobians.Montel.SupNorm
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.RCLike.Real

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

/-! ### Step B.3 — `localRep` is analytic in chart coordinates

The `ContMDiff ω ⇔ AnalyticOn ℂ` bridge at bundle-section level:
`z ↦ localRep α x₀ ((chartAt ℂ x₀).symm z)` is analytic on the chart
target (an open subset of `ℂ`).

**Proof outline.**
1. `α.contMDiff_toFun` gives smoothness of α as a bundle section in the
   Hom bundle globally.
2. The constant-1 frame tangent vector
   `y ↦ TotalSpace.mk' ℂ y (e.symmL ℂ y 1)` is `ContMDiffOn ω` on
   `e.baseSet` (from `e.contMDiffOn_section_baseSet_iff`: its
   trivialization representative is the constant function `1`, which
   is smooth).
3. `ContMDiffOn.clm_bundle_apply` combines (1) and (2) to give
   smoothness of `y ↦ TotalSpace.mk' ℂ y (localRep α x₀ y)` as a
   section of the Trivial ℂ bundle.
4. `contMDiffWithinAt_section` on the Trivial bundle (whose
   trivialization projection is the identity) extracts scalar
   smoothness `ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (localRep α x₀) e.baseSet`.
5. `contMDiffOn_iff` unfolds manifold-smoothness into
   `ContDiffOn ℂ ω (f ∘ (chartAt ℂ x₀).symm)` on the chart target
   (using `extChartAt 𝓘(ℂ) = chartAt ℂ` for ℂ as its own model).
6. `contDiffOn_omega_iff_analyticOn` on the open chart target
   concludes `AnalyticOn`. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- The trivialization base set at `x₀` equals `(chartAt ℂ x₀).source`
(specialization of `TangentBundle.trivializationAt_baseSet`). -/
theorem baseSet_eq_chartAt_source (x₀ : X) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet =
      (chartAt ℂ x₀).source :=
  TangentBundle.trivializationAt_baseSet x₀

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- The constant-1 tangent-frame section
`y ↦ (trivializationAt …).symmL ℂ y 1` is smooth as a bundle section
on the trivialization's base set. Proof: via
`Trivialization.contMDiffOn_section_baseSet_iff`, equivalent to
smoothness of the trivialization representative, which equals the
constant `1 : ℂ` on the base set. -/
theorem contMDiffOn_frame
    (x₀ : X) :
    ContMDiffOn 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)) ω
      (fun y : X => TotalSpace.mk' ℂ
        (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x) y
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1))
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
  rw [(trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).contMDiffOn_section_baseSet_iff]
  have hconst : Set.EqOn
      (fun y : X =>
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀)
          ⟨y, (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1⟩).2)
      (fun _ : X => (1 : ℂ))
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
    intro y hy
    simp only
    have hsymmL :
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1 =
          (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symm y 1 := rfl
    rw [hsymmL]
    have hmk :
        (⟨y, (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symm y 1⟩ :
          TotalSpace ℂ (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x)) =
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).toOpenPartialHomeomorph.symm (y, 1) :=
      Trivialization.mk_symm _ hy 1
    rw [hmk]
    simp [(trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).apply_symm_apply' hy]
  exact contMDiffOn_const.congr hconst

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- Scalar smoothness of `localRep α x₀` as a function `X → ℂ` on the
chart source (= trivialization base set). Combines `α.contMDiff_toFun`,
`contMDiffOn_frame`, and `ContMDiffOn.clm_bundle_apply` via scalar
extraction on the Trivial bundle. -/
theorem localRep_contMDiffOn
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (localRep α x₀)
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
  have hα : ContMDiffOn 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : X => TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)
        x (α.toFun x))
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet :=
    α.contMDiff_toFun.contMDiffOn
  have happ : ContMDiffOn 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ)) ω
      (fun y : X => TotalSpace.mk' ℂ (E := Bundle.Trivial X ℂ) y (localRep α x₀ y))
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet :=
    hα.clm_bundle_apply (contMDiffOn_frame x₀)
  intro y hy
  have h := happ y hy
  rw [contMDiffWithinAt_section] at h
  have heqPt : ∀ x : X,
      ((trivializationAt ℂ (Bundle.Trivial X ℂ) y) ⟨x, localRep α x₀ x⟩).2 = localRep α x₀ x := by
    intro x
    simp [Bundle.Trivial.trivialization]
  exact h.congr (fun x _ => heqPt x) (heqPt y)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- **Step B.3 — the holomorphicity bridge.**
In chart coordinates at `x₀`, the local representative of a holomorphic
1-form α is analytic on the chart target.

Proof chain:
1. `localRep_contMDiffOn` gives `ContMDiffOn ω` on the chart source.
2. `contMDiffOn_iff` reduces this to `ContDiffOn ℂ ω` in chart
   coordinates (using that ℂ's `extChartAt` is essentially the
   identity).
3. `contDiffOn_omega_iff_analyticOn` on the open chart target
   promotes `ContDiffOn ω` ⇒ `AnalyticOn`. -/
theorem localRep_analyticOn_chartTarget
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    AnalyticOn ℂ (fun z : ℂ => localRep α x₀ ((chartAt ℂ x₀).symm z))
      (chartAt ℂ x₀).target := by
  -- Step 1: manifold smoothness on the chart source.
  have hfm : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (localRep α x₀) (chartAt ℂ x₀).source := by
    rw [← baseSet_eq_chartAt_source x₀]
    exact localRep_contMDiffOn α x₀
  -- Step 2: unfold contMDiffOn_iff to ContDiffOn ℂ ω via ℂ's identity model.
  rw [contMDiffOn_iff] at hfm
  obtain ⟨_, hf_chart⟩ := hfm
  have hCD := hf_chart x₀ (0 : ℂ)
  have h1 : (extChartAt 𝓘(ℂ, ℂ) x₀).target = (chartAt ℂ x₀).target := by simp [extChartAt]
  have h2 : (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)).source = Set.univ := by simp [extChartAt]
  have h3 : ∀ z, (extChartAt 𝓘(ℂ, ℂ) x₀).symm z = (chartAt ℂ x₀).symm z := by
    intro z; simp [extChartAt]
  have h4 : ∀ z, (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)) z = z := by intro z; simp [extChartAt]
  rw [h2, Set.preimage_univ, Set.inter_univ] at hCD
  have hset : (extChartAt 𝓘(ℂ, ℂ) x₀).target ∩
      (extChartAt 𝓘(ℂ, ℂ) x₀).symm ⁻¹' (chartAt ℂ x₀).source = (chartAt ℂ x₀).target := by
    ext z
    refine ⟨fun ⟨htgt, _⟩ => by rw [h1] at htgt; exact htgt, fun hz => ?_⟩
    refine ⟨h1 ▸ hz, ?_⟩
    simp only [Set.mem_preimage]
    rw [h3]
    exact (chartAt ℂ x₀).map_target hz
  rw [hset] at hCD
  have hfun : ((extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)) ∘ localRep α x₀ ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm) =
      (fun z : ℂ => localRep α x₀ ((chartAt ℂ x₀).symm z)) := by
    funext z
    simp [Function.comp_def]
  rw [hfun] at hCD
  -- Step 3: ContDiffOn ω ↔ AnalyticOn via UniqueDiffOn on open set.
  exact (contDiffOn_omega_iff_analyticOn (chartAt ℂ x₀).open_target.uniqueDiffOn).mp hCD

/-! ### Step B.4 — Cauchy estimate: uniform derivative bound on compacta

Pure complex analysis (no bundles). For an analytic function `f : ℂ → ℂ`
on an open set `U`, bounded by `C` on `U`, the derivative is bounded by
`L · C` on any compact `K ⊂ U`, where `L = 1/δ` and `δ > 0` is a
thickening radius with `cthickening δ K ⊆ U` (which exists by
`IsCompact.exists_cthickening_subset_open`).

The derivative bound `L` depends only on `U` and `K`, not on `f`, so
this lemma directly yields **uniform** derivative bounds for families
of analytic functions — precisely what Arzelà–Ascoli needs. -/

/-- Cauchy estimate on a compact subset of an open set: for `f`
analytic on `U` with `‖f‖ ≤ C`, `‖deriv f z‖ ≤ L · C` for all `z ∈ K`,
with `L = 1/δ` depending only on `K ⊂ U`. -/
theorem exists_cauchy_deriv_bound
    {U K : Set ℂ} (hU : IsOpen U) (hKcpt : IsCompact K) (hKU : K ⊆ U) :
    ∃ L : ℝ, 0 < L ∧ ∀ (f : ℂ → ℂ), AnalyticOn ℂ f U → ∀ C : ℝ,
      (∀ z ∈ U, ‖f z‖ ≤ C) → ∀ z ∈ K, ‖deriv f z‖ ≤ L * C := by
  obtain ⟨δ, hδpos, hδsub⟩ := hKcpt.exists_cthickening_subset_open hU hKU
  refine ⟨1 / δ, by positivity, fun f hf C hfb z hz => ?_⟩
  have hclosedBall : Metric.closedBall z δ ⊆ U := by
    have h1 : Metric.closedBall z δ ⊆ Metric.cthickening δ K := by
      intro w hw
      rw [hKcpt.cthickening_eq_biUnion_closedBall hδpos.le]
      exact Set.mem_biUnion hz hw
    exact h1.trans hδsub
  have hAnalBall : AnalyticOn ℂ f (Metric.closedBall z δ) := hf.mono hclosedBall
  have hdcoc : DiffContOnCl ℂ f (Metric.ball z δ) :=
    ⟨(hAnalBall.mono Metric.ball_subset_closedBall).differentiableOn,
     by rw [closure_ball z hδpos.ne']; exact hAnalBall.continuousOn⟩
  have hsphere : ∀ w ∈ Metric.sphere z δ, ‖f w‖ ≤ C := fun w hw =>
    hfb w (hclosedBall (Metric.sphere_subset_closedBall hw))
  have hcd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδpos hdcoc hsphere
  calc ‖deriv f z‖ ≤ C / δ := hcd
    _ = 1 / δ * C := by ring

/-! ### Next steps (scheduled, not implemented here)

**B.5** `equicontinuous_of_bounded` — combine B.3 + B.4 to get a
uniform Lipschitz bound for the family `{localRep α x₀ ∘
(chartAt …).symm : ‖α‖ ≤ M}` on a compact subset of the chart target.
Then equicontinuity follows by MVT on segments (or local Lipschitz via
ball-covering). Pure complex analysis.

**B.6** `closedBall_relativelyCompact` — Arzelà–Ascoli assembly on each
`C(shrunkChart x₀, ℂ)`, then finite product.

**B.7** `closedBall_isClosed` — via uniform limits of holomorphic
functions being holomorphic (`TendstoLocallyUniformlyOn.analyticOn`).

**Assembly** — discharge `HolomorphicOneForms.closedBall_isCompact` in
`Jacobians/Montel.lean`. -/

end Jacobians.Montel
