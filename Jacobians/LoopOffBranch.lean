import Jacobians.SmoothPathCore
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Chart-local FTC for the line integral, and the off-branch-loop foundations

This module builds the **chart-local Fundamental Theorem of Calculus** for the
manifold `lineIntegral`, the genuine analytic nugget needed to discharge
`exists_loop_off_branchLocus` (sorry #6) via the *local-detour* route (Forster
§10.5, but with NO global manifold Stokes):

* `chartFrame_cancel_general` — for **any** path `γ` staying in a single chart
  source around `Q₀`, the `lineIntegral` integrand `ωᵢ(γ t)(γ'(t))` equals the
  chart-coordinate integrand
  `chartFormCoeff Q₀ i (chartₖ(γ t)) · (chartₖ ∘ γ)'(t)`.
  (The `ChartBallPath`-specific `chartFrame_cancel` in `SmoothPathCore` is the
  special case `γ = ChartBallPath`.)

* `lineIntegral_eq_primitive_diff_in_ballChart` — **chart-local FTC**: if `γ`
  stays in a *ball*-chart (target `Metric.ball c r`, hence simply connected) and
  is C¹ in chart coordinates, then
  `lineIntegral ωᵢ γ = F (chart γ(1)) − F (chart γ(0))`
  where `F` is a holomorphic **primitive** of the (holomorphic) coefficient
  `chartFormCoeff Q₀ i` on the ball (Mathlib's
  `DifferentiableOn.isExactOn_ball`, Morera). The line integral therefore depends
  only on the chart-coordinate endpoints.

* `lineIntegral_eq_of_chart_ball_endpoints` — the immediate corollary: two
  C¹ paths with **equal endpoints** inside one ball-chart have **equal**
  `lineIntegral`. (This reinstates, with the correct `ball` hypothesis, the
  `lineIntegral_eq_of_chart_local` lemma that was removed from
  `Jacobians/LineIntegral.lean` as unprovable in full generality.)

These are the local primitives for period-preservation: replacing a sub-arc of a
loop by a detour with the same endpoints inside one ball-chart does not change the
contribution to any period, because both contributions equal the same
primitive-difference. The remaining work (global subdivision, detour-off-`B`
surgery, C¹ gluing, telescoping the primitive-differences across chart overlaps)
is the assembly of `exists_loop_off_branchLocus` itself.

## References
Forster §10.5; Mathlib `Mathlib/Analysis/Complex/HasPrimitives.lean` (Morera).
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Complex Set MeasureTheory Filter

namespace Jacobians.OfCurveSkeleton

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **General chart-frame cancellation.** For any path `γ` that stays in the chart
source of `Q₀` on a neighbourhood of `t`, and is chart-pullback-differentiable at
`t`, the `lineIntegral` integrand of the `i`-th period basis form factors through
the chart `e := chartAt ℂ Q₀`:

```
ωᵢ(γ t)(pathSpeed γ t) = chartFormCoeff Q₀ i (e (γ t)) · (fderiv ℝ (e ∘ γ) t 1).
```

This is `OfCurveSkeleton.chartFrame_cancel` generalised from `ChartBallPath` to an
arbitrary path: the proof is the same chart-transition + ℂ-linearity computation,
with the `ChartBallPath`-specific `chart_ChartBallPath_eq` step replaced by the
local equality `e ∘ γ` (the chart coordinate) directly. -/
lemma chartFrame_cancel_general (Q₀ : X) (γ : ℝ → X) (i : Fin (genus X)) (t : ℝ)
    (h_source_nbhd : ∀ᶠ s : ℝ in nhds t, γ s ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t) :
    (periodBasisForm X i).toFun (γ t) (pathSpeed γ t) =
      chartFormCoeff (X := X) Q₀ i ((chartAt (H := ℂ) Q₀) (γ t))
        * (fderiv ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t 1) := by
  set e := chartAt (H := ℂ) Q₀ with he
  set w : ℂ := e (γ t) with hw
  have hγt_source : γ t ∈ e.source := h_source_nbhd.self_of_nhds
  have hγt_self_source : γ t ∈ (chartAt (H := ℂ) (γ t)).source := mem_chart_source ℂ (γ t)
  -- The chart transition `h_trans := (chartAt γt) ∘ e.symm`, holomorphic at `w`.
  set h_trans : ℂ → ℂ := fun v => (chartAt (H := ℂ) (γ t)) (e.symm v) with hh_trans
  have h_trans_diff_C : DifferentiableAt ℂ h_trans w := by
    have h_src : e.symm w ∈ (chartAt (H := ℂ) (γ t)).source := by
      rw [show e.symm w = γ t from e.left_inv hγt_source]; exact hγt_self_source
    have h_wtarget : w ∈ e.target := e.map_source hγt_source
    have h_dC := Jacobians.chart_transition_differentiableAt_C (X := X) Q₀ (γ t) w h_wtarget h_src
    have h_eq_comp : (fun v : ℂ =>
        (((e.symm ≫ₕ (chartAt (H := ℂ) (γ t))) : ℂ → ℂ)) v) =ᶠ[nhds w] h_trans := by
      have h_open : IsOpen (e.symm ≫ₕ (chartAt (H := ℂ) (γ t))).source :=
        (e.symm ≫ₕ (chartAt (H := ℂ) (γ t))).open_source
      have h_mem : w ∈ (e.symm ≫ₕ (chartAt (H := ℂ) (γ t))).source :=
        (Jacobians.chart_trans_source_iff (X := X) Q₀ (γ t) w).mpr ⟨h_wtarget, h_src⟩
      filter_upwards [h_open.mem_nhds h_mem] with v _; rfl
    exact h_dC.congr_of_eventuallyEq h_eq_comp
  have h_trans_diff_R : DifferentiableAt ℝ h_trans w :=
    @DifferentiableAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _ Jacobians.instIsScalarTower_R_C_C
      ℂ _ _ _ Jacobians.instIsScalarTower_R_C_C _ _ h_trans_diff_C
  -- `(chartAt γt) ∘ γ =ᶠ h_trans ∘ (e ∘ γ)` near `t`.
  have h_local_eq : (chartAt (H := ℂ) (γ t)).toFun ∘ γ =ᶠ[nhds t]
      h_trans ∘ (e.toFun ∘ γ) := by
    filter_upwards [h_source_nbhd] with s hs
    show (chartAt (H := ℂ) (γ t)) (γ s) = h_trans (e (γ s))
    rw [hh_trans]; simp only; rw [e.left_inv hs]
  have h_pathSpeed : pathSpeed γ t = fderiv ℝ (h_trans ∘ (e.toFun ∘ γ)) t 1 := by
    show fderiv ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t 1 = _
    rw [Filter.EventuallyEq.fderiv_eq h_local_eq]
  have h_chain : fderiv ℝ (h_trans ∘ (e.toFun ∘ γ)) t =
      (fderiv ℝ h_trans w).comp (fderiv ℝ (e.toFun ∘ γ) t) :=
    fderiv_comp t h_trans_diff_R hγ_diff
  set D : ℂ := fderiv ℝ (e.toFun ∘ γ) t 1 with hD
  have h_pathSpeed_eq : pathSpeed γ t = (fderiv ℝ h_trans w) D := by
    rw [h_pathSpeed, h_chain, ContinuousLinearMap.comp_apply]
  have h_trans_fderiv_RC : fderiv ℝ h_trans w = (fderiv ℂ h_trans w).restrictScalars ℝ := by
    have hFD_C : HasFDerivAt h_trans (fderiv ℂ h_trans w) w := h_trans_diff_C.hasFDerivAt
    have hFD_R : HasFDerivAt h_trans ((fderiv ℂ h_trans w).restrictScalars ℝ) w := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hFD_C ⊢
      simp only [ContinuousLinearMap.coe_restrictScalars']; exact hFD_C
    exact hFD_R.fderiv
  have h_pathSpeed_C : pathSpeed γ t = (fderiv ℂ h_trans w) D := by
    rw [h_pathSpeed_eq, h_trans_fderiv_RC, ContinuousLinearMap.coe_restrictScalars']
  have h_fderiv_apply : (fderiv ℂ h_trans w) D = D * (fderiv ℂ h_trans w) 1 := by
    have := (fderiv ℂ h_trans w).map_smul D (1 : ℂ)
    rw [smul_eq_mul, mul_one] at this; rw [this, smul_eq_mul]
  have h_pathSpeed_final : pathSpeed γ t = D * (fderiv ℂ h_trans w) 1 := by
    rw [h_pathSpeed_C, h_fderiv_apply]
  have h_chartFormCoeff : chartFormCoeff (X := X) Q₀ i w =
      (periodBasisForm X i).toFun (γ t) ((fderiv ℂ h_trans w) 1) := by
    unfold chartFormCoeff
    show Jacobians.Montel.localRep (periodBasisForm X i) Q₀ (e.symm w) = _
    rw [show e.symm w = γ t from e.left_inv hγt_source]
    show (periodBasisForm X i).toFun (γ t)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ (γ t) 1) = _
    rw [trivAt_symmL_one_eq_fderiv_C Q₀ (γ t) hγt_source]
    congr 1
  rw [h_chartFormCoeff, h_pathSpeed_final]
  have h_lin : ((periodBasisForm X i).toFun (γ t)) (D * (fderiv ℂ h_trans w) 1) =
        D * ((periodBasisForm X i).toFun (γ t)) ((fderiv ℂ h_trans w) 1) := by
    have := (periodBasisForm X i).toFun (γ t) |>.map_smul D ((fderiv ℂ h_trans w) 1)
    simp only [smul_eq_mul] at this; exact this
  rw [h_lin]; ring

/-- **Chart-local Fundamental Theorem of Calculus for `lineIntegral`.**

If a path `γ` stays in a **ball**-chart around `Q₀` (chart target
`Metric.ball c r`, so the chart-coordinate region is simply connected) and is
C¹ in chart coordinates on `[0,1]`, then the line integral of the `i`-th period
basis form along `γ` equals the **primitive-difference**

```
lineIntegral ωᵢ γ = F (e (γ 1)) − F (e (γ 0)),    e := chartAt ℂ Q₀,
```

where `F` is a holomorphic primitive of the (holomorphic) chart coefficient
`chartFormCoeff Q₀ i` on the ball, produced by Morera's theorem
(`DifferentiableOn.isExactOn_ball`). In particular the value depends on `γ` only
through its chart-coordinate endpoints `e (γ 0)`, `e (γ 1)`.

`hint` (interval-integrability of the line-integral integrand) is what a
`IsClosedSmoothLoop`/`IsSmoothPath` already supplies via
`intervalIntegrable_form_pathSpeed_of_velContinuous`. -/
lemma lineIntegral_eq_primitive_diff_in_ballChart
    (Q₀ : X) (γ : ℝ → X) (i : Fin (genus X)) (c : ℂ) (r : ℝ)
    (htgt : (chartAt (H := ℂ) Q₀).target = Metric.ball c r)
    (hγ_in : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t)
    (hint : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)) volume 0 1) :
    ∃ F : ℂ → ℂ,
      (∀ w ∈ Metric.ball c r, HasDerivAt F (chartFormCoeff (X := X) Q₀ i w) w) ∧
      lineIntegral (periodBasisForm X i) γ =
        F ((chartAt (H := ℂ) Q₀) (γ 1)) - F ((chartAt (H := ℂ) Q₀) (γ 0)) := by
  set e := chartAt (H := ℂ) Q₀ with he
  -- `chartFormCoeff Q₀ i` is holomorphic on the (ball) chart target ⟹ has a primitive `F`.
  have hcoeff_diffOn : DifferentiableOn ℂ (chartFormCoeff (X := X) Q₀ i) (Metric.ball c r) := by
    rw [← htgt]; exact chartFormCoeff_differentiableOn Q₀ i
  obtain ⟨F, hF⟩ := hcoeff_diffOn.isExactOn_ball
  refine ⟨F, hF, ?_⟩
  set g : ℝ → ℂ := e.toFun ∘ γ with hg
  have hg_ball : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ Metric.ball c r := by
    intro t ht; rw [hg]; show e (γ t) ∈ Metric.ball c r
    rw [← htgt]; exact e.map_source (hγ_in t ht)
  have huIcc_sub : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le (by norm_num)
  -- `F ∘ g` has derivative `coeff(g t) · g'(t)` by the chain rule.
  have hFg_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (F ∘ g) (chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1)) t := by
    intro t ht
    rw [huIcc_sub] at ht
    have hg_deriv : HasDerivAt g (fderiv ℝ g t 1) t := (hγ_diff t (huIcc_sub ▸ ht)).hasDerivAt
    have hF_at : HasDerivAt F (chartFormCoeff (X := X) Q₀ i (g t)) (g t) := hF (g t) (hg_ball t ht)
    have := hF_at.comp t hg_deriv
    convert this using 1
  unfold lineIntegral
  -- The line-integral integrand equals `coeff(g t) · g'(t)` on `[0,1]`.
  have hintegrand : Set.EqOn
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
      (fun t => chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1))
      (Set.uIcc 0 1) := by
    intro t ht
    rw [huIcc_sub] at ht
    have h_src_nbhd : ∀ᶠ s : ℝ in nhds t, γ s ∈ e.source :=
      (e.open_source.preimage hγ_cont).mem_nhds (hγ_in t ht)
    exact chartFrame_cancel_general Q₀ γ i t h_src_nbhd (hγ_diff t (huIcc_sub ▸ ht))
  rw [intervalIntegral.integral_congr hintegrand,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hFg_deriv
      (hint.congr (fun t ht => hintegrand (Set.uIoc_subset_uIcc ht)))]
  rfl

/-- **Chart-local path-independence of `lineIntegral`** (the corrected form of the
lemma removed from `Jacobians/LineIntegral.lean`). Two C¹ paths `γ₁, γ₂` that both
stay inside one **ball**-chart around `Q₀` and share endpoints
(`e (γ₁ 0) = e (γ₂ 0)` and `e (γ₁ 1) = e (γ₂ 1)`, with `e := chartAt ℂ Q₀`) have
**equal** line integrals of each period basis form. Proof: both equal the same
primitive-difference (`lineIntegral_eq_primitive_diff_in_ballChart`).

This is the local period-preservation primitive: a sub-arc and a same-endpoints
detour inside a ball-chart contribute equally to every period. -/
lemma lineIntegral_eq_of_chart_ball_endpoints
    (Q₀ : X) (γ₁ γ₂ : ℝ → X) (i : Fin (genus X)) (c : ℂ) (r : ℝ)
    (htgt : (chartAt (H := ℂ) Q₀).target = Metric.ball c r)
    (hγ₁_in : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₁ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ₂_in : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₂ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ₁_cont : Continuous γ₁) (hγ₂_cont : Continuous γ₂)
    (hγ₁_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ₁) t)
    (hγ₂_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ₂) t)
    (hint₁ : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ₁ t) (pathSpeed γ₁ t)) volume 0 1)
    (hint₂ : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ₂ t) (pathSpeed γ₂ t)) volume 0 1)
    (h0 : (chartAt (H := ℂ) Q₀) (γ₁ 0) = (chartAt (H := ℂ) Q₀) (γ₂ 0))
    (h1 : (chartAt (H := ℂ) Q₀) (γ₁ 1) = (chartAt (H := ℂ) Q₀) (γ₂ 1)) :
    lineIntegral (periodBasisForm X i) γ₁ = lineIntegral (periodBasisForm X i) γ₂ := by
  obtain ⟨F₁, hF₁, he₁⟩ :=
    lineIntegral_eq_primitive_diff_in_ballChart Q₀ γ₁ i c r htgt hγ₁_in hγ₁_cont hγ₁_diff hint₁
  obtain ⟨F₂, hF₂, he₂⟩ :=
    lineIntegral_eq_primitive_diff_in_ballChart Q₀ γ₂ i c r htgt hγ₂_in hγ₂_cont hγ₂_diff hint₂
  -- `F₁ − F₂` has zero derivative on the (open, preconnected) ball, hence is constant there;
  -- so the endpoint-differences `F₁ p1 − F₁ p0` and `F₂ p1 − F₂ p0` agree.
  set D : ℂ → ℂ := fun z => F₁ z - F₂ z with hD
  have hD_diff : DifferentiableOn ℂ D (Metric.ball c r) := fun w hw =>
    ((hF₁ w hw).sub (hF₂ w hw)).differentiableAt.differentiableWithinAt
  have hD_deriv0 : Set.EqOn (deriv D) 0 (Metric.ball c r) := by
    intro w hw
    have : HasDerivAt D 0 w := by simpa using (hF₁ w hw).sub (hF₂ w hw)
    simp [this.deriv]
  have hp0 : (chartAt (H := ℂ) Q₀) (γ₁ 0) ∈ Metric.ball c r := by
    rw [← htgt]; exact (chartAt (H := ℂ) Q₀).map_source (hγ₁_in 0 ⟨le_rfl, zero_le_one⟩)
  have hp1 : (chartAt (H := ℂ) Q₀) (γ₁ 1) ∈ Metric.ball c r := by
    rw [← htgt]; exact (chartAt (H := ℂ) Q₀).map_source (hγ₁_in 1 ⟨zero_le_one, le_rfl⟩)
  have hDeq : D ((chartAt (H := ℂ) Q₀) (γ₁ 1)) = D ((chartAt (H := ℂ) Q₀) (γ₁ 0)) :=
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
      hD_diff hD_deriv0 hp1 hp0
  rw [he₁, he₂, ← h0, ← h1]
  -- Goal: `F₁ p1 − F₁ p0 = F₂ p1 − F₂ p0`, which is `D p1 = D p0` rearranged.
  have hthis := hDeq
  simp only [hD] at hthis
  linear_combination hthis

/-! ## Sub-ball generalization (usable with `chart_restrict_to_ball`)

The two lemmas above require the chart `chartAt Q₀` to have its **entire** target equal
to a ball — which generic charts do not. The downstream subdivision machinery
(`Path.exists_ball_chart_subdivision`, built on `chart_restrict_to_ball`) instead gives a
ball `Metric.ball c r ⊆ (chartAt Q₀).target` that is a *sub-region* of the chart target,
together with the guarantee that the path stays in the restricted (smaller) source. The
following generalizations replace the `target = ball` hypothesis by `ball ⊆ target` plus an
explicit "chart-images land in the ball" hypothesis. The proofs are identical: the ball is
still the simply-connected region carrying Morera's primitive (`isExactOn_ball`); the only
change is `chartFormCoeff` is now holomorphic on the ball by `DifferentiableOn.mono` from
the full target, and chart-image confinement is supplied rather than derived from
`map_source`. -/

/-- **Chart-local FTC on a sub-ball of the chart target.** Generalizes
`lineIntegral_eq_primitive_diff_in_ballChart`: the ball `Metric.ball c r` need only be a
subset of `(chartAt Q₀).target`, with the path's chart-images supplied to lie in the ball
(`hg_ball`). The conclusion is the same primitive-difference. -/
lemma lineIntegral_eq_primitive_diff_in_subball
    (Q₀ : X) (γ : ℝ → X) (i : Fin (genus X)) (c : ℂ) (r : ℝ)
    (hsub : Metric.ball c r ⊆ (chartAt (H := ℂ) Q₀).target)
    (hg_ball : ∀ t ∈ Set.Icc (0 : ℝ) 1, (chartAt (H := ℂ) Q₀) (γ t) ∈ Metric.ball c r)
    (hγ_in : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t)
    (hint : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)) volume 0 1) :
    ∃ F : ℂ → ℂ,
      (∀ w ∈ Metric.ball c r, HasDerivAt F (chartFormCoeff (X := X) Q₀ i w) w) ∧
      lineIntegral (periodBasisForm X i) γ =
        F ((chartAt (H := ℂ) Q₀) (γ 1)) - F ((chartAt (H := ℂ) Q₀) (γ 0)) := by
  set e := chartAt (H := ℂ) Q₀ with he
  -- `chartFormCoeff Q₀ i` is holomorphic on the (sub-)ball ⟹ has a primitive `F`.
  have hcoeff_diffOn : DifferentiableOn ℂ (chartFormCoeff (X := X) Q₀ i) (Metric.ball c r) :=
    (chartFormCoeff_differentiableOn Q₀ i).mono hsub
  obtain ⟨F, hF⟩ := hcoeff_diffOn.isExactOn_ball
  refine ⟨F, hF, ?_⟩
  set g : ℝ → ℂ := e.toFun ∘ γ with hg
  have hg_ball' : ∀ t ∈ Set.Icc (0 : ℝ) 1, g t ∈ Metric.ball c r := hg_ball
  have huIcc_sub : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le (by norm_num)
  -- `F ∘ g` has derivative `coeff(g t) · g'(t)` by the chain rule.
  have hFg_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (F ∘ g) (chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1)) t := by
    intro t ht
    rw [huIcc_sub] at ht
    have hg_deriv : HasDerivAt g (fderiv ℝ g t 1) t := (hγ_diff t (huIcc_sub ▸ ht)).hasDerivAt
    have hF_at : HasDerivAt F (chartFormCoeff (X := X) Q₀ i (g t)) (g t) := hF (g t) (hg_ball' t ht)
    have := hF_at.comp t hg_deriv
    convert this using 1
  unfold lineIntegral
  -- The line-integral integrand equals `coeff(g t) · g'(t)` on `[0,1]`.
  have hintegrand : Set.EqOn
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
      (fun t => chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1))
      (Set.uIcc 0 1) := by
    intro t ht
    rw [huIcc_sub] at ht
    have h_src_nbhd : ∀ᶠ s : ℝ in nhds t, γ s ∈ e.source :=
      (e.open_source.preimage hγ_cont).mem_nhds (hγ_in t ht)
    exact chartFrame_cancel_general Q₀ γ i t h_src_nbhd (hγ_diff t (huIcc_sub ▸ ht))
  rw [intervalIntegral.integral_congr hintegrand,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hFg_deriv
      (hint.congr (fun t ht => hintegrand (Set.uIoc_subset_uIcc ht)))]
  rfl

/-- **Chart-local path-independence on a sub-ball of the chart target.** Generalizes
`lineIntegral_eq_of_chart_ball_endpoints`: two C¹ paths `γ₁, γ₂` whose chart-images lie in a
common ball `Metric.ball c r ⊆ (chartAt Q₀).target` and share chart-coordinate endpoints have
equal line integrals. This is the form directly usable from the subdivision machinery, where
the relevant ball is the `chart_restrict_to_ball` ball sitting inside the chart target. -/
lemma lineIntegral_eq_of_chart_subball_endpoints
    (Q₀ : X) (γ₁ γ₂ : ℝ → X) (i : Fin (genus X)) (c : ℂ) (r : ℝ)
    (hsub : Metric.ball c r ⊆ (chartAt (H := ℂ) Q₀).target)
    (hg₁_ball : ∀ t ∈ Set.Icc (0 : ℝ) 1, (chartAt (H := ℂ) Q₀) (γ₁ t) ∈ Metric.ball c r)
    (hg₂_ball : ∀ t ∈ Set.Icc (0 : ℝ) 1, (chartAt (H := ℂ) Q₀) (γ₂ t) ∈ Metric.ball c r)
    (hγ₁_in : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₁ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ₂_in : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ₂ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ₁_cont : Continuous γ₁) (hγ₂_cont : Continuous γ₂)
    (hγ₁_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ₁) t)
    (hγ₂_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ₂) t)
    (hint₁ : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ₁ t) (pathSpeed γ₁ t)) volume 0 1)
    (hint₂ : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ₂ t) (pathSpeed γ₂ t)) volume 0 1)
    (h0 : (chartAt (H := ℂ) Q₀) (γ₁ 0) = (chartAt (H := ℂ) Q₀) (γ₂ 0))
    (h1 : (chartAt (H := ℂ) Q₀) (γ₁ 1) = (chartAt (H := ℂ) Q₀) (γ₂ 1)) :
    lineIntegral (periodBasisForm X i) γ₁ = lineIntegral (periodBasisForm X i) γ₂ := by
  obtain ⟨F₁, hF₁, he₁⟩ :=
    lineIntegral_eq_primitive_diff_in_subball Q₀ γ₁ i c r hsub hg₁_ball hγ₁_in hγ₁_cont hγ₁_diff hint₁
  obtain ⟨F₂, hF₂, he₂⟩ :=
    lineIntegral_eq_primitive_diff_in_subball Q₀ γ₂ i c r hsub hg₂_ball hγ₂_in hγ₂_cont hγ₂_diff hint₂
  set D : ℂ → ℂ := fun z => F₁ z - F₂ z with hD
  have hD_diff : DifferentiableOn ℂ D (Metric.ball c r) := fun w hw =>
    ((hF₁ w hw).sub (hF₂ w hw)).differentiableAt.differentiableWithinAt
  have hD_deriv0 : Set.EqOn (deriv D) 0 (Metric.ball c r) := by
    intro w hw
    have : HasDerivAt D 0 w := by simpa using (hF₁ w hw).sub (hF₂ w hw)
    simp [this.deriv]
  have hp0 : (chartAt (H := ℂ) Q₀) (γ₁ 0) ∈ Metric.ball c r := hg₁_ball 0 ⟨le_rfl, zero_le_one⟩
  have hp1 : (chartAt (H := ℂ) Q₀) (γ₁ 1) ∈ Metric.ball c r := hg₁_ball 1 ⟨zero_le_one, le_rfl⟩
  have hDeq : D ((chartAt (H := ℂ) Q₀) (γ₁ 1)) = D ((chartAt (H := ℂ) Q₀) (γ₁ 0)) :=
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
      hD_diff hD_deriv0 hp1 hp0
  rw [he₁, he₂, ← h0, ← h1]
  have hthis := hDeq
  simp only [hD] at hthis
  linear_combination hthis

/-! ## Sub-interval primitive-difference (telescoping primitive)

The lemmas above integrate over the *full* interval `[0,1]` (i.e. over `lineIntegral`). For the
global off-branch assembly we instead need the **partial** line integral over a sub-interval
`[a,b] ⊆ [0,1]` of a loop: when the sub-arc `γ([a,b])` lies in a sub-ball of one chart, the
partial integral `∫ t in a..b, ωᵢ(γ t)(γ'(t))` equals the primitive-difference
`F(chart γ(b)) − F(chart γ(a))`, hence depends on `γ` only through its chart-coordinate values at
`a` and `b`. This is the "splice" primitive: replacing a sub-arc of a loop by a same-chart-endpoints
detour over the SAME parameter sub-interval leaves the partial integral — and therefore (by
additivity over the subdivision) the whole `periodVec` — unchanged, with NO reparametrization. -/

/-- **Sub-interval primitive-difference.** The partial line-integral integrand of `ωᵢ` over a
sub-interval `[a,b]` of a path `γ` whose sub-arc lies in a sub-ball `Metric.ball c r ⊆ chart
target`, integrates to `F(chart γ b) − F(chart γ a)` for the Morera primitive `F`. Hence the
partial integral depends only on the chart-coordinate endpoints `chart γ a`, `chart γ b`. -/
lemma intervalIntegral_form_pathSpeed_eq_primitive_diff_in_subball
    (Q₀ : X) (γ : ℝ → X) (i : Fin (genus X)) (c : ℂ) (r : ℝ) (a b : ℝ)
    (hsub : Metric.ball c r ⊆ (chartAt (H := ℂ) Q₀).target)
    (hg_ball : ∀ t ∈ Set.uIcc a b, (chartAt (H := ℂ) Q₀) (γ t) ∈ Metric.ball c r)
    (hγ_in : ∀ t ∈ Set.uIcc a b, γ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ) t)
    (hint : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)) volume a b) :
    ∃ F : ℂ → ℂ,
      (∀ w ∈ Metric.ball c r, HasDerivAt F (chartFormCoeff (X := X) Q₀ i w) w) ∧
      (∫ t in a..b, (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)) =
        F ((chartAt (H := ℂ) Q₀) (γ b)) - F ((chartAt (H := ℂ) Q₀) (γ a)) := by
  set e := chartAt (H := ℂ) Q₀ with he
  have hcoeff_diffOn : DifferentiableOn ℂ (chartFormCoeff (X := X) Q₀ i) (Metric.ball c r) :=
    (chartFormCoeff_differentiableOn Q₀ i).mono hsub
  obtain ⟨F, hF⟩ := hcoeff_diffOn.isExactOn_ball
  refine ⟨F, hF, ?_⟩
  set g : ℝ → ℂ := e.toFun ∘ γ with hg
  have hg_ball' : ∀ t ∈ Set.uIcc a b, g t ∈ Metric.ball c r := hg_ball
  -- `F ∘ g` has derivative `coeff(g t) · g'(t)` by the chain rule on `uIcc a b`.
  have hFg_deriv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (F ∘ g) (chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1)) t := by
    intro t ht
    have hg_deriv : HasDerivAt g (fderiv ℝ g t 1) t := (hγ_diff t ht).hasDerivAt
    have hF_at : HasDerivAt F (chartFormCoeff (X := X) Q₀ i (g t)) (g t) := hF (g t) (hg_ball' t ht)
    have := hF_at.comp t hg_deriv
    convert this using 1
  -- The line-integral integrand equals `coeff(g t) · g'(t)` on `uIcc a b`.
  have hintegrand : Set.EqOn
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
      (fun t => chartFormCoeff (X := X) Q₀ i (g t) * (fderiv ℝ g t 1))
      (Set.uIcc a b) := by
    intro t ht
    have h_src_nbhd : ∀ᶠ s : ℝ in nhds t, γ s ∈ e.source :=
      (e.open_source.preimage hγ_cont).mem_nhds (hγ_in t ht)
    exact chartFrame_cancel_general Q₀ γ i t h_src_nbhd (hγ_diff t ht)
  rw [intervalIntegral.integral_congr hintegrand,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hFg_deriv
      (hint.congr (fun t ht => hintegrand (Set.uIoc_subset_uIcc ht)))]
  rfl

/-- **Sub-interval splice.** Two paths `γ₁, γ₂` whose sub-arcs over `[a,b]` lie in a common
sub-ball and share chart-coordinate endpoints (`chart γ₁ a = chart γ₂ a`, `chart γ₁ b = chart γ₂ b`)
have equal partial line integrals over `[a,b]`. This is the telescoping step: it lets a bad sub-arc
be replaced by a same-chart-endpoints detour over the SAME `[a,b]` without changing the integral. -/
lemma intervalIntegral_form_pathSpeed_eq_of_subball_endpoints
    (Q₀ : X) (γ₁ γ₂ : ℝ → X) (i : Fin (genus X)) (c : ℂ) (r : ℝ) (a b : ℝ)
    (hsub : Metric.ball c r ⊆ (chartAt (H := ℂ) Q₀).target)
    (hg₁_ball : ∀ t ∈ Set.uIcc a b, (chartAt (H := ℂ) Q₀) (γ₁ t) ∈ Metric.ball c r)
    (hg₂_ball : ∀ t ∈ Set.uIcc a b, (chartAt (H := ℂ) Q₀) (γ₂ t) ∈ Metric.ball c r)
    (hγ₁_in : ∀ t ∈ Set.uIcc a b, γ₁ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ₂_in : ∀ t ∈ Set.uIcc a b, γ₂ t ∈ (chartAt (H := ℂ) Q₀).source)
    (hγ₁_cont : Continuous γ₁) (hγ₂_cont : Continuous γ₂)
    (hγ₁_diff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ₁) t)
    (hγ₂_diff : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ ((chartAt (H := ℂ) Q₀).toFun ∘ γ₂) t)
    (hint₁ : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ₁ t) (pathSpeed γ₁ t)) volume a b)
    (hint₂ : IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ₂ t) (pathSpeed γ₂ t)) volume a b)
    (h0 : (chartAt (H := ℂ) Q₀) (γ₁ a) = (chartAt (H := ℂ) Q₀) (γ₂ a))
    (h1 : (chartAt (H := ℂ) Q₀) (γ₁ b) = (chartAt (H := ℂ) Q₀) (γ₂ b)) :
    (∫ t in a..b, (periodBasisForm X i).toFun (γ₁ t) (pathSpeed γ₁ t)) =
      (∫ t in a..b, (periodBasisForm X i).toFun (γ₂ t) (pathSpeed γ₂ t)) := by
  obtain ⟨F₁, hF₁, he₁⟩ :=
    intervalIntegral_form_pathSpeed_eq_primitive_diff_in_subball Q₀ γ₁ i c r a b hsub hg₁_ball
      hγ₁_in hγ₁_cont hγ₁_diff hint₁
  obtain ⟨F₂, hF₂, he₂⟩ :=
    intervalIntegral_form_pathSpeed_eq_primitive_diff_in_subball Q₀ γ₂ i c r a b hsub hg₂_ball
      hγ₂_in hγ₂_cont hγ₂_diff hint₂
  set D : ℂ → ℂ := fun z => F₁ z - F₂ z with hD
  have hD_diff : DifferentiableOn ℂ D (Metric.ball c r) := fun w hw =>
    ((hF₁ w hw).sub (hF₂ w hw)).differentiableAt.differentiableWithinAt
  have hD_deriv0 : Set.EqOn (deriv D) 0 (Metric.ball c r) := by
    intro w hw
    have : HasDerivAt D 0 w := by simpa using (hF₁ w hw).sub (hF₂ w hw)
    simp [this.deriv]
  have hp0 : (chartAt (H := ℂ) Q₀) (γ₁ a) ∈ Metric.ball c r := hg₁_ball a Set.left_mem_uIcc
  have hp1 : (chartAt (H := ℂ) Q₀) (γ₁ b) ∈ Metric.ball c r := hg₁_ball b Set.right_mem_uIcc
  have hDeq : D ((chartAt (H := ℂ) Q₀) (γ₁ b)) = D ((chartAt (H := ℂ) Q₀) (γ₁ a)) :=
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c r).isPreconnected
      hD_diff hD_deriv0 hp1 hp0
  rw [he₁, he₂, ← h0, ← h1]
  have hthis := hDeq
  simp only [hD] at hthis
  linear_combination hthis

/-! ## §off-branch surgery — foundational pieces (Layer A)

The remaining geometric construction for `exists_splicedLoop_off_branchLocus` is assembled here as
reusable sub-lemmas, then wired together in `Jacobians/TracePullback.lean`.

### A1. Flat seam velocities of `ChartBallPathSmooth`

Every detour piece is a `ChartBallPathSmooth` (a `ChartBallPath` reparametrized by `smoothStep01`).
Because `smoothStep01` has vanishing derivative at `0` and `1`, the pathSpeed of any such piece
vanishes at its own endpoints. This is exactly the `pathSpeed γ 1 = 0` / `pathSpeed γ 0 = 0`
hypothesis that `IsSmoothPath.concat` needs at each seam, so n-fold concatenation of these pieces is
automatically C¹ with NO velocity-matching. -/

/-- **Seam velocity of `ChartBallPathSmooth` vanishes at `t = 0`.** Via the smoothStep chain rule
(`pathSpeed_smoothStep01_comp_eq`) and `smoothStep01_deriv 0 = 0`. The chart-pullback
differentiability of the underlying `ChartBallPath` at `smoothStep01 0 = 0` is supplied by
`ChartBallPath_chart_at_self_differentiableAt`. -/
lemma pathSpeed_ChartBallPathSmooth_zero (Q₀ Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.pathSpeed (Jacobians.ChartBallPathSmooth Q₀ Q) 0 = 0 := by
  have hdiff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (Jacobians.ChartBallPath Q₀ Q₀ Q (Jacobians.smoothStep01 0))).toFun ∘
        Jacobians.ChartBallPath Q₀ Q₀ Q) (Jacobians.smoothStep01 0) :=
    Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q (Jacobians.smoothStep01 0)
      (h_chart_ball _ (Jacobians.smoothStep01_mem_unit 0))
  have h := pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath Q₀ Q₀ Q) 0 hdiff
  show Jacobians.pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q ∘ Jacobians.smoothStep01) 0 = 0
  rw [h, Jacobians.smoothStep01_deriv_zero]; simp

/-- **Seam velocity of `ChartBallPathSmooth` vanishes at `t = 1`.** Same as the `t = 0` case, with
`smoothStep01 1 = 1` and `smoothStep01_deriv 1 = 0`. -/
lemma pathSpeed_ChartBallPathSmooth_one (Q₀ Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.pathSpeed (Jacobians.ChartBallPathSmooth Q₀ Q) 1 = 0 := by
  have hdiff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (Jacobians.ChartBallPath Q₀ Q₀ Q (Jacobians.smoothStep01 1))).toFun ∘
        Jacobians.ChartBallPath Q₀ Q₀ Q) (Jacobians.smoothStep01 1) :=
    Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q (Jacobians.smoothStep01 1)
      (h_chart_ball _ (Jacobians.smoothStep01_mem_unit 1))
  have h := pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath Q₀ Q₀ Q) 1 hdiff
  show Jacobians.pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q ∘ Jacobians.smoothStep01) 1 = 0
  rw [h, Jacobians.smoothStep01_deriv_one]; simp

/-! ### A2. Planar two-segment dodge in ℂ

The geometric heart of the off-branch detour: given a finite set `B ⊆ ℂ` (the chart-coordinate
image of the branch locus), an open ball `Metric.ball c r`, and two points `p, q` in the ball off
`B`, there is a relay point `m` in the ball such that both segments `[p,m]` and `[m,q]` stay in the
ball and avoid `B`. This is the convex/ball-confined analogue of Mathlib's
`Set.Countable.isPathConnected_compl_of_one_lt_rank` (whose proof is the same two-segment dodge),
specialized so the relay stays inside a prescribed ball. The detour `p → m → q` is then pulled back
through the chart and reparametrized (smoothStep) to give a flat-ended off-branch chart path. -/

/-- A neighborhood of `0` in the relay parameter keeps `c + t·y` inside the ball. -/
private lemma eventually_relay_mem_ball (c : ℂ) (r : ℝ) (hr : 0 < r) (y : ℂ) :
    ∀ᶠ t : ℝ in nhds 0, c + (t : ℂ) * y ∈ Metric.ball c r := by
  have hcont : Continuous (fun t : ℝ => c + (t : ℂ) * y) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have h0 : Filter.Tendsto (fun t : ℝ => c + (t : ℂ) * y) (nhds 0) (nhds c) := by
    simpa using hcont.tendsto 0
  exact h0.eventually_mem (Metric.ball_mem_nhds c hr)

/-- **Two-segment planar dodge, ball-confined.** For a finite `B ⊆ ℂ`, an open ball and two points
`p, q` of the ball off `B`, a relay `m` in the ball exists with `[p,m]` and `[m,q]` inside the ball
and disjoint from `B`.

The argument is the ball-confined version of Mathlib's
`Set.Countable.isPathConnected_compl_of_one_lt_rank`: writing `p = cm - x`, `q = cm + x` with `cm`
the midpoint, pick a relay direction `y` linearly independent from `x`; the pencils of segments from
`p` (resp. `q`) to `cm + t·y` are pairwise disjoint off their common vertex, so only countably many
`t` let a segment meet the (countable) `B`. The midpoint `cm` lies in the convex ball, so a whole
neighborhood of `t = 0` keeps `cm + t·y` in the ball; intersecting with the cofinite good set (dense
complement) yields a valid `t`. -/
lemma exists_relay_dodge_finite (B : Set ℂ) (hB : B.Finite) (c : ℂ) (r : ℝ)
    (p q : ℂ) (hp : p ∈ Metric.ball c r) (hq : q ∈ Metric.ball c r)
    (hpB : p ∉ B) (hqB : q ∉ B) :
    ∃ m ∈ Metric.ball c r,
      segment ℝ p m ⊆ Metric.ball c r ∧ segment ℝ m q ⊆ Metric.ball c r ∧
      Disjoint (segment ℝ p m) B ∧ Disjoint (segment ℝ m q) B := by
  classical
  have hBc : B.Countable := hB.countable
  have hr : 0 < r := Metric.pos_of_mem_ball hp
  -- Midpoint / half-difference decomposition: p = cm - x, q = cm + x.
  set cm : ℂ := (2 : ℝ)⁻¹ • (p + q) with hcm
  set x : ℂ := (2 : ℝ)⁻¹ • (q - p) with hx
  have Ip : cm - x = p := by simp only [hcm, hx]; module
  have Iq : cm + x = q := by simp only [hcm, hx]; module
  have hcm_ball : cm ∈ Metric.ball c r := by
    have hmid : cm ∈ segment ℝ p q :=
      ⟨(2:ℝ)⁻¹, (2:ℝ)⁻¹, by norm_num, by norm_num, by norm_num, by rw [hcm]; module⟩
    exact (convex_ball c r).segment_subset hp hq hmid
  -- Relay direction `y` linearly independent from `x`; if `x = 0` then `p = q`, handle separately.
  rcases eq_or_ne x 0 with hx0 | hxne
  · -- p = q: relay m = p works with degenerate segments.
    have hpq : p = q := by rw [← Ip, ← Iq, hx0]; ring
    refine ⟨p, hp, ?_, ?_, ?_, ?_⟩
    · rw [show segment ℝ p p = {p} from segment_same ℝ p]; exact Set.singleton_subset_iff.2 hp
    · rw [← hpq, show segment ℝ p p = {p} from segment_same ℝ p]
      exact Set.singleton_subset_iff.2 hp
    · rw [show segment ℝ p p = {p} from segment_same ℝ p]; exact Set.disjoint_singleton_left.2 hpB
    · rw [← hpq, show segment ℝ p p = {p} from segment_same ℝ p]
      exact Set.disjoint_singleton_left.2 hpB
  · obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![x, y] :=
      exists_linearIndependent_pair_of_one_lt_rank
        (by rw [Complex.rank_real_complex]; exact_mod_cast one_lt_two) hxne
    -- bad-t for the q-vertex (q = cm + x) and p-vertex (p = cm - x).
    have A : Set.Countable {t : ℝ | (segment ℝ q (cm + t • y) ∩ B).Nonempty} := by
      apply countable_setOf_nonempty_of_disjoint _ (fun t => Set.inter_subset_right) hBc
      intro t t' htt'
      apply Set.disjoint_iff_inter_eq_empty.2
      have N : {cm + x} ∩ B = ∅ := by
        rw [Set.singleton_inter_eq_empty]; rw [Iq]; exact hqB
      have hseg : ∀ s : ℝ, segment ℝ q (cm + s • y) = segment ℝ (cm + x) (cm + s • y) := by
        intro s; rw [Iq]
      simp only [hseg t, hseg t']
      rw [Set.inter_assoc, Set.inter_comm B, Set.inter_assoc, Set.inter_self,
        ← Set.inter_assoc, ← Set.subset_empty_iff, ← N]
      apply Set.inter_subset_inter_left
      exact Eq.subset (segment_inter_eq_endpoint_of_linearIndependent_of_ne hy htt'.symm cm)
    have Bc : Set.Countable {t : ℝ | (segment ℝ p (cm + t • y) ∩ B).Nonempty} := by
      apply countable_setOf_nonempty_of_disjoint _ (fun t => Set.inter_subset_right) hBc
      intro t t' htt'
      apply Set.disjoint_iff_inter_eq_empty.2
      have N : {cm - x} ∩ B = ∅ := by
        rw [Set.singleton_inter_eq_empty]; rw [Ip]; exact hpB
      have hseg : ∀ s : ℝ, segment ℝ p (cm + s • y) = segment ℝ (cm + -x) (cm + s • y) := by
        intro s; rw [show cm + -x = p by rw [← Ip]; ring]
      simp only [hseg t, hseg t']
      rw [Set.inter_assoc, Set.inter_comm B, Set.inter_assoc, Set.inter_self,
        ← Set.inter_assoc, ← Set.subset_empty_iff, ← N]
      apply Set.inter_subset_inter_left
      rw [show cm - x = cm + -x by ring]
      refine Eq.subset (segment_inter_eq_endpoint_of_linearIndependent_of_ne ?_ htt'.symm cm)
      have := hy.units_smul ![(-1 : ℝˣ), 1]
      simpa [← List.ofFn_inj, Matrix.cons_val_zero, Matrix.cons_val_one] using this
    -- good relay parameters: cofinite (off both bad sets) ∩ keeps cm+t•y in the ball.
    have hgood : Set.Nonempty (({t : ℝ | (segment ℝ q (cm + t • y) ∩ B).Nonempty} ∪
        {t : ℝ | (segment ℝ p (cm + t • y) ∩ B).Nonempty})ᶜ ∩
        {t : ℝ | cm + t • y ∈ Metric.ball c r}) := by
      have hUnhds : {t : ℝ | cm + t • y ∈ Metric.ball c r} ∈ nhds (0 : ℝ) := by
        have hcont : Continuous (fun t : ℝ => cm + t • y) := by
          have : (fun t : ℝ => cm + t • y) = fun t : ℝ => cm + (t : ℂ) * y := by
            funext t; rw [Complex.real_smul]
          rw [this]
          exact continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        have h0 : Filter.Tendsto (fun t : ℝ => cm + t • y) (nhds 0) (nhds cm) := by
          simpa using hcont.tendsto 0
        exact h0.eventually_mem (Metric.isOpen_ball.mem_nhds hcm_ball)
      have hdense : Dense (({t : ℝ | (segment ℝ q (cm + t • y) ∩ B).Nonempty} ∪
          {t : ℝ | (segment ℝ p (cm + t • y) ∩ B).Nonempty})ᶜ) :=
        Set.Countable.dense_compl ℝ (A.union Bc)
      exact hdense.inter_nhds_nonempty hUnhds
    obtain ⟨t, ht_good, ht_ball⟩ := hgood
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or,
      Set.not_nonempty_iff_eq_empty] at ht_good
    refine ⟨cm + t • y, ht_ball, ?_, ?_, ?_, ?_⟩
    · exact (convex_ball c r).segment_subset hp ht_ball
    · exact (convex_ball c r).segment_subset ht_ball hq
    · rw [Set.disjoint_iff_inter_eq_empty]; exact ht_good.2
    · rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm]
      rw [show segment ℝ (cm + t • y) q = segment ℝ q (cm + t • y) from segment_symm _ _ _]
      rw [Set.inter_comm B]; exact ht_good.1

/-! ### A3. General-anchor flat-ended chart path

`ChartBallPathSmooth` (in `SmoothPath.lean`) is anchored at its own start point. For the off-branch
detour we need a flat-ended chart path between two arbitrary points `P, Q` measured in a *third*
anchor's chart `chartAt w` (the common cover anchor of the piece), so that all pieces of `δ'` over
one sub-interval share the chart frame the splice lemma needs. We build it as `ChartBallPath w P Q ∘
smoothStep01` and prove `IsSmoothPath P Q` for it. Every building block already exists for a general
anchor (the `_self` in `ChartBallPath_chart_at_self_differentiableAt` refers to the *moving* frame
`chartAt (γ t)`, not the anchor), so this is the self-anchored `isSmoothPath_ChartBallPathSmooth`
argument with `chartAt w P`, `chartAt w Q` in place of `chartAt Q₀ Q₀`, `chartAt Q₀ Q`. -/

/-- Flat-ended chart-linear path `P → Q` in the chart at anchor `w` (smoothStep-reparametrized so
both endpoint velocities vanish). -/
noncomputable def ChartBallPathSmooth3 (w P Q : X) : ℝ → X :=
  fun t => Jacobians.ChartBallPath w P Q (Jacobians.smoothStep01 t)

/-- `ChartBallPathSmooth3 w P Q 0 = P` when `P` is in the anchor chart's source. -/
@[simp] lemma ChartBallPathSmooth3_zero (w P Q : X) (hP : P ∈ (chartAt (H := ℂ) w).source) :
    ChartBallPathSmooth3 w P Q 0 = P := by
  unfold ChartBallPathSmooth3
  rw [Jacobians.smoothStep01_zero]; exact Jacobians.ChartBallPath.start w P Q hP

/-- `ChartBallPathSmooth3 w P Q 1 = Q` when `Q` is in the anchor chart's source. -/
@[simp] lemma ChartBallPathSmooth3_one (w P Q : X) (hQ : Q ∈ (chartAt (H := ℂ) w).source) :
    ChartBallPathSmooth3 w P Q 1 = Q := by
  unfold ChartBallPathSmooth3
  rw [Jacobians.smoothStep01_one]; exact Jacobians.ChartBallPath.finish w P Q hQ

/-- The chart-`w` pullback of `ChartBallPathSmooth3 w P Q` is the affine interpolation
reparametrized by `smoothStep01` — used to read off the chart-coordinate endpoints for the splice. -/
lemma chart_ChartBallPathSmooth3_eq (w P Q : X) (t : ℝ)
    (h_in_target : ((1 - (Jacobians.smoothStep01 t : ℂ)) * (chartAt (H := ℂ) w) P +
      (Jacobians.smoothStep01 t : ℂ) * (chartAt (H := ℂ) w) Q) ∈ (chartAt (H := ℂ) w).target) :
    (chartAt (H := ℂ) w) (ChartBallPathSmooth3 w P Q t) =
      (1 - (Jacobians.smoothStep01 t : ℂ)) * (chartAt (H := ℂ) w) P +
        (Jacobians.smoothStep01 t : ℂ) * (chartAt (H := ℂ) w) Q := by
  unfold ChartBallPathSmooth3
  exact Jacobians.chart_ChartBallPath_eq w P Q (Jacobians.smoothStep01 t) h_in_target

/-- `ChartBallPathSmooth3 w P Q` stays in the anchor chart source on `[0,1]` under the chart-ball
hypothesis. -/
lemma ChartBallPathSmooth3_mem_source (w P Q : X) (t : ℝ)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    ChartBallPathSmooth3 w P Q t ∈ (chartAt (H := ℂ) w).source := by
  unfold ChartBallPathSmooth3
  exact Jacobians.ChartBallPath_mem_source w P Q (Jacobians.smoothStep01 t)
    (h_chart_ball _ (Jacobians.smoothStep01_mem_unit t))

/-- Continuity of `ChartBallPathSmooth3 w P Q` under the chart-ball hypothesis on `[0,1]`. -/
lemma ChartBallPathSmooth3_continuous (w P Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    Continuous (ChartBallPathSmooth3 w P Q) := by
  unfold ChartBallPathSmooth3
  refine (Jacobians.ChartBallPath_continuousOn_target_set w P Q (Set.Icc 0 1) ?_).comp_continuous
    Jacobians.smoothStep01_continuous (fun t => Jacobians.smoothStep01_mem_unit t)
  intro s hs; exact h_chart_ball s hs

/-- Moving-frame chart-pullback differentiability of `ChartBallPathSmooth3` (the `IsSmoothPath.diff`
field). Chain rule on `(general-anchor ChartBallPath chart-pullback) ∘ smoothStep01`. -/
lemma ChartBallPathSmooth3_chart_at_differentiableAt (w P Q : X) (t : ℝ)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    DifferentiableAt ℝ
      ((chartAt (H := ℂ) (ChartBallPathSmooth3 w P Q t)).toFun ∘ ChartBallPathSmooth3 w P Q) t := by
  have h_at : ((1 - (Jacobians.smoothStep01 t : ℂ)) * (chartAt (H := ℂ) w) P +
      (Jacobians.smoothStep01 t : ℂ) * (chartAt (H := ℂ) w) Q) ∈ (chartAt (H := ℂ) w).target :=
    h_chart_ball _ (Jacobians.smoothStep01_mem_unit t)
  have h_inner : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (Jacobians.ChartBallPath w P Q (Jacobians.smoothStep01 t))).toFun ∘
        Jacobians.ChartBallPath w P Q) (Jacobians.smoothStep01 t) :=
    Jacobians.ChartBallPath_chart_at_self_differentiableAt w P Q (Jacobians.smoothStep01 t) h_at
  have h_eq : ((chartAt (H := ℂ) (ChartBallPathSmooth3 w P Q t)).toFun ∘ ChartBallPathSmooth3 w P Q) =
      ((chartAt (H := ℂ) (Jacobians.ChartBallPath w P Q (Jacobians.smoothStep01 t))).toFun ∘
        Jacobians.ChartBallPath w P Q) ∘ Jacobians.smoothStep01 := by
    funext s; rfl
  rw [h_eq]
  exact h_inner.comp t (Jacobians.smoothStep01_differentiable t)

/-- Velocity-section continuity of `ChartBallPathSmooth3` (the `IsSmoothPath.velCont` field). The
path is `(chartAt w).symm ∘ β` with `β` the smoothStep-reparametrized affine chart-coord curve;
push the model-space velocity continuity through the holomorphic chart inverse via
`velCont_compOn`. -/
lemma ChartBallPathSmooth3_velCont (w P Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    ContinuousOn (fun s : ℝ =>
        Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X))
          (ChartBallPathSmooth3 w P Q s) (Jacobians.pathSpeed (ChartBallPathSmooth3 w P Q) s))
      (Set.Icc 0 1) := by
  set z₀ : ℂ := (chartAt (H := ℂ) w) P with hz₀
  set z : ℂ := (chartAt (H := ℂ) w) Q with hz
  set β : ℝ → ℂ := fun t : ℝ =>
    (1 - (Jacobians.smoothStep01 t : ℂ)) * z₀ + (Jacobians.smoothStep01 t : ℂ) * z with hβ
  have hβcont : Continuous β := by
    refine Continuous.add ?_ ?_
    · exact (continuous_const.sub
        (Complex.continuous_ofReal.comp Jacobians.smoothStep01_continuous)).mul continuous_const
    · exact (Complex.continuous_ofReal.comp Jacobians.smoothStep01_continuous).mul continuous_const
  have hβderiv_eq : deriv β = fun t : ℝ => (Jacobians.smoothStep01_deriv t : ℂ) * (z - z₀) := by
    funext t
    have hσ : HasDerivAt (fun s : ℝ => (Jacobians.smoothStep01 s : ℂ))
        (Jacobians.smoothStep01_deriv t : ℂ) t :=
      (Jacobians.smoothStep01_hasDerivAt_explicit t).ofReal_comp
    have hβhd : HasDerivAt β ((Jacobians.smoothStep01_deriv t : ℂ) * (z - z₀)) t := by
      have h1 : HasDerivAt (fun s : ℝ => (1 - (Jacobians.smoothStep01 s : ℂ)) * z₀)
          (-(Jacobians.smoothStep01_deriv t : ℂ) * z₀) t := by
        simpa using (hσ.const_sub 1).mul_const z₀
      have h2 : HasDerivAt (fun s : ℝ => (Jacobians.smoothStep01 s : ℂ) * z)
          ((Jacobians.smoothStep01_deriv t : ℂ) * z) t := hσ.mul_const z
      have hsum := h1.add h2
      convert hsum using 1; ring
    exact hβhd.deriv
  have hβ' : Continuous (deriv β) := by
    rw [hβderiv_eq]
    exact (Complex.continuous_ofReal.comp Jacobians.smoothStep01_deriv_continuous).mul
      continuous_const
  have hβvel := velCont_modelPath β hβcont hβ'
  have hVo : IsOpen (chartAt (H := ℂ) w).target := (chartAt (H := ℂ) w).open_target
  have hg : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (fun v : ℂ => (chartAt (H := ℂ) w).symm v)
      (chartAt (H := ℂ) w).target := Jacobians.chartAt_symm_contMDiffOn w
  have hβV : ∀ s ∈ Set.Icc (0 : ℝ) 1, β s ∈ (chartAt (H := ℂ) w).target := by
    intro s hs; exact h_chart_ball (Jacobians.smoothStep01 s) (Jacobians.smoothStep01_mem_unit s)
  have hβdiff : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (β s)).toFun ∘ β) s := by
    intro s _
    have hd : DifferentiableAt ℝ β s :=
      ((differentiableAt_const _).sub
        (Complex.ofRealCLM.differentiableAt.comp s (Jacobians.smoothStep01_differentiable s))
          |>.mul (differentiableAt_const _)).add
        ((Complex.ofRealCLM.differentiableAt.comp s (Jacobians.smoothStep01_differentiable s))
          |>.mul (differentiableAt_const _))
    exact hd
  have hcompOn := velCont_compOn (fun v : ℂ => (chartAt (H := ℂ) w).symm v) hg hVo β hβV
    hβcont hβdiff hβvel
  exact hcompOn

/-- **`IsSmoothPath` for the general-anchor flat-ended chart path.** Assembled from the fields
above; this is the per-piece building block of the off-branch detour. -/
lemma isSmoothPath_ChartBallPathSmooth3 (w P Q : X)
    (hP : P ∈ (chartAt (H := ℂ) w).source) (hQ : Q ∈ (chartAt (H := ℂ) w).source)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    Jacobians.IsSmoothPath P Q (ChartBallPathSmooth3 w P Q) :=
  ⟨ChartBallPathSmooth3_zero w P Q hP, ChartBallPathSmooth3_one w P Q hQ,
    ChartBallPathSmooth3_continuous w P Q h_chart_ball,
    fun t _ => ChartBallPathSmooth3_chart_at_differentiableAt w P Q t h_chart_ball,
    ChartBallPathSmooth3_velCont w P Q h_chart_ball⟩

/-- Endpoint velocities of `ChartBallPathSmooth3` vanish (smoothStep chain rule, as in A1). -/
lemma pathSpeed_ChartBallPathSmooth3_zero (w P Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    Jacobians.pathSpeed (ChartBallPathSmooth3 w P Q) 0 = 0 := by
  have hdiff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (Jacobians.ChartBallPath w P Q (Jacobians.smoothStep01 0))).toFun ∘
        Jacobians.ChartBallPath w P Q) (Jacobians.smoothStep01 0) :=
    Jacobians.ChartBallPath_chart_at_self_differentiableAt w P Q (Jacobians.smoothStep01 0)
      (h_chart_ball _ (Jacobians.smoothStep01_mem_unit 0))
  have h := pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath w P Q) 0 hdiff
  show Jacobians.pathSpeed (Jacobians.ChartBallPath w P Q ∘ Jacobians.smoothStep01) 0 = 0
  rw [h, Jacobians.smoothStep01_deriv_zero]; simp

lemma pathSpeed_ChartBallPathSmooth3_one (w P Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) w) P + (s : ℂ) * (chartAt (H := ℂ) w) Q)
        ∈ (chartAt (H := ℂ) w).target) :
    Jacobians.pathSpeed (ChartBallPathSmooth3 w P Q) 1 = 0 := by
  have hdiff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (Jacobians.ChartBallPath w P Q (Jacobians.smoothStep01 1))).toFun ∘
        Jacobians.ChartBallPath w P Q) (Jacobians.smoothStep01 1) :=
    Jacobians.ChartBallPath_chart_at_self_differentiableAt w P Q (Jacobians.smoothStep01 1)
      (h_chart_ball _ (Jacobians.smoothStep01_mem_unit 1))
  have h := pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath w P Q) 1 hdiff
  show Jacobians.pathSpeed (Jacobians.ChartBallPath w P Q ∘ Jacobians.smoothStep01) 1 = 0
  rw [h, Jacobians.smoothStep01_deriv_one]; simp

end Jacobians.OfCurveSkeleton

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Period-vector telescoping over a partition.** If `δ, δ'` are closed smooth loops and there
is a partition `0 = s₀ ≤ s₁ ≤ ⋯ ≤ sₙ = 1` of `[0,1]` (with each sub-interval inside `[0,1]`) such
that the *partial* line integrals of every period basis form agree piece-by-piece
(`∫_{sₖ}^{sₖ₊₁} ωᵢ(δ') = ∫_{sₖ}^{sₖ₊₁} ωᵢ(δ)`), then `periodVec δ' = periodVec δ`.

This is the analytic core of period-preservation for the off-branch surgery, fully discharged:
`periodVec` is the integral over `[0,1]`, which splits as the sum of the partial integrals over the
subdivision (`intervalIntegral.sum_integral_adjacent_intervals`, with per-piece integrability
inherited from `IsClosedSmoothLoop.integrable` via `IntervalIntegrable.mono_set`); the hypothesis
makes the two sums equal term-by-term. The remaining (geometric) work for
`exists_loop_off_branchLocus` is to *produce* a `δ'` avoiding `branchLocus f` whose per-piece partial
integrals match `δ`'s — for pieces where `δ'` is left equal to `δ` this is trivial, and for replaced
pieces it is exactly `OfCurveSkeleton.intervalIntegral_form_pathSpeed_eq_of_subball_endpoints` (the
detour and the original sub-arc share chart-coordinate endpoints inside one sub-ball). -/
theorem periodVec_eq_of_partition_integral_eq (δ δ' : ℝ → X)
    (hδ : IsClosedSmoothLoop δ) (hδ' : IsClosedSmoothLoop δ')
    (s : ℕ → ℝ) (n : ℕ) (hs0 : s 0 = 0) (hsn : s n = 1)
    (hs_sub : ∀ k, k < n → Set.uIcc (s k) (s (k+1)) ⊆ Set.Icc (0:ℝ) 1)
    (hpiece : ∀ (i : Fin (genus X)) (k : ℕ), k < n →
      (∫ t in (s k)..(s (k+1)), (periodBasisForm X i).toFun (δ' t) (pathSpeed δ' t)) =
      (∫ t in (s k)..(s (k+1)), (periodBasisForm X i).toFun (δ t) (pathSpeed δ t))) :
    periodVec δ' = periodVec δ := by
  funext i
  show lineIntegral (periodBasisForm X i) δ' = lineIntegral (periodBasisForm X i) δ
  unfold lineIntegral
  have hint_δ : ∀ k, k < n → IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (δ t) (pathSpeed δ t)) volume (s k) (s (k+1)) :=
    fun k hk => (hδ.integrable i).mono_set (by
      rw [Set.uIcc_of_le (zero_le_one)]; exact hs_sub k hk)
  have hint_δ' : ∀ k, k < n → IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (δ' t) (pathSpeed δ' t)) volume (s k) (s (k+1)) :=
    fun k hk => (hδ'.integrable i).mono_set (by
      rw [Set.uIcc_of_le (zero_le_one)]; exact hs_sub k hk)
  have htel_δ := intervalIntegral.sum_integral_adjacent_intervals (a := s) (n := n)
    (f := fun t => (periodBasisForm X i).toFun (δ t) (pathSpeed δ t)) hint_δ
  have htel_δ' := intervalIntegral.sum_integral_adjacent_intervals (a := s) (n := n)
    (f := fun t => (periodBasisForm X i).toFun (δ' t) (pathSpeed δ' t)) hint_δ'
  rw [hs0, hsn] at htel_δ htel_δ'
  rw [← htel_δ, ← htel_δ']
  exact Finset.sum_congr rfl (fun k hk => hpiece i k (Finset.mem_range.mp hk))

end Jacobians
