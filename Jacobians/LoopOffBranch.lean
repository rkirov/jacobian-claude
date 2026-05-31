import Jacobians.SmoothPathCore
import Mathlib.Analysis.Complex.HasPrimitives

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

end Jacobians.OfCurveSkeleton
