/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.LineIntegral
import Jacobians.Genus

/-!
# Cotangent-bundle coefficient continuity (the *local* coefficient is the right object)

A `HolomorphicOneForms X` is a `ContMDiffSection` of the cotangent hom-bundle
`x ↦ TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ`. To integrate a form along a path one needs control of
its coefficient. The naive "global coefficient" `x ↦ α.toFun x (1 : TangentSpace 𝓘(ℂ) x)`
is **discontinuous** in general: `1 : TangentSpace 𝓘(ℂ) x` is the `∂/∂z` of the *preferred
chart at `x`*, and since the chart varies with `x` and chart transitions are general
biholomorphisms (derivatives ≠ 1), the constant-`1` tangent section is not continuous (it is
continuous iff the tangent bundle is trivialized by the atlas, i.e. parallelizable — false for
genus ≥ 2). Pairing it with a form nonzero at a point gives a discontinuous map. The
obstruction is isolated below (`const_one_section_continuous_of_coordChange_fixes_one`,
`target_eq_inCoordinates_of_w`).

The **correct, provable** object is the coefficient read in a *fixed* chart/trivialization
(`continuousAt_inCoordinates`, `continuousAt_localCoeff`). This is the tool a chart-patchwork
needs to integrate `α.toFun (γ s) (pathSpeed γ s)` along a (chart-pointwise-differentiable)
path: on a segment where `γ` stays in one chart, the integrand is the (continuous, bounded)
fixed-chart coefficient times the (integrable) fixed-chart velocity. It is also the
continuity input that `traceForm_comp` needs.

Derived via `contMDiffAt_hom_bundle` (Mathlib): the section's smoothness gives that its
`ContinuousLinearMap.inCoordinates` representation is continuous *into the fixed normed space*
`ℂ →L[ℂ] ℂ`. (Found 2026-05-30; corrects the earlier false "global coefficient" target.)
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology
open Filter Set MeasureTheory

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **The continuous local object.** Near `x₀`, the coordinate of the section `α` in the FIXED
hom-bundle trivialization at `x₀` is continuous (indeed it is `ContMDiffAt`) as a map into the
fixed normed space `ℂ →L[ℂ] ℂ`. This is `inCoordinates (α x)`. -/
theorem continuousAt_inCoordinates (α : HolomorphicOneForms X) (x₀ : X) :
    ContinuousAt (fun x : X => ContinuousLinearMap.inCoordinates ℂ
      (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ) x₀ x x₀ x (α.toFun x)) x₀ := by
  have hα := α.contMDiff_toFun x₀
  rw [contMDiffAt_hom_bundle] at hα
  exact hα.2.continuousAt

/-- **The local coefficient is continuous.** `x ↦ inCoordinates (α x) 1` (the coefficient of
`α` read in the FIXED chart at `x₀`, i.e. `α` paired with the *coordinate vector field of the
chart at `x₀`*) is continuous at `x₀`. NOTE this is `inCoordinates (α x) 1`, **not** the
discontinuous `α x 1`. -/
theorem continuousAt_localCoeff (α : HolomorphicOneForms X) (x₀ : X) :
    ContinuousAt (fun x : X => ContinuousLinearMap.inCoordinates ℂ
      (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ) x₀ x x₀ x (α.toFun x) (1 : ℂ)) x₀ :=
  (continuousAt_inCoordinates α x₀).clm_apply continuousAt_const

/-- **The obstruction, isolated.** Continuity of the constant-`1` tangent section is implied by
(in fact equivalent to, via `FiberBundleCore.continuous_const_section`) the constant `1 : ℂ`
being invariant under EVERY chart-transition derivative, `coordChange i j x 1 = 1`. That
hypothesis is false for a complex 1-manifold with non-trivial tangent bundle (genus ≥ 2):
chart transitions are general biholomorphisms whose derivatives do not fix `1`. Hence the
constant-`1` section is discontinuous, and `x ↦ α x (1 : TangentSpace x)` is discontinuous. -/
theorem const_one_section_continuous_of_coordChange_fixes_one
    (h : ∀ (i j : atlas ℂ X) (x : X),
        x ∈ (tangentBundleCore 𝓘(ℂ) X).toFiberBundleCore.baseSet i ∩
            (tangentBundleCore 𝓘(ℂ) X).toFiberBundleCore.baseSet j →
        (tangentBundleCore 𝓘(ℂ) X).toFiberBundleCore.coordChange i j x 1 = 1) :
    Continuous (fun x : X => (Bundle.TotalSpace.mk' ℂ
        (E := fun (x : X) => TangentSpace 𝓘(ℂ) x) x ((1 : ℂ) : TangentSpace 𝓘(ℂ) x))) :=
  (tangentBundleCore 𝓘(ℂ) X).toFiberBundleCore.continuous_const_section 1 h

/-- **Why the global target differs from the continuous local coefficient.** Near `x₀`,
`α x (1 : TangentSpace x)` equals `inCoordinates (α x)` applied to the input
`continuousLinearMapAt (triv x₀) x 1`. The operator `inCoordinates (α x)` is continuous
(`continuousAt_inCoordinates`), but the INPUT is the constant-`1` tangent-section coordinate,
which is discontinuous (see the obstruction). So the global target is a continuous operator
times a discontinuous input — discontinuous. -/
theorem target_eq_inCoordinates_of_w (α : HolomorphicOneForms X) (x₀ x : X)
    (hx : x ∈ (chartAt ℂ x₀).source) :
    α.toFun x ((1 : ℂ) : TangentSpace 𝓘(ℂ) x) =
      ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ)
        x₀ x x₀ x (α.toFun x)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).continuousLinearMapAt ℂ x (1 : ℂ)) := by
  have hxbase : x ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hxbase]

/-- **General-vector form of `target_eq_inCoordinates_of_w`.** For any tangent vector `v` at
`x ∈ (chartAt ℂ x₀).source`, applying the form equals applying its fixed-`x₀`-trivialization
`inCoordinates` representation to `v` read in that trivialization. (The `v = 1` case is the
obstruction lemma `target_eq_inCoordinates_of_w`; this general version is what lets a
chart-patchwork rewrite the line-integral integrand `α.toFun (γ s) (pathSpeed γ s)` into a
product of the continuous local coefficient and the trivialized velocity.) -/
theorem apply_eq_inCoordinates (α : HolomorphicOneForms X) (x₀ x : X)
    (hx : x ∈ (chartAt ℂ x₀).source) (v : TangentSpace 𝓘(ℂ) x) :
    α.toFun x v =
      ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ)
        x₀ x x₀ x (α.toFun x)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).continuousLinearMapAt ℂ x v) := by
  have hxbase : x ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hxbase]

/-! ## The justification lemma: continuous velocity ⇒ integrable integrand

This is what makes the genuinely-`C¹` loop predicate sound: if the **velocity tangent
section** `s ↦ ⟨γ s, pathSpeed γ s⟩` is continuous on `[0,1]`, then the line-integral
integrand `α.toFun (γ s) (pathSpeed γ s)` is continuous (hence interval-integrable) — for
*every* form `α`. The proof pairs the (continuous, fixed-chart) `inCoordinates` operator
`continuousAt_inCoordinates` with the trivialized velocity (continuous since the velocity
section is, and the trivialization is continuous), via `apply_eq_inCoordinates`. Crucially the
hypothesis is the *geometric* velocity-section continuity, NOT continuity of the bare number
`pathSpeed γ` (which would still leave the discontinuous coefficient `α.toFun · 1`). -/

/-- Continuous velocity tangent-section ⇒ the form integrand is `ContinuousOn [0,1]`. -/
theorem continuousOn_form_pathSpeed (α : HolomorphicOneForms X) (γ : ℝ → X)
    (hvel : ContinuousOn (fun s : ℝ =>
        (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s)))
      (Set.Icc 0 1)) :
    ContinuousOn (fun s : ℝ => α.toFun (γ s) (pathSpeed γ s)) (Set.Icc 0 1) := by
  have hγ : ContinuousOn γ (Set.Icc (0 : ℝ) 1) :=
    (FiberBundle.continuous_proj ℂ (TangentSpace 𝓘(ℂ) (M := X))).comp_continuousOn hvel
  intro s₀ hs₀
  set x₀ := γ s₀ with hx₀
  set triv := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀ with htriv
  set vel : ℝ → Bundle.TotalSpace ℂ (TangentSpace 𝓘(ℂ) (M := X)) :=
    fun s => Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s)
      (pathSpeed γ s) with hvel_def
  have hx₀src : x₀ ∈ (chartAt ℂ x₀).source := mem_chart_source ℂ x₀
  have hev_src : ∀ᶠ s in 𝓝[Set.Icc (0 : ℝ) 1] s₀, γ s ∈ (chartAt ℂ x₀).source :=
    (hγ s₀ hs₀).eventually ((chartAt ℂ x₀).open_source.mem_nhds hx₀src)
  have hO : ContinuousWithinAt (fun s : ℝ => ContinuousLinearMap.inCoordinates ℂ
      (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ) x₀ (γ s) x₀ (γ s)
      (α.toFun (γ s))) (Set.Icc 0 1) s₀ :=
    (continuousAt_inCoordinates α x₀).comp_continuousWithinAt (hγ s₀ hs₀)
  have hV : ContinuousWithinAt (fun s : ℝ =>
      triv.continuousLinearMapAt ℂ (γ s) (pathSpeed γ s)) (Set.Icc 0 1) s₀ := by
    have hx₀base : x₀ ∈ triv.baseSet := mem_baseSet_trivializationAt ℂ _ x₀
    have hmem_src : vel s₀ ∈ triv.source := triv.mem_source.mpr hx₀base
    have htrivCA : ContinuousAt triv (vel s₀) :=
      triv.continuousOn.continuousAt (triv.open_source.mem_nhds hmem_src)
    have hcomp : ContinuousWithinAt (fun s : ℝ => (triv (vel s)).2) (Set.Icc 0 1) s₀ :=
      (continuous_snd.continuousAt.comp_continuousWithinAt
        (htrivCA.comp_continuousWithinAt (hvel s₀ hs₀)))
    refine hcomp.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [hev_src] with s hs
      have hsbase : γ s ∈ triv.baseSet := by
        rw [htriv, TangentBundle.trivializationAt_baseSet]; exact hs
      exact triv.continuousLinearMapAt_apply_of_mem ℂ hsbase (pathSpeed γ s)
    · exact triv.continuousLinearMapAt_apply_of_mem ℂ hx₀base (pathSpeed γ s₀)
  have hpair : ContinuousWithinAt (fun s : ℝ =>
      (ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ)
        x₀ (γ s) x₀ (γ s) (α.toFun (γ s)))
      (triv.continuousLinearMapAt ℂ (γ s) (pathSpeed γ s))) (Set.Icc 0 1) s₀ :=
    hO.clm_apply hV
  refine hpair.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hev_src] with s hs
    exact apply_eq_inCoordinates α x₀ (γ s) hs (pathSpeed γ s)
  · exact apply_eq_inCoordinates α x₀ (γ s₀) hx₀src (pathSpeed γ s₀)

/-- Continuous velocity tangent-section ⇒ the form integrand is interval-integrable on `[0,1]`.
**The justification for the genuinely-`C¹` loop predicate**: the `integrable` field follows from
the velocity-continuity (`velCont`) field. -/
theorem intervalIntegrable_form_pathSpeed_of_velContinuous (α : HolomorphicOneForms X) (γ : ℝ → X)
    (hvel : ContinuousOn (fun s : ℝ =>
        (Bundle.TotalSpace.mk' ℂ (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s)))
      (Set.Icc 0 1)) :
    IntervalIntegrable (fun s : ℝ => α.toFun (γ s) (pathSpeed γ s)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  exact continuousOn_form_pathSpeed α γ hvel

/-! ## Velocity-section continuity is preserved by smooth composition

The constructor-side tools for the C¹ refactor. `velCont_comp` handles `IsClosedSmoothLoop.comp`
(`f∘γ`, global `f`); `velCont_compOn` handles the §3 lift `g∘δr` (local section `g`, `C^ω` on an
open `V`) and the `ChartBall` base case (via `chartAt _).symm`). **Both require, beyond velocity
continuity `hγ`, the pointwise `hγdiff` and `hγcont` fields** — these are NOT implied by `hγ`
(`pathSpeed` uses the junk-value convention, so a nowhere-differentiable continuous curve has a
continuous velocity section), which is exactly why the refactor *keeps* the `cont`/`diff` fields and
only replaces `integrable` with `velCont`. -/

/-- Local analogue of `pathSpeed_comp_eq_mfderiv`: only `MDifferentiableAt f (γ t)` is needed (the
global `ContMDiff f` in the original is used solely to produce this), so it applies to local sections. -/
theorem pathSpeed_comp_eq_mfderiv_of_mdiff (f : X → Y) (γ : ℝ → X) (t : ℝ)
    (hf_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (γ t))
    (hγ_cont : ContinuousAt γ t)
    (hγ_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) :
    pathSpeed (f ∘ γ) t = mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t) (pathSpeed γ t) := by
  set φ_X := chartAt (H := ℂ) (γ t) with hφ_X_def
  set φ_Y := chartAt (H := ℂ) (f (γ t)) with hφ_Y_def
  set f_loc : ℂ → ℂ := fun z => φ_Y (f (φ_X.symm z)) with hf_loc_def
  set g_X : ℝ → ℂ := φ_X.toFun ∘ γ with hg_X_def
  set g_Y : ℝ → ℂ := φ_Y.toFun ∘ (f ∘ γ) with hg_Y_def
  have hγt_X : γ t ∈ φ_X.source := mem_chart_source ℂ (γ t)
  have hfγt_Y : f (γ t) ∈ φ_Y.source := mem_chart_source ℂ (f (γ t))
  have hγ_source : ∀ᶠ s in 𝓝 t, γ s ∈ φ_X.source :=
    hγ_cont.eventually (φ_X.open_source.mem_nhds hγt_X)
  have h_eq : g_Y =ᶠ[𝓝 t] f_loc ∘ g_X := by
    filter_upwards [hγ_source] with s hs
    simp only [hg_Y_def, hf_loc_def, hg_X_def, Function.comp_apply]
    congr 2
    exact (φ_X.left_inv hs).symm
  have hf_loc_diff_ℂ : DifferentiableAt ℂ f_loc (g_X t) := by
    have h1 := hf_mdiff.differentiableWithinAt_writtenInExtChartAt
    rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
    convert h1 using 2
  have hf_loc_hasFD_ℂ : HasFDerivAt f_loc (fderiv ℂ f_loc (g_X t)) (g_X t) :=
    hf_loc_diff_ℂ.hasFDerivAt
  have hf_loc_hasFD_ℝ : HasFDerivAt f_loc
      ((fderiv ℂ f_loc (g_X t)).restrictScalars ℝ) (g_X t) := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hf_loc_hasFD_ℂ ⊢
    simp only [ContinuousLinearMap.coe_restrictScalars']
    exact hf_loc_hasFD_ℂ
  have hf_loc_diff_ℝ : DifferentiableAt ℝ f_loc (g_X t) :=
    hf_loc_hasFD_ℝ.differentiableAt
  have hf_loc_fderiv_ℝ : fderiv ℝ f_loc (g_X t) =
      (fderiv ℂ f_loc (g_X t)).restrictScalars ℝ :=
    hf_loc_hasFD_ℝ.fderiv
  have h_chain : fderiv ℝ (f_loc ∘ g_X) t =
      (fderiv ℝ f_loc (g_X t)).comp (fderiv ℝ g_X t) :=
    fderiv_comp t hf_loc_diff_ℝ hγ_diff
  have h_mfderiv : mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t) = fderiv ℂ f_loc (g_X t) := by
    rw [hf_mdiff.mfderiv]
    rw [ModelWithCorners.range_eq_univ, fderivWithin_univ]
    congr 1
  show pathSpeed (f ∘ γ) t = mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t) (pathSpeed γ t)
  rw [h_mfderiv]
  show fderiv ℝ ((chartAt (H := ℂ) ((f ∘ γ) t)).toFun ∘ (f ∘ γ)) t 1 =
    fderiv ℂ f_loc (g_X t) (pathSpeed γ t)
  have h_gY : (chartAt (H := ℂ) ((f ∘ γ) t)).toFun ∘ (f ∘ γ) = g_Y := rfl
  rw [h_gY, h_eq.fderiv_eq, h_chain, ContinuousLinearMap.comp_apply,
      hf_loc_fderiv_ℝ, ContinuousLinearMap.coe_restrictScalars']
  rfl

/-- **GLOBAL: velocity-section continuity is preserved by a global `C^ω` map.** For the
`IsClosedSmoothLoop.comp` constructor. Identifies velocity-section(`f∘γ`) with `tangentMap f`
applied to velocity-section(`γ`) (pointwise via `pathSpeed_comp_eq_mfderiv`), then composes with the
continuous `tangentMap f`. -/
theorem velCont_comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (γ : ℝ → X)
    (hγcont : Continuous γ)
    (hγdiff : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ s)).toFun ∘ γ) s)
    (hγ : ContinuousOn (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s))) (Set.Icc 0 1)) :
    ContinuousOn (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := Y)) (f (γ s)) (pathSpeed (f ∘ γ) s))) (Set.Icc 0 1) := by
  have hcont_tm : Continuous (tangentMap 𝓘(ℂ) 𝓘(ℂ) f) :=
    hf.continuous_tangentMap (by decide : (1 : WithTop ℕ∞) ≤ ω)
  have hcomp : ContinuousOn ((tangentMap 𝓘(ℂ) 𝓘(ℂ) f) ∘
      (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
        (E := TangentSpace 𝓘(ℂ) (M := X)) (γ s) (pathSpeed γ s)))) (Set.Icc 0 1) :=
    hcont_tm.comp_continuousOn hγ
  refine hcomp.congr ?_
  intro s hs
  simp only [Function.comp_apply, tangentMap, Bundle.TotalSpace.mk']
  congr 1
  exact pathSpeed_comp_eq_mfderiv f hf γ s hγcont.continuousAt (hγdiff s hs)

/-- **LOCAL: velocity-section continuity is preserved by a map `C^ω` on an open set.** For the §3
lift `g∘γ` (`g` a local section) and the `ChartBall` base case. Open `V` upgrades `ContMDiffOn` to
`ContMDiffAt`/`MDifferentiableAt`, so `pathSpeed_comp_eq_mfderiv_of_mdiff` applies, and
`tangentMapWithin g V = tangentMap g` on `V`. -/
theorem velCont_compOn (g : Y → X) {V : Set Y} (hg : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g V)
    (hVo : IsOpen V) (γ : ℝ → Y) (hγV : ∀ s ∈ Set.Icc (0 : ℝ) 1, γ s ∈ V)
    (hγcont : Continuous γ)
    (hγdiff : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ s)).toFun ∘ γ) s)
    (hγ : ContinuousOn (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := Y)) (γ s) (pathSpeed γ s))) (Set.Icc 0 1)) :
    ContinuousOn (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := X)) (g (γ s)) (pathSpeed (g ∘ γ) s))) (Set.Icc 0 1) := by
  have htmw : ContinuousOn (tangentMapWithin 𝓘(ℂ) 𝓘(ℂ) g V) (Bundle.TotalSpace.proj ⁻¹' V) :=
    hg.continuousOn_tangentMapWithin (by decide : (1 : WithTop ℕ∞) ≤ ω) hVo.uniqueMDiffOn
  have hmaps : Set.MapsTo (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
      (E := TangentSpace 𝓘(ℂ) (M := Y)) (γ s) (pathSpeed γ s)))
      (Set.Icc 0 1) (Bundle.TotalSpace.proj ⁻¹' V) := fun s hs => hγV s hs
  have hcomp : ContinuousOn ((tangentMapWithin 𝓘(ℂ) 𝓘(ℂ) g V) ∘
      (fun s : ℝ => (Bundle.TotalSpace.mk' ℂ
        (E := TangentSpace 𝓘(ℂ) (M := Y)) (γ s) (pathSpeed γ s)))) (Set.Icc 0 1) :=
    htmw.comp hγ hmaps
  refine hcomp.congr ?_
  intro s hs
  have hgmdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (γ s) :=
    (hg.contMDiffAt (hVo.mem_nhds (hγV s hs))).mdifferentiableAt (by decide : ω ≠ 0)
  rw [Function.comp_apply, tangentMapWithin_eq_tangentMap (hVo.uniqueMDiffWithinAt (hγV s hs)) hgmdiff]
  simp only [tangentMap, Bundle.TotalSpace.mk']
  congr 1
  exact pathSpeed_comp_eq_mfderiv_of_mdiff g γ s hgmdiff hγcont.continuousAt (hγdiff s hs)

end Jacobians
