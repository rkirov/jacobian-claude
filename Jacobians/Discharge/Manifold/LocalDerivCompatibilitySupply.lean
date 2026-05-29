/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.Discharge.Manifold.DerivBridgeFromNonConstant
import Jacobians.Discharge.Manifold.CriticalSetDerivBridge
import Jacobians.Discharge.Manifold.ClopennessOfLocallyConstDischarge
import Jacobians.Discharge.Manifold.MeromorphicAt
import Jacobians.Discharge.Manifold.RamificationIndexPositive
import Jacobians.Discharge.Manifold.MeromorphicExtension
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Analytic

set_option autoImplicit true


/-! # Unconditional supplier for `LocalDerivCompatibilityData`

This file (the **R-Compat** chip) constructs an unconditional supplier for
the `LocalDerivCompatibilityData f x` record consumed by
`derivBridgeData_of_localCompatibility` (in `DerivBridgeFromNonConstant.lean`).

The construction uses, for the chart pullback `F` at `x`,
* the *literal* chart pullback `F := (chartAt ℂ (f.toRiemannSphere x))
  ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm` (analyticity at `(chartAt ℂ x) x`
  is automatic by ZZ24);
* the unconditional non-eventual-constancy of `F` at `(chartAt ℂ x) x`
  (`chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst`
  combined with `clopennessOfLocallyConst_holds`, modulo a non-constancy
  hypothesis on `f.toRiemannSphere`);
* the per-point compatibility iff on a *small* open neighbourhood `V` of
  `x`, established by combining:
  - the planar bridge `notInjOn_iff_deriv_zero_of_analytic_of_order` (ZZ99)
    at the point `x'` (using the *canonical* chart pullback at `x'`),
  - the chart-transition non-vanishing-derivative lemma
    `deriv_chart_transition_of_isManifold_ne_zero`, applied twice (source
    and target) to relate the canonical pullback at `x'` to the *fixed*
    pullback at `x`.

## What this file ships

* `localDerivCompatibilityData_of_meromorphicNonzero`
  — given non-constancy of `f.toRiemannSphere`, build the per-point
  unconditional `LocalDerivCompatibilityData f x` for every `x : X`.

* `derivBridgeData_of_meromorphicNonzero`
  — corollary: per-point `DerivBridgeData (f.toRiemannSphere) x` for every
  `x : X`, by composition with `derivBridgeData_of_localCompatibility`.

No `sorry`, no `axiom`. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace Jacobians.Discharge

namespace Manifold

universe u

/-! ## Helper: chart-transition derivative for `chartAt` charts -/

/-- A specialised form of `deriv_chart_transition_of_isManifold_ne_zero`
applied to the canonical charts `chartAt ℂ x` and `chartAt ℂ x'` at two
points of a complex 1-manifold, both lying in `(chartAt ℂ x).source`. -/
private lemma deriv_chartAt_transition_ne_zero
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (x x' : X) (hx' : x' ∈ (chartAt ℂ x).source) :
    deriv ((chartAt ℂ x') ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x') ≠ 0 := by
  have h_atlas_x : chartAt ℂ x ∈ atlas ℂ X := chart_mem_atlas ℂ x
  have h_atlas_x' : chartAt ℂ x' ∈ atlas ℂ X := chart_mem_atlas ℂ x'
  have hx'_atx' : x' ∈ (chartAt ℂ x').source := mem_chart_source ℂ x'
  exact Jacobians.Discharge.deriv_chart_transition_of_isManifold_ne_zero
    h_atlas_x h_atlas_x' hx' hx'_atx'

/-! ## Main supplier -/

/-- **Unconditional `LocalDerivCompatibilityData` supplier.**

For `f : MeromorphicNonzero X` with `¬ IsConstantMap f.toRiemannSphere`, at
every `x : X`, build `LocalDerivCompatibilityData f x` whose `F` is the
literal chart pullback of `f.toRiemannSphere` through `chartAt ℂ x` and
`chartAt ℂ (f.toRiemannSphere x)`.

The neighbourhood `V` is `(chartAt ℂ x).source ∩ f.toRiemannSphere ⁻¹'
(chartAt ℂ (f.toRiemannSphere x)).source` — open, contains `x`, and on it
the chart-transition argument relates the fixed-chart pullback at `x` to
the canonical-chart pullback at every `x' ∈ V`. -/
noncomputable def localDerivCompatibilityData_of_meromorphicNonzero
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : Jacobians.Discharge.MeromorphicNonzero X)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap f.toRiemannSphere)
    (x : X) :
    LocalDerivCompatibilityData f x := by
  classical
  -- Abbreviations.
  set c : OpenPartialHomeomorph X ℂ := chartAt ℂ x with hc_def
  set d : OpenPartialHomeomorph RiemannSphere ℂ := chartAt ℂ (f.toRiemannSphere x)
    with hd_def
  set F : ℂ → ℂ := d ∘ f.toRiemannSphere ∘ c.symm with hF_def
  -- Manifold-side facts about `f.toRiemannSphere`.
  have hf : ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f.toRiemannSphere :=
    Jacobians.Discharge.MeromorphicNonzero.toRiemannSphere_contMDiff f
  -- Chart-source membership.
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  have hfx_d : f.toRiemannSphere x ∈ d.source := mem_chart_source ℂ (f.toRiemannSphere x)
  -- Open neighbourhood `V` of `x`.
  set V : Set X := c.source ∩ f.toRiemannSphere ⁻¹' d.source with hV_def
  have hV_open : IsOpen V := by
    refine c.open_source.inter ?_
    exact d.open_source.preimage hf.continuous
  have hxV : x ∈ V := ⟨hxc, hfx_d⟩
  have hV_subS : V ⊆ c.source := fun _ hy => hy.1
  -- Analyticity of `F` at `c x` (ZZ24).
  have hFA_at_x : AnalyticAt ℂ F (c x) :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback hf x
  -- Non-eventual-constancy of `F` at `c x` (clopenness discharge).
  have hClop :
      Jacobians.Discharge.ContMDiff.Degree.ClopennessOfLocallyConstHypothesis
        X RiemannSphere :=
    Jacobians.Discharge.ContMDiff.Degree.clopennessOfLocallyConst_holds
  have hChartNEC :
      Jacobians.Discharge.ContMDiff.Degree.ChartPullbackNotEventuallyConstHypothesis
        X RiemannSphere :=
    Jacobians.Discharge.ContMDiff.Degree.chartPullbackNotEventuallyConst_of_clopennessOfLocallyConst
      hClop
  have hFne_raw :
      ¬ ∀ᶠ z in 𝓝 (c x),
        ((chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
            ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f.toRiemannSphere x)) (f.toRiemannSphere x) :=
    hChartNEC f.toRiemannSphere hf hnc (f.toRiemannSphere x) x rfl
  -- `F (c x) = d (f.toRiemannSphere x)` via chart left-inverse.
  have hFcx : F (c x) = d (f.toRiemannSphere x) := by
    have h_inv : c.symm (c x) = x := c.left_inv hxc
    show (d ∘ f.toRiemannSphere ∘ c.symm) (c x) = d (f.toRiemannSphere x)
    simp [Function.comp, h_inv]
  -- Translate `hFne_raw` to "F not eventually equal to F (c x)".
  have hFne : ¬ ∀ᶠ z in 𝓝 (c x), F z = F (c x) := by
    intro hev
    apply hFne_raw
    exact hev.mono (fun z hz => by
      show ((chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
            ∘ (chartAt ℂ x).symm) z
          = (chartAt ℂ (f.toRiemannSphere x)) (f.toRiemannSphere x)
      have : F z = F (c x) := hz
      rw [show ((chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
            ∘ (chartAt ℂ x).symm) z = F z from rfl, this, hFcx])
  -- The hard part: per-point compatibility on V.
  -- For x' ∈ V: x' ∈ criticalSet ↔ deriv F (c x') = 0.
  -- Strategy:
  --   1. ZZ99 at x' (canonical chart pullback F' at x') gives
  --      x' ∈ criticalSet ↔ deriv F' (c' x') = 0.
  --   2. Chart-transition argument: F = (d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)
  --      on a neighbourhood of (c x'), so deriv F (c x') is a nonzero
  --      multiple of deriv F' (c' x'), hence zero iff zero.
  have hCompat :
      ∀ x' ∈ V, (x' ∈ f.criticalSet) ↔ deriv F (c x') = 0 := by
    intro x' hx'V
    obtain ⟨hx'c, hx'fd⟩ := hx'V
    -- Canonical charts at x' and at f.toRiemannSphere x'.
    set c' : OpenPartialHomeomorph X ℂ := chartAt ℂ x' with hc'_def
    set d' : OpenPartialHomeomorph RiemannSphere ℂ := chartAt ℂ (f.toRiemannSphere x')
      with hd'_def
    set F' : ℂ → ℂ := d' ∘ f.toRiemannSphere ∘ c'.symm with hF'_def
    have hx'c' : x' ∈ c'.source := mem_chart_source ℂ x'
    have hfx'd' : f.toRiemannSphere x' ∈ d'.source :=
      mem_chart_source ℂ (f.toRiemannSphere x')
    -- F' analytic at c' x' (ZZ24).
    have hF'A_at_x' : AnalyticAt ℂ F' (c' x') :=
      Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback
        hf x'
    -- F' (c' x') = d' (f.toRiemannSphere x').
    have hF'cx' : F' (c' x') = d' (f.toRiemannSphere x') := by
      have h_inv : c'.symm (c' x') = x' := c'.left_inv hx'c'
      show (d' ∘ f.toRiemannSphere ∘ c'.symm) (c' x') = d' (f.toRiemannSphere x')
      simp [Function.comp, h_inv]
    -- F' not eventually equal to F' (c' x') at c' x' (chart NEC at x').
    have hF'ne_raw :
        ¬ ∀ᶠ z in 𝓝 (c' x'),
          ((chartAt ℂ (f.toRiemannSphere x')) ∘ f.toRiemannSphere
              ∘ (chartAt ℂ x').symm) z
            = (chartAt ℂ (f.toRiemannSphere x')) (f.toRiemannSphere x') :=
      hChartNEC f.toRiemannSphere hf hnc (f.toRiemannSphere x') x' rfl
    have hF'ne : ¬ ∀ᶠ z in 𝓝 (c' x'), F' z = F' (c' x') := by
      intro hev
      apply hF'ne_raw
      exact hev.mono (fun z hz => by
        show ((chartAt ℂ (f.toRiemannSphere x')) ∘ f.toRiemannSphere
              ∘ (chartAt ℂ x').symm) z
            = (chartAt ℂ (f.toRiemannSphere x')) (f.toRiemannSphere x')
        have : F' z = F' (c' x') := hz
        rw [show ((chartAt ℂ (f.toRiemannSphere x')) ∘ f.toRiemannSphere
              ∘ (chartAt ℂ x').symm) z = F' z from rfl, this, hF'cx'])
    -- Order of (F' - F' (c' x')) at (c' x') is finite.
    have hF'A_sub : AnalyticAt ℂ (fun z => F' z - F' (c' x')) (c' x') :=
      hF'A_at_x'.sub analyticAt_const
    have h_ord_ne_top :
        analyticOrderAt (fun z => F' z - F' (c' x')) (c' x') ≠ ⊤ := by
      intro h_top
      apply hF'ne
      have h := analyticOrderAt_eq_top.mp h_top
      exact h.mono (fun z hz => sub_eq_zero.mp hz)
    have hF'_self : (fun z => F' z - F' (c' x')) (c' x') = 0 := by simp
    have h_ord_ne_zero :
        analyticOrderAt (fun z => F' z - F' (c' x')) (c' x') ≠ 0 := by
      intro h_zero
      have hne := (hF'A_sub.analyticOrderAt_eq_zero).mp h_zero
      exact hne hF'_self
    -- Extract the natural number k.
    set ord : ℕ∞ := analyticOrderAt (fun z => F' z - F' (c' x')) (c' x') with hord_def
    obtain ⟨k, hk_eq⟩ : ∃ k : ℕ, ord = (k : ℕ∞) := by
      cases hord_eq : ord with
      | top => exact absurd hord_eq h_ord_ne_top
      | coe n => exact ⟨n, by simp [hord_eq]⟩
    have hk_ge_one : 1 ≤ k := by
      by_contra hlt
      push_neg at hlt
      interval_cases k
      apply h_ord_ne_zero
      exact hk_eq
    -- ZZ99 at x' via the canonical chart pullback F'.
    -- The planar iff: ¬ InjOn locally at c' x' for F' ↔ deriv F' (c' x') = 0.
    have h_planar :
        (¬ ∃ U ∈ 𝓝 (c' x'), Set.InjOn F' U) ↔ deriv F' (c' x') = 0 := by
      apply notInjOn_iff_deriv_zero_of_analytic_of_order hF'A_at_x' hk_ge_one
      -- Need: analyticOrderAt (F' - F' (c' x')) (c' x') = (k : ℕ∞).
      exact hk_eq
    -- Bridge x' ∈ criticalSet (= ¬ ∃ U ∈ 𝓝 x', InjOn f̃ U) ↔ ¬ ∃ U' ∈ 𝓝 (c' x'), InjOn F' U'.
    -- Forward: f̃ locally injective near x' iff F' locally injective near c' x'
    -- (both directions through the chart partial-homeomorph c' restricted to c'.source
    -- and the injectivity of d' on d'.source).
    have h_inj_iff_x' :
        (∃ U ∈ 𝓝 x', Set.InjOn f.toRiemannSphere U) ↔
          (∃ U' ∈ 𝓝 (c' x'), Set.InjOn F' U') := by
      constructor
      · rintro ⟨U, hU_nhds, hU_inj⟩
        -- Take U ∩ c'.source ∩ f̃ ⁻¹' d'.source — open nbhd of x'.
        set U₁ : Set X := U ∩ c'.source ∩ f.toRiemannSphere ⁻¹' d'.source with hU₁_def
        have hf_cont : Continuous f.toRiemannSphere := hf.continuous
        have hU₁_nhds : U₁ ∈ 𝓝 x' :=
          Filter.inter_mem (Filter.inter_mem hU_nhds (c'.open_source.mem_nhds hx'c'))
            (hf_cont.continuousAt.preimage_mem_nhds (d'.open_source.mem_nhds hfx'd'))
        -- Image via c' is open in ℂ.
        have hU₁_subc' : U₁ ⊆ c'.source := fun _ hy => hy.1.2
        obtain ⟨U₁_open, hU₁_open_open, hU₁_open_sub, hx'_U₁_open⟩ :
            ∃ U_o, IsOpen U_o ∧ U_o ⊆ U₁ ∧ x' ∈ U_o := by
          obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU₁_nhds
          exact ⟨W, hW_open, hW_sub, hxW⟩
        have hU₁_open_subc' : U₁_open ⊆ c'.source := hU₁_open_sub.trans hU₁_subc'
        set U' : Set ℂ := c' '' U₁_open with hU'_def
        have hU'_open : IsOpen U' :=
          c'.isOpen_image_of_subset_source hU₁_open_open hU₁_open_subc'
        have hcx'_in_U' : c' x' ∈ U' := ⟨x', hx'_U₁_open, rfl⟩
        have hU'_nhds : U' ∈ 𝓝 (c' x') := hU'_open.mem_nhds hcx'_in_U'
        refine ⟨U', hU'_nhds, ?_⟩
        -- Show InjOn F' U'.
        rintro z₁ ⟨y₁, hy₁_U, hy₁_eq⟩ z₂ ⟨y₂, hy₂_U, hy₂_eq⟩ hF'_eq
        have hy₁_subc' : y₁ ∈ c'.source := hU₁_open_subc' hy₁_U
        have hy₂_subc' : y₂ ∈ c'.source := hU₁_open_subc' hy₂_U
        have hy₁_U₁ : y₁ ∈ U₁ := hU₁_open_sub hy₁_U
        have hy₂_U₁ : y₂ ∈ U₁ := hU₁_open_sub hy₂_U
        have hy₁_U_outer : y₁ ∈ U := hy₁_U₁.1.1
        have hy₂_U_outer : y₂ ∈ U := hy₂_U₁.1.1
        have hy₁_fd' : f.toRiemannSphere y₁ ∈ d'.source := hy₁_U₁.2
        have hy₂_fd' : f.toRiemannSphere y₂ ∈ d'.source := hy₂_U₁.2
        -- Translate F' equality to f.toRiemannSphere equality at y₁, y₂.
        have h_inv_y₁ : c'.symm (c' y₁) = y₁ := c'.left_inv hy₁_subc'
        have h_inv_y₂ : c'.symm (c' y₂) = y₂ := c'.left_inv hy₂_subc'
        have hF'_at_y₁ : F' (c' y₁) = d' (f.toRiemannSphere y₁) := by
          show (d' ∘ f.toRiemannSphere ∘ c'.symm) (c' y₁) = d' (f.toRiemannSphere y₁)
          simp [Function.comp, h_inv_y₁]
        have hF'_at_y₂ : F' (c' y₂) = d' (f.toRiemannSphere y₂) := by
          show (d' ∘ f.toRiemannSphere ∘ c'.symm) (c' y₂) = d' (f.toRiemannSphere y₂)
          simp [Function.comp, h_inv_y₂]
        rw [← hy₁_eq, ← hy₂_eq] at hF'_eq
        rw [hF'_at_y₁, hF'_at_y₂] at hF'_eq
        have h_inj_d : Set.InjOn d' d'.source := d'.injOn
        have hf_eq : f.toRiemannSphere y₁ = f.toRiemannSphere y₂ :=
          h_inj_d hy₁_fd' hy₂_fd' hF'_eq
        have hy_eq : y₁ = y₂ := hU_inj hy₁_U_outer hy₂_U_outer hf_eq
        rw [← hy₁_eq, ← hy₂_eq, hy_eq]
      · rintro ⟨U', hU'_nhds, hU'_inj⟩
        -- Pull back via c'.symm.
        -- Take U := c'.symm '' (U' ∩ c'.target) ∩ c'.source — but we want a nhd of x' on
        -- which f.toRiemannSphere is injective.
        -- Let U := c' ⁻¹' U' ∩ c'.source. This is open and contains x'.
        have hc'_cont : ContinuousOn c' c'.source := c'.continuousOn_toFun
        obtain ⟨U'_open, hU'_open_open, hU'_open_sub, hcx'_U'_open⟩ :
            ∃ U'_o, IsOpen U'_o ∧ U'_o ⊆ U' ∧ c' x' ∈ U'_o := by
          obtain ⟨W, hW_sub, hW_open, hxW⟩ := mem_nhds_iff.mp hU'_nhds
          exact ⟨W, hW_open, hW_sub, hxW⟩
        set U : Set X := c'.source ∩ c' ⁻¹' U'_open with hU_def
        have hU_open : IsOpen U :=
          hc'_cont.isOpen_inter_preimage c'.open_source hU'_open_open
        have hx'_U : x' ∈ U := ⟨hx'c', hcx'_U'_open⟩
        have hU_nhds : U ∈ 𝓝 x' := hU_open.mem_nhds hx'_U
        refine ⟨U, hU_nhds, ?_⟩
        intro y₁ hy₁ y₂ hy₂ hf_eq
        obtain ⟨hy₁_subc', hy₁_pre⟩ := hy₁
        obtain ⟨hy₂_subc', hy₂_pre⟩ := hy₂
        have hcy₁_U' : c' y₁ ∈ U' := hU'_open_sub hy₁_pre
        have hcy₂_U' : c' y₂ ∈ U' := hU'_open_sub hy₂_pre
        -- f.toRiemannSphere y₁ = f.toRiemannSphere y₂ ⇒ d' (f.toRiemannSphere y₁) = d' (f.toRiemannSphere y₂)
        -- ⇒ F' (c' y₁) = F' (c' y₂) ⇒ c' y₁ = c' y₂ (by InjOn F' U') ⇒ y₁ = y₂.
        have h_inv_y₁ : c'.symm (c' y₁) = y₁ := c'.left_inv hy₁_subc'
        have h_inv_y₂ : c'.symm (c' y₂) = y₂ := c'.left_inv hy₂_subc'
        have hF'_at_y₁ : F' (c' y₁) = d' (f.toRiemannSphere y₁) := by
          show (d' ∘ f.toRiemannSphere ∘ c'.symm) (c' y₁) = d' (f.toRiemannSphere y₁)
          simp [Function.comp, h_inv_y₁]
        have hF'_at_y₂ : F' (c' y₂) = d' (f.toRiemannSphere y₂) := by
          show (d' ∘ f.toRiemannSphere ∘ c'.symm) (c' y₂) = d' (f.toRiemannSphere y₂)
          simp [Function.comp, h_inv_y₂]
        have hF'_eq : F' (c' y₁) = F' (c' y₂) := by
          rw [hF'_at_y₁, hF'_at_y₂, hf_eq]
        have hcy_eq : c' y₁ = c' y₂ := hU'_inj hcy₁_U' hcy₂_U' hF'_eq
        have h_inj_c : Set.InjOn c' c'.source := c'.injOn
        exact h_inj_c hy₁_subc' hy₂_subc' hcy_eq
    -- Critical set membership at x' ↔ ¬ ∃ U' ∈ 𝓝 (c' x'), InjOn F' U'.
    have h_crit_iff_F' :
        (x' ∈ f.criticalSet) ↔ deriv F' (c' x') = 0 := by
      have h_iff_neg : (¬ ∃ U ∈ 𝓝 x', Set.InjOn f.toRiemannSphere U) ↔
          ¬ ∃ U' ∈ 𝓝 (c' x'), Set.InjOn F' U' := by
        constructor
        · intro h hex; exact h (h_inj_iff_x'.mpr hex)
        · intro h hex; exact h (h_inj_iff_x'.mp hex)
      have h_crit : (x' ∈ f.criticalSet) ↔ ¬ ∃ U ∈ 𝓝 x', Set.InjOn f.toRiemannSphere U :=
        Iff.rfl
      rw [h_crit, h_iff_neg, h_planar]
    -- Now translate `deriv F' (c' x') = 0` to `deriv F (c x') = 0`.
    -- F = d ∘ f̃ ∘ c.symm; F' = d' ∘ f̃ ∘ c'.symm.
    -- On a neighbourhood W of (c x'),
    --   F = (d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm).
    -- The chart-transition derivatives `deriv (c' ∘ c.symm) (c x')` and
    -- `deriv (d ∘ d'.symm) (d' (f̃ x'))` are nonzero, so
    -- `deriv F (c x') = (nonzero) * deriv F' (c' x') * (nonzero)`.
    -- Therefore deriv F (c x') = 0 ↔ deriv F' (c' x') = 0.
    -- Step (a): chart-transition pieces.
    have h_atlas_d : d ∈ atlas ℂ RiemannSphere := chart_mem_atlas ℂ (f.toRiemannSphere x)
    have h_atlas_d' : d' ∈ atlas ℂ RiemannSphere := chart_mem_atlas ℂ (f.toRiemannSphere x')
    -- Need d.source containing f̃ x' AND d'.source containing f̃ x'.
    have hfx'_d : f.toRiemannSphere x' ∈ d.source := hx'fd
    have hfx'_d' : f.toRiemannSphere x' ∈ d'.source := hfx'd'
    -- deriv (d ∘ d'.symm) at d' (f̃ x') is nonzero.
    have h_deriv_d_d' :
        deriv (d ∘ d'.symm) (d' (f.toRiemannSphere x')) ≠ 0 :=
      Jacobians.Discharge.deriv_chart_transition_of_isManifold_ne_zero
        h_atlas_d' h_atlas_d hfx'_d' hfx'_d
    -- deriv (c' ∘ c.symm) at c x' is nonzero.
    have h_deriv_c'_c : deriv (c' ∘ c.symm) (c x') ≠ 0 :=
      deriv_chartAt_transition_ne_zero x x' hx'c
    -- Step (b): F = (d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm) on a neighbourhood of (c x').
    -- Build the witness set W ⊆ ℂ such that c.symm maps W to V ∩ c.source.
    -- More concretely: at z ∈ W, we want
    --   F z = d (f̃ (c.symm z)) and F' (c' (c.symm z)) = d' (f̃ (c.symm z)),
    --   and d (...) = (d ∘ d'.symm) (d' ...) when d' (f̃ (c.symm z)) ∈ d'.source.
    -- Build W := c.target ∩ c.symm ⁻¹' (c'.source ∩ f̃ ⁻¹' d'.source).
    set W : Set ℂ :=
      c.target ∩ c.symm ⁻¹' (c'.source ∩ f.toRiemannSphere ⁻¹' d'.source) with hW_def
    have hW_open : IsOpen W := by
      refine c.isOpen_inter_preimage_symm ?_
      refine c'.open_source.inter ?_
      exact d'.open_source.preimage hf.continuous
    -- c x' ∈ W.
    have hc_x'_target : c x' ∈ c.target := c.map_source hx'c
    have hcx'_W : c x' ∈ W := by
      refine ⟨hc_x'_target, ?_⟩
      show c.symm (c x') ∈ c'.source ∩ f.toRiemannSphere ⁻¹' d'.source
      rw [c.left_inv hx'c]
      exact ⟨hx'c', hfx'd'⟩
    -- W ∈ 𝓝 (c x').
    have hW_nhds : W ∈ 𝓝 (c x') := hW_open.mem_nhds hcx'_W
    -- The composition equality on W.
    have h_F_eq_comp : ∀ z ∈ W,
        F z = ((d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)) z := by
      intro z hz
      obtain ⟨hz_target, hz_pre⟩ := hz
      have hz_pre' : c.symm z ∈ c'.source ∩ f.toRiemannSphere ⁻¹' d'.source := hz_pre
      obtain ⟨hcsymm_c'src, hcsymm_d'pre⟩ := hz_pre'
      -- f̃ (c.symm z) ∈ d'.source.
      have hfcsymm_d' : f.toRiemannSphere (c.symm z) ∈ d'.source := hcsymm_d'pre
      have h_inv_d' : d'.symm (d' (f.toRiemannSphere (c.symm z))) =
          f.toRiemannSphere (c.symm z) := d'.left_inv hfcsymm_d'
      have h_inv_c' : c'.symm (c' (c.symm z)) = c.symm z := c'.left_inv hcsymm_c'src
      show (d ∘ f.toRiemannSphere ∘ c.symm) z =
          ((d ∘ d'.symm) ∘ (d' ∘ f.toRiemannSphere ∘ c'.symm) ∘ (c' ∘ c.symm)) z
      simp [Function.comp, h_inv_c', h_inv_d']
    -- Eventual equality of F to the composition near (c x').
    have h_F_evEq : F =ᶠ[𝓝 (c x')] ((d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)) :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨W, hW_nhds, h_F_eq_comp⟩
    -- Differentiability at the relevant points (for chain rule).
    have h_atlas_x : chartAt ℂ x ∈ atlas ℂ X := chart_mem_atlas ℂ x
    have h_atlas_x' : chartAt ℂ x' ∈ atlas ℂ X := chart_mem_atlas ℂ x'
    have h_an_c'_c : AnalyticAt ℂ (c' ∘ c.symm) (c x') :=
      Jacobians.Discharge.analyticAt_chart_transition_of_isManifold
        h_atlas_x h_atlas_x' hx'c hx'c'
    have h_an_d_d' : AnalyticAt ℂ (d ∘ d'.symm) (d' (f.toRiemannSphere x')) :=
      Jacobians.Discharge.analyticAt_chart_transition_of_isManifold
        h_atlas_d' h_atlas_d hfx'_d' hfx'_d
    have h_diff_c'_c : DifferentiableAt ℂ (c' ∘ c.symm) (c x') :=
      h_an_c'_c.differentiableAt
    have h_diff_F' : DifferentiableAt ℂ F' ((c' ∘ c.symm) (c x')) := by
      have h_pt : (c' ∘ c.symm) (c x') = c' x' := by
        show c' (c.symm (c x')) = c' x'
        rw [c.left_inv hx'c]
      rw [h_pt]; exact hF'A_at_x'.differentiableAt
    have h_diff_d_d' : DifferentiableAt ℂ (d ∘ d'.symm) (F' ((c' ∘ c.symm) (c x'))) := by
      have h_pt_F' : F' ((c' ∘ c.symm) (c x')) = d' (f.toRiemannSphere x') := by
        have h_pt : (c' ∘ c.symm) (c x') = c' x' := by
          show c' (c.symm (c x')) = c' x'
          rw [c.left_inv hx'c]
        rw [h_pt]; exact hF'cx'
      rw [h_pt_F']; exact h_an_d_d'.differentiableAt
    -- Chain rule on the composition.
    have h_pt_inner : (c' ∘ c.symm) (c x') = c' x' := by
      show c' (c.symm (c x')) = c' x'
      rw [c.left_inv hx'c]
    have h_pt_F' : F' ((c' ∘ c.symm) (c x')) = d' (f.toRiemannSphere x') := by
      rw [h_pt_inner]; exact hF'cx'
    have h_chain_inner :
        deriv (F' ∘ (c' ∘ c.symm)) (c x') =
          deriv F' ((c' ∘ c.symm) (c x')) * deriv (c' ∘ c.symm) (c x') :=
      deriv_comp (c x') h_diff_F' h_diff_c'_c
    have h_diff_inner : DifferentiableAt ℂ (F' ∘ (c' ∘ c.symm)) (c x') :=
      h_diff_F'.comp (c x') h_diff_c'_c
    have h_chain_outer :
        deriv ((d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)) (c x') =
          deriv (d ∘ d'.symm) ((F' ∘ (c' ∘ c.symm)) (c x'))
            * deriv (F' ∘ (c' ∘ c.symm)) (c x') :=
      deriv_comp (c x') h_diff_d_d' h_diff_inner
    -- LHS via EventuallyEq is `deriv F (c x')`.
    have h_F_deriv :
        deriv F (c x') = deriv ((d ∘ d'.symm) ∘ F' ∘ (c' ∘ c.symm)) (c x') :=
      h_F_evEq.deriv_eq
    -- Combine.
    have h_pt_inner_comp : (F' ∘ (c' ∘ c.symm)) (c x') = F' (c' x') := by
      show F' ((c' ∘ c.symm) (c x')) = F' (c' x')
      rw [h_pt_inner]
    have h_F_deriv_factored :
        deriv F (c x') =
          deriv (d ∘ d'.symm) (d' (f.toRiemannSphere x'))
            * (deriv F' (c' x') * deriv (c' ∘ c.symm) (c x')) := by
      rw [h_F_deriv, h_chain_outer, h_chain_inner, h_pt_inner_comp, h_pt_inner]
      -- Goal now: deriv (d ∘ d'.symm) (F' (c' x')) * (deriv F' (c' x') * ...) = ...
      rw [hF'cx']
    -- Conclude: deriv F (c x') = 0 ↔ deriv F' (c' x') = 0.
    have h_deriv_iff : deriv F (c x') = 0 ↔ deriv F' (c' x') = 0 := by
      rw [h_F_deriv_factored]
      constructor
      · intro h
        rcases mul_eq_zero.mp h with h1 | h2
        · exact absurd h1 h_deriv_d_d'
        rcases mul_eq_zero.mp h2 with h3 | h4
        · exact h3
        · exact absurd h4 h_deriv_c'_c
      · intro h
        rw [h, zero_mul, mul_zero]
    rw [h_crit_iff_F']
    exact h_deriv_iff.symm
  exact {
    V := V
    hV_open := hV_open
    hxV := hxV
    hV_subS := hV_subS
    F := F
    hFne := hFne
    hCompat := hCompat
  }

-- (No standalone `derivBridgeData_of_meromorphicNonzero` corollary is shipped
-- here. Downstream consumers compose `localDerivCompatibilityData_of_meromorphicNonzero`
-- with `derivBridgeData_of_localCompatibility` from `DerivBridgeFromNonConstant.lean`
-- by supplying the analyticity at the basepoint via ZZ24's
-- `contMDiff_omega_analyticAt_chart_pullback`, applied to the *F-field of the
-- supplied `LocalDerivCompatibilityData`*. The structure-projection through
-- this `def` does not reduce automatically; in practice consumers can call
-- the supplier with `[F := <literal pullback>]` directly via the
-- `derivBridgeData_of_localCompatibility_literalPullback` constructor.)

end Manifold

end Jacobians.Discharge

end

end
