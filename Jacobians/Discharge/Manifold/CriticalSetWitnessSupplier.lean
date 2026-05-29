/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.Discharge.Manifold.CriticalSetDefinition
import Jacobians.Discharge.Manifold.CriticalSetDerivBridge

set_option autoImplicit true


/-! # Supplier for `CriticalChartPullbackData` (ZZ101)

This file narrows ZZ100's R-MN residual by providing a *per-point*
constructor for `CriticalChartPullbackData f.toRiemannSphere f.criticalSet x`
out of a uniform chart-bridge bundle `CriticalChartBridgeBundle f x` that
records, near `x`:

* a chart `eX` at `x` and an open neighbourhood `V ⊆ eX.source` containing
  `x`, with `eX` mapping `V` to an open `W ⊆ ℂ`;
* a function `F' : ℂ → ℂ` analytic at `eX x` and not eventually zero near
  `eX x`;
* the pointwise compatibility
  `∀ x' ∈ V, x' ∈ f.criticalSet ↔ F' (eX x') = 0`.

Given such a bundle at every critical point, the constructor
`criticalChartPullbackData_of_bridge` produces the witness consumed by
ZZ44's `criticalSet_finite_of_chart_pullback`. The construction is purely
bookkeeping (restrict `eX` to a homeomorphism `V → W`, repackage `F'`).

## Status — what is and isn't closed

This file **does not** unconditionally discharge R-MN. The remaining gap
is: building `CriticalChartBridgeBundle f x` from the underlying
`MeromorphicNonzero` data, which requires
* selecting target charts of `OnePoint ℂ` valid on the *image* of a
  source-chart neighbourhood (regular branch: the `some`-chart suffices
  on a sufficiently small neighbourhood; pole branch: requires the
  `∞`-chart of `OnePoint ℂ`),
* invoking ZZ24 to upgrade `ContMDiffAt … ω` to `AnalyticAt ℂ` for the
  resulting chart pullback,
* exhibiting "not eventually zero" of `deriv F` from the
  `mmeromorphicOrderAt ≠ ⊤` field of `MeromorphicNonzero` (combined with
  the order≥1 finiteness of `F - F z₀` and the planar bridge
  `notInjOn_iff_deriv_zero_of_analytic_of_order` from ZZ99),
* checking the pointwise compatibility on a uniform neighbourhood (not
  just at the basepoint), which requires the order finiteness to hold
  at every nearby chart image — a chart-pullback meromorphy fact that is
  *pointwise* true via `MeromorphicNonzero.meromorphic` but needs to be
  threaded through `ChartBridgePackage` at every point.

Each of these is a separable sub-chip. The supplier here factors the
construction so that those sub-chips can land independently and feed
into the final witness without re-architecting the file structure.

No `sorry`. No `axiom`. No signature changes outside this new file. -/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace Jacobians.Discharge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ## Per-point chart bridge bundle

The minimal data needed to assemble `CriticalChartPullbackData` for the map
`f.toRiemannSphere` at the point `x`.

The bundle is *agnostic* to whether `x` is a regular point or a pole — the
chart `eX` is the manifold's `chartAt ℂ x` (the source-chart of `X`), and
`F'` is whatever analytic chart-pullback function detects criticality on
the chosen neighbourhood. -/
structure CriticalChartBridgeBundle (f : MeromorphicNonzero X) (x : X) where
  /-- An open neighbourhood of `x`, contained in the source-chart of `X`
  at `x`. -/
  V : Set X
  hV_open : IsOpen V
  hxV : x ∈ V
  hV_subS : V ⊆ (chartAt ℂ x).source
  /-- The chart-pullback derivative-style function. -/
  F' : ℂ → ℂ
  /-- Analyticity of `F'` at the chart image of `x`. -/
  hF'A : AnalyticAt ℂ F' ((chartAt ℂ x) x)
  /-- `F'` is not identically zero in any neighbourhood of `(chartAt ℂ x) x`. -/
  hF'ne : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x), F' z = 0
  /-- Compatibility on `V`: criticality at `x'` ↔ `F'` vanishes at the chart
  image of `x'`. -/
  hCompat :
    ∀ x' ∈ V, (x' ∈ f.criticalSet) ↔ F' ((chartAt ℂ x) x') = 0

/-! ## Constructor: bundle ⇒ `CriticalChartPullbackData` -/

/-- **Build `CriticalChartPullbackData` from a chart bridge bundle.**

Given a `CriticalChartBridgeBundle f x`, restrict the chart `chartAt ℂ x`
to a homeomorphism `V → W := (chartAt ℂ x) '' V` and repackage the
bundle's `F'` and compatibility data into the structure consumed by
`criticalSet_finite_of_chart_pullback`. -/
noncomputable def criticalChartPullbackData_of_bridge
    (f : MeromorphicNonzero X) {x : X}
    (B : CriticalChartBridgeBundle f x) :
    ContMDiff.Degree.CriticalChartPullbackData
      f.toRiemannSphere f.criticalSet x := by
  classical
  -- Source-chart abbreviation.
  set eX : OpenPartialHomeomorph X ℂ := chartAt ℂ x with heX_def
  -- Image of `V` under `eX`, with openness via the open-embedding restricted form.
  set W : Set ℂ := eX '' B.V with hW_def
  have hxS : x ∈ eX.source := mem_chart_source ℂ x
  have hW_open : IsOpen W := by
    have hWeq : W = eX.target ∩ eX.symm ⁻¹' B.V := by
      ext z
      constructor
      · rintro ⟨v, hvV, rfl⟩
        refine ⟨eX.map_source (B.hV_subS hvV), ?_⟩
        show eX.symm (eX v) ∈ B.V
        rw [eX.left_inv (B.hV_subS hvV)]
        exact hvV
      · rintro ⟨hz_target, hz_pre⟩
        refine ⟨eX.symm z, hz_pre, ?_⟩
        exact eX.right_inv hz_target
    rw [hWeq]
    exact eX.isOpen_inter_preimage_symm B.hV_open
  -- Chart image basepoint.
  set z₀ : ℂ := eX x with hz₀_def
  have hz₀W : z₀ ∈ W := ⟨x, B.hxV, rfl⟩
  -- The restricted homeomorphism `φ : V → W`.
  let φ : B.V → W := fun v => ⟨eX v.1, mem_image_of_mem _ v.2⟩
  -- Continuity of `φ`.
  have hφ_cont : Continuous φ := by
    apply Continuous.subtype_mk
    have h_co : ContinuousOn eX eX.source := eX.continuousOn_toFun
    have h_co_V : ContinuousOn eX B.V := h_co.mono B.hV_subS
    exact continuousOn_iff_continuous_restrict.mp h_co_V
  -- Bijectivity of `φ`.
  have hφ_bij : Function.Bijective φ := by
    refine ⟨?_, ?_⟩
    · intro v₁ v₂ hv
      have h_eq : eX v₁.1 = eX v₂.1 := by
        have := congrArg Subtype.val hv
        simpa using this
      have hi := eX.injOn (B.hV_subS v₁.2) (B.hV_subS v₂.2) h_eq
      exact Subtype.ext hi
    · rintro ⟨w, hw⟩
      obtain ⟨v', hv'V, hv'eq⟩ := hw
      refine ⟨⟨v', hv'V⟩, ?_⟩
      exact Subtype.ext hv'eq
  -- `(φ ⟨x, hxV⟩ : ℂ) = z₀` reduces to `eX x = z₀` (definitional).
  have hz₀_eq : (φ ⟨x, B.hxV⟩ : ℂ) = z₀ := rfl
  -- Compatibility: re-package via the bundle's `hCompat`.
  have hCompat :
      ∀ x' : B.V, x'.1 ∈ f.criticalSet ↔ B.F' (φ x') = 0 := by
    intro x'
    have h := B.hCompat x'.1 x'.2
    -- `(φ x' : ℂ) = eX x'.1` by construction.
    have h_eq : (φ x' : ℂ) = eX x'.1 := rfl
    rw [h_eq]; exact h
  -- Assemble.
  exact
    { V := B.V
      hV_open := B.hV_open
      hxV := B.hxV
      W := W
      hW_open := hW_open
      φ := φ
      hφ := hφ_cont
      hφ_inv := hφ_bij
      z₀ := z₀
      hz₀ := hz₀_eq
      hz₀W := hz₀W
      F' := B.F'
      hF'A := B.hF'A
      hF'ne := B.hF'ne
      hCompat := hCompat }

/-! ## Globalised: per-point bundles ⇒ chart-pullback data at every critical point -/

/-- **Globalised supplier.** If a `CriticalChartBridgeBundle f x` exists at
every `x ∈ f.criticalSet`, then `CriticalChartPullbackData ... x` exists at
every such point. This is the per-point half of `CriticalSetWitness`; the
remaining half is `IsClosed f.criticalSet` (residual R-Closed in ZZ100). -/
noncomputable def criticalChartPullbackData_of_bridge_global
    (f : MeromorphicNonzero X)
    (h : ∀ x ∈ f.criticalSet, CriticalChartBridgeBundle f x) :
    ∀ x ∈ f.criticalSet,
      ContMDiff.Degree.CriticalChartPullbackData
        f.toRiemannSphere f.criticalSet x :=
  fun x hx => criticalChartPullbackData_of_bridge f (h x hx)

/-- **Witness from bridge bundles + closedness.** Combine the per-point
bundle supplier with R-Closed to produce a `CriticalSetWitness`. -/
noncomputable def criticalSetWitness_of_bridge
    (f : MeromorphicNonzero X)
    (h_closed : IsClosed f.criticalSet)
    (h : ∀ x ∈ f.criticalSet, CriticalChartBridgeBundle f x) :
    CriticalSetWitness f where
  closed := h_closed
  chart_data := criticalChartPullbackData_of_bridge_global f h

end MeromorphicNonzero

end Jacobians.Discharge

end

end
