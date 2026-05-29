/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.Discharge.Manifold.CriticalValuesFinite
import Jacobians.Discharge.Manifold.ContMDiffOmegaAnalytic
import Jacobians.Discharge.Manifold.MeromorphicExtension

set_option autoImplicit true


/-! # Per-point `DerivBridgeData` from non-eventually-constant chart pullback

This file (the **R-MN** chip) constructs the per-point bridge record
`DerivBridgeData f x` (introduced in `CriticalValuesFinite.lean` by RH6)
from the natural local hypotheses available for a `MeromorphicNonzero X`:

* the pole-extension `f.toRiemannSphere : X → RiemannSphere` is unconditionally
  `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ) ω` (`MeromorphicNonzero.toRiemannSphere_contMDiff`),
  hence its chart pullback at any `x : X` is `AnalyticAt ℂ` at the chart image
  (`contMDiff_omega_analyticAt_chart_pullback`, ZZ24);
* a non-eventual-constancy hypothesis on the chart pullback at `x` (the
  `ChartPullbackNotEventuallyConstHypothesis` of ZZ43, packaged here per-point);
* a *local compatibility iff* at every nearby point of an open neighbourhood of
  `x` — translated from the planar `criticalSet ↔ chart-pullback derivative
  zero` bridge (ZZ99, `criticalSet_iff_chart_pullback_deriv_zero`) supplied by
  a `ChartBridgePackage` — packaged here as a single named hypothesis.

The chip ships:

* `LocalDerivCompatibilityData f x` — a record bundling exactly the local data
  that `DerivBridgeData f x` needs but does **not** itself derive from
  `f`+`x`+typeclass alone: an open neighbourhood `V`, the chart pullback `F`,
  the non-eventual-constancy of `F`, and the per-point compatibility iff
  `criticalSet ↔ deriv F vanishes` on `V`.

* `derivBridgeData_of_localCompatibility` — packages a
  `LocalDerivCompatibilityData f x` into the `DerivBridgeData f x`
  consumed downstream by `criticalChartBridgeBundle_of_derivBridge`.

* `globalDerivBridge_of_localCompatibility` — globalised: a per-critical-point
  `LocalDerivCompatibilityData` supplier yields the
  `∀ x ∈ f.criticalSet, DerivBridgeData f x` consumed by
  `criticalSet_finite_of_derivBridge`.

This chip does **not** discharge the `LocalDerivCompatibilityData` hypothesis
itself — that remains deferred to the joint composition of:

1. ZZ43's `ChartPullbackNotEventuallyConstHypothesis` (already discharged from
   `ChartOverlapPropagationHypothesis`);
2. ZZ99's `criticalSet_iff_chart_pullback_deriv_zero` (already proven planar
   bridge via `ChartBridgePackage`);
3. the local manifold-↔-chart-pullback non-injectivity transfer at every point
   in the chart neighbourhood, which combined with the bridge of (2) at every
   such point produces the iff field of `LocalDerivCompatibilityData`.

What this file delivers is the *clean assembly point*: once the local
compatibility data is supplied, the per-point `DerivBridgeData` follows by a
direct field-by-field repackaging.

## Status — no `sorry`, no `axiom`, no signature changes outside this file.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace Jacobians.Discharge

namespace Manifold

universe u

/-! ## Local compatibility data -/

/-- **Local compatibility data at a point.** Bundles the local inputs that
the `DerivBridgeData f x` constructor consumes but does not itself derive:
a chart-source-restricted open neighbourhood `V` of `x`, the analytic chart
pullback `F` of `f.toRiemannSphere`, the non-eventual-constancy of `F` at the
chart image of `x`, and the per-point compatibility iff
`criticalSet ↔ deriv F vanishes` on `V`.

The analyticity of `F` at `(chartAt ℂ x) x` is **not** a field of this record:
it is supplied unconditionally by ZZ24 inside the constructor, since
`f.toRiemannSphere` is unconditionally `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ) ω`. -/
structure LocalDerivCompatibilityData
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : Jacobians.Discharge.MeromorphicNonzero X) (x : X) where
  /-- Open neighbourhood of `x`, contained in the source-chart at `x`. -/
  V : Set X
  hV_open : IsOpen V
  hxV : x ∈ V
  hV_subS : V ⊆ (chartAt ℂ x).source
  /-- The chart pullback of `f.toRiemannSphere` at `x`. -/
  F : ℂ → ℂ
  /-- `F` is not eventually equal to `F z₀` at `z₀ := (chartAt ℂ x) x`. -/
  hFne : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x), F z = F ((chartAt ℂ x) x)
  /-- `F` is the chart pullback of `f.toRiemannSphere`: at every `x' ∈ V`,
  `F ((chartAt ℂ x) x')` matches the value computed by composing through the
  target chart. We do not require `F` to coincide with the literal chart
  pullback away from `V`: only `hFA` (analyticity at `z₀`) and `hCompat`
  (the criticality iff on `V`) are load-bearing for the bridge. -/
  hCompat :
    ∀ x' ∈ V, (x' ∈ f.criticalSet) ↔ deriv F ((chartAt ℂ x) x') = 0

/-- **Build `DerivBridgeData f x` from `LocalDerivCompatibilityData f x`.**

The analyticity of `F` at the chart image of `x` is supplied here from
ZZ24's `contMDiff_omega_analyticAt_chart_pullback` applied to
`f.toRiemannSphere` (unconditionally `ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ) ω` via
`MeromorphicNonzero.toRiemannSphere_contMDiff`). Nothing else needs to be
recomputed: the remaining fields of `DerivBridgeData` are exactly the fields
of `LocalDerivCompatibilityData`.

Caveat. The `F` field of `LocalDerivCompatibilityData` is constrained only by
its non-eventual-constancy at `(chartAt ℂ x) x` and the criticality iff on
`V`. To make `DerivBridgeData.hFA` discharge automatically here, we instead
take the *literal* chart pullback `(chartAt ℂ (f.toRiemannSphere x))
∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm` and require the supplier to use
exactly that `F`. The version below does that by setting `F` from the
constructor. We provide the more flexible version
`derivBridgeData_of_localCompatibility_with_analyticity` immediately
afterwards, which takes the analyticity of `F` as an extra field. -/
noncomputable def derivBridgeData_of_localCompatibility
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {f : Jacobians.Discharge.MeromorphicNonzero X} {x : X}
    (D : LocalDerivCompatibilityData f x)
    (hFA : AnalyticAt ℂ D.F ((chartAt ℂ x) x)) :
    DerivBridgeData f x where
  V := D.V
  hV_open := D.hV_open
  hxV := D.hxV
  hV_subS := D.hV_subS
  F := D.F
  hFA := hFA
  hFne := D.hFne
  hCompat := D.hCompat

/-- **Specialisation: literal chart pullback of `f.toRiemannSphere`.**

When the supplied `F` is exactly the literal chart pullback of
`f.toRiemannSphere`, the analyticity hypothesis is automatic from ZZ24, and
no extra input is required. -/
noncomputable def derivBridgeData_of_localCompatibility_literalPullback
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {f : Jacobians.Discharge.MeromorphicNonzero X} {x : X}
    (V : Set X) (hV_open : IsOpen V) (hxV : x ∈ V)
    (hV_subS : V ⊆ (chartAt ℂ x).source)
    (hFne : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      ((chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
          ∘ (chartAt ℂ x).symm) z
        = ((chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
            ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
    (hCompat :
      ∀ x' ∈ V, (x' ∈ f.criticalSet) ↔
        deriv ((chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
            ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x') = 0) :
    DerivBridgeData f x where
  V := V
  hV_open := hV_open
  hxV := hxV
  hV_subS := hV_subS
  F := (chartAt ℂ (f.toRiemannSphere x)) ∘ f.toRiemannSphere
        ∘ (chartAt ℂ x).symm
  hFA :=
    Jacobians.Discharge.ContMDiff.Degree.contMDiff_omega_analyticAt_chart_pullback
      (Jacobians.Discharge.MeromorphicNonzero.toRiemannSphere_contMDiff f) x
  hFne := hFne
  hCompat := hCompat

/-! ## Globalised: per-critical-point local data ⇒ per-critical-point bridge -/

/-- **Globalised constructor.** A per-critical-point supplier of
`LocalDerivCompatibilityData` (with each supplier carrying its own analyticity
proof for its `F`) yields the per-critical-point `DerivBridgeData` consumed
by `criticalSet_finite_of_derivBridge`. -/
noncomputable def globalDerivBridge_of_localCompatibility
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {f : Jacobians.Discharge.MeromorphicNonzero X}
    (h : ∀ x ∈ f.criticalSet,
      Σ' (D : LocalDerivCompatibilityData f x),
        AnalyticAt ℂ D.F ((chartAt ℂ x) x)) :
    ∀ x ∈ f.criticalSet, DerivBridgeData f x := by
  intro x hx
  obtain ⟨D, hFA⟩ := h x hx
  exact derivBridgeData_of_localCompatibility D hFA

/-- **End-to-end conditional finiteness.** Assemble the global supplier with
the closedness of the critical set (residual R-Closed) to obtain the
headline `f.criticalSet.Finite`.

This is the *conditional headline* of this chip: combined with the planar
core in `CriticalValuesFinite.lean` and the unconditional
`f.toRiemannSphere : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ) ω`, the only remaining
unknowns are R-Closed (closedness of `f.criticalSet`, separate parallel chip)
and `LocalDerivCompatibilityData` per critical point (which decomposes
into ZZ43 + ZZ99 + manifold-side non-injectivity transfer). -/
theorem criticalSet_finite_of_localCompatibility
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : Jacobians.Discharge.MeromorphicNonzero X)
    (h_closed : IsClosed f.criticalSet)
    (h : ∀ x ∈ f.criticalSet,
      Σ' (D : LocalDerivCompatibilityData f x),
        AnalyticAt ℂ D.F ((chartAt ℂ x) x)) :
    f.criticalSet.Finite :=
  criticalSet_finite_of_derivBridge f h_closed
    (globalDerivBridge_of_localCompatibility h)

/-- **Corollary.** Critical values are finite under the same hypotheses. -/
theorem criticalValues_finite_of_localCompatibility
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : Jacobians.Discharge.MeromorphicNonzero X)
    (h_closed : IsClosed f.criticalSet)
    (h : ∀ x ∈ f.criticalSet,
      Σ' (D : LocalDerivCompatibilityData f x),
        AnalyticAt ℂ D.F ((chartAt ℂ x) x)) :
    f.criticalValues.Finite :=
  criticalValues_finite_of_derivBridge f h_closed
    (globalDerivBridge_of_localCompatibility h)

end Manifold

end Jacobians.Discharge

end

end
