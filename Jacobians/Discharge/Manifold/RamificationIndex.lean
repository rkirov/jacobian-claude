/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

set_option autoImplicit true

/-! # Manifold-side ramification index (ZZ179 starter)

Definition of `manifoldRamificationIndex f x : ℕ` for `f : X → Y` between
charted spaces modelled on `ℂ` and `x : X`. The value is the order of
vanishing of the chart-pullback `F z = (chartAt ℂ (f x)) ∘ f ∘
(chartAt ℂ x).symm` minus `F z₀` at `z₀ = (chartAt ℂ x) x`, viewed as a
natural number (`⊤` from the constant case maps to `0` via `ENat.toNat`).

This is the seed for the multiplicity-weighted divisor pullback laid out
in `HANDOFF_ZZ177_PULLBACK_BLOCKER.md`. The classical fact
`∑_{x ∈ f ⁻¹{y}} manifoldRamificationIndex f x = degreeFiber f hf` (for
non-constant `f` on the regular locus) is the single named obligation
that the weighted-fibre-sum descent will consume.

This starter file ships the definition and an unfold lemma. Properties
(invariance under chart change, identity = 1, sum-equals-degree on
regular fibres) are follow-up chips.

No `sorry`, no `axiom`. -/

@[expose] public section

open scoped Topology

namespace Jacobians.Discharge

namespace Manifold

universe u v

/-- **Manifold-side ramification index** of `f : X → Y` at `x : X`.

Defined as the order of vanishing (as a `ℕ`, via `ENat.toNat`) of the
chart-pullback `F z := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm`
minus `F z₀` at `z₀ := (chartAt ℂ x) x`.

For `f = id`, this returns `1` (the chart-pullback reduces to the
identity locally, with order-1 vanishing). For `f` constant on a
neighbourhood of `x`, the chart-pullback minus its value vanishes
identically and `analyticOrderAt = ⊤`, mapped to `0`. For
`f(z) = z^k` (in a chart) at the branch point, returns `k`. -/
noncomputable def manifoldRamificationIndex
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X → Y) (x : X) : ℕ :=
  let z₀ : ℂ := (chartAt ℂ x) x
  let F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm
  (analyticOrderAt (fun z => F z - F z₀) z₀).toNat

/-- Unfold lemma: the ramification index equals the `ENat.toNat` of the
analytic order of the chart-pullback shift. -/
lemma manifoldRamificationIndex_eq
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X → Y) (x : X) :
    manifoldRamificationIndex f x =
      (analyticOrderAt
        (fun z =>
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z -
          ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x))
        ((chartAt ℂ x) x)).toNat := rfl

end Manifold

end Jacobians.Discharge
