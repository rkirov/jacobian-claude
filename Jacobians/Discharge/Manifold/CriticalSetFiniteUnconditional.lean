/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.Discharge.Manifold.CriticalSetDefinition
import Jacobians.Discharge.Manifold.CriticalSetDerivBridge

set_option autoImplicit true


/-! # Finiteness of the critical set / critical values (ZZ100)

This file delivers the headline finiteness theorems for the critical set
and critical values of `f.toRiemannSphere : X → RiemannSphere` for a
non-constant `f : MeromorphicNonzero X`, given the chart-pullback
witness data supplied at every critical point.

## What is delivered

* `nonDegenerateCriticalSet f` — the subset of `f.criticalSet` where a
  `CriticalChartPullbackData` chart-pullback witness is available. By
  ZZ44 (`criticalSet_isDiscrete_of_chart_pullback`), this set is
  *discrete*, and if additionally closed in `X` (e.g. as a subset of
  a closed `f.criticalSet`), it is finite by compactness.

* `criticalSet_finite_of_nonconstant_of_witness` — the headline
  theorem: for `f : MeromorphicNonzero X` and a
  `CriticalSetWitness f` supplied (closedness of `f.criticalSet` plus
  per-point chart-pullback witnesses), the critical set is finite.
  This is just `criticalSet_finite_of_witness` re-exposed under the
  "non-constant" name; we package it for the downstream `Degree.lean`
  hand-off.

* `criticalValues_finite_of_nonconstant_of_witness` — the immediate
  image-finiteness corollary.

* `criticalSet_finite_on_nonDegenerate` — finiteness on the
  non-degenerate sub-set, under closedness *of that sub-set*. This
  shows the strategy is sound on the part of `criticalSet` we can
  certify; the remaining residual is whether every `x ∈ criticalSet`
  is non-degenerate, which is what the "non-constant ⇒ chart-pullback
  derivative not eventually zero" argument supplies in the classical
  proof.

## Residuals (named, not hidden)

The unconditional statement
`∀ f : MeromorphicNonzero X, ¬ IsConstantMap f.toRiemannSphere →
  f.criticalSet.Finite` requires producing, for every
`x ∈ f.criticalSet`, a `CriticalChartPullbackData` witness whose chart
pullback is the *specific* chart-pullback of `f.toRiemannSphere`. The
present infrastructure (`CriticalSetDerivBridge`, ZZ99, planar side;
`ContMDiffOmegaAnalytic`, ZZ24, manifold side; `MeromorphicAt`
`mmeromorphicOrderAt` chart-independence, manifold side) supplies all
the pieces needed for the construction *up to* one named residual:

* **(Residual R-MN)** A construction
  `MeromorphicNonzero.criticalChartPullbackData :
    ∀ (f : MeromorphicNonzero X), ¬ IsConstantMap f.toRiemannSphere →
    ∀ x ∈ f.criticalSet,
      CriticalChartPullbackData f.toRiemannSphere f.criticalSet x`
  that builds the witness from the underlying chart-pullback meromorphic
  function. This requires (i) selecting a target chart of `RiemannSphere`
  containing `f.toRiemannSphere x`, (ii) reading off the chart-pullback
  via `MeromorphicAt`, (iii) bridging `mmeromorphicOrderAt` finiteness to
  "chart-pullback derivative not eventually zero" via the planar
  bridge `notInjOn_iff_deriv_zero_of_analytic_of_order` (ZZ99).

* **(Residual R-Closed)** Closedness `IsClosed f.criticalSet`. The
  natural argument is via the openness of "`f̃` is locally injective at
  `x`" (a `Filter`-eventual property, hence open). This is independent
  of the per-point witness package.

The headline theorem `criticalSet_finite_of_nonconstant_of_witness`
takes the `CriticalSetWitness` data directly, so it is unconditional
once the witness is supplied.

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

/-! ## Non-degenerate critical set: where a chart-pullback witness exists -/

/-- **Non-degenerate critical set.** Subset of `f.criticalSet`
consisting of points where a `CriticalChartPullbackData` chart-pullback
witness exists. This is the sub-set on which discreteness (and hence,
under closedness + compactness of `X`, finiteness) is unconditionally
provable from the present infrastructure. -/
def nonDegenerateCriticalSet (f : MeromorphicNonzero X) : Set X :=
  { x ∈ f.criticalSet | Nonempty (
      ContMDiff.Owed.degree.CriticalChartPullbackData
        f.toRiemannSphere f.criticalSet x) }

/-- The non-degenerate critical set is contained in the critical set. -/
lemma nonDegenerateCriticalSet_subset (f : MeromorphicNonzero X) :
    f.nonDegenerateCriticalSet ⊆ f.criticalSet := by
  intro x hx
  exact hx.1

/-! ## Headline finiteness theorems (under the witness package) -/

/-- **Headline: critical set finite for non-constant `f`, given the
witness package.**

For `f : MeromorphicNonzero X` on a compact connected complex
1-manifold `X`, supplied with a `CriticalSetWitness f` (the closedness
of `f.criticalSet` plus per-point chart-pullback witnesses), the
critical set `f.criticalSet` is finite.

The non-constancy hypothesis on `f.toRiemannSphere` is included for
documentation: the witness package is what *encodes* non-constancy in
analytic terms (a chart-pullback derivative not eventually zero is
exactly the local non-constancy condition). The proof itself is just
`criticalSet_finite_of_witness`. -/
theorem criticalSet_finite_of_nonconstant_of_witness
    (f : MeromorphicNonzero X)
    (_hnc : ¬ Jacobians.Discharge.IsConstantMap f.toRiemannSphere)
    (w : CriticalSetWitness f) :
    f.criticalSet.Finite :=
  criticalSet_finite_of_witness f w

/-- **Headline: critical values finite for non-constant `f`, given the
witness package.** Image-finiteness corollary. -/
theorem criticalValues_finite_of_nonconstant_of_witness
    (f : MeromorphicNonzero X)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap f.toRiemannSphere)
    (w : CriticalSetWitness f) :
    f.criticalValues.Finite :=
  criticalValues_finite_of_criticalSet_finite f
    (criticalSet_finite_of_nonconstant_of_witness f hnc w)

/-! ## Finiteness on the non-degenerate sub-set (no witness package
required at the global level) -/

/-- **Non-degenerate sub-set is `IsDiscrete` from per-point witnesses.**
Specialised form of `criticalSet_isDiscrete_of_chart_pullback` on the
sub-set; uses Choice to extract the per-point witness from the
`Nonempty` field of `nonDegenerateCriticalSet`.

The statement is about discreteness as a *subset* of `f.criticalSet`
(via the existing `CriticalChartPullbackData ... f.criticalSet x`
witness), which is what the downstream `criticalSet_finite_of_isDiscrete_of_isClosed`
lemma consumes. -/
noncomputable def nonDegenerateCriticalSet_chartPullbackData
    (f : MeromorphicNonzero X) :
    ∀ x ∈ f.nonDegenerateCriticalSet,
      ContMDiff.Owed.degree.CriticalChartPullbackData
        f.toRiemannSphere f.criticalSet x := by
  classical
  intro x hx
  exact (hx.2).some

/-- **Finiteness on the non-degenerate sub-set, given closedness.**

Under closedness of `f.nonDegenerateCriticalSet` in `X`, this set is
discrete (per `nonDegenerateCriticalSet_chartPullbackData` applied to
the constant set `f.criticalSet ⊇ f.nonDegenerateCriticalSet`, *but*
the discreteness lemma `criticalSet_isDiscrete_of_chart_pullback`
expects a witness *of the same set*, i.e. with second argument equal to
the set whose discreteness we want).

We work around this by supplying chart witnesses directly for
`f.nonDegenerateCriticalSet`: each `x ∈ f.nonDegenerateCriticalSet` has
a `CriticalChartPullbackData f.toRiemannSphere f.criticalSet x`; the
compatibility predicate `x' ∈ f.criticalSet ↔ F' (φ x') = 0` then
implies `x' ∈ f.nonDegenerateCriticalSet → F' (φ x') = 0` (one direction
suffices for the isolation argument). The full reverse direction would
require building a witness at every point in the chart-image; we get
discreteness *of the larger set* `f.criticalSet ∩ V` (V the chart
neighbourhood), which still isolates `x` in `f.nonDegenerateCriticalSet`.

The cleanest route is therefore: per-point isolation of `x` in
`f.criticalSet` (already provided by
`criticalSet_pointIsolated_via_chart_pullback`) gives a fortiori
isolation in the sub-set `f.nonDegenerateCriticalSet`. -/
lemma criticalSet_finite_on_nonDegenerate
    (f : MeromorphicNonzero X)
    (h_closed : IsClosed f.nonDegenerateCriticalSet) :
    f.nonDegenerateCriticalSet.Finite := by
  classical
  -- Per-point: each `x ∈ nonDegenerateCriticalSet` is isolated in
  -- `f.criticalSet`, hence isolated in the sub-set.
  have h_disc : IsDiscrete f.nonDegenerateCriticalSet := by
    rw [isDiscrete_iff_forall_exists_isOpen]
    intro x hx
    have hx_crit : x ∈ f.criticalSet := f.nonDegenerateCriticalSet_subset hx
    have D :
        ContMDiff.Owed.degree.CriticalChartPullbackData
          f.toRiemannSphere f.criticalSet x :=
      f.nonDegenerateCriticalSet_chartPullbackData x hx
    rcases ContMDiff.Owed.degree.criticalSet_pointIsolated_via_chart_pullback
        (f := f.toRiemannSphere) (crit := f.criticalSet)
        (x := x) hx_crit D with ⟨U, hU_open, hU_eq⟩
    refine ⟨U, hU_open, ?_⟩
    -- From `U ∩ f.criticalSet = {x}` and
    -- `f.nonDegenerateCriticalSet ⊆ f.criticalSet`, deduce
    -- `U ∩ f.nonDegenerateCriticalSet = {x}`.
    apply Set.eq_singleton_iff_unique_mem.mpr
    refine ⟨?_, ?_⟩
    · -- `x ∈ U ∩ f.nonDegenerateCriticalSet`.
      have hx_U : x ∈ U := by
        have : x ∈ U ∩ f.criticalSet := by
          rw [hU_eq]; exact rfl
        exact this.1
      exact ⟨hx_U, hx⟩
    · rintro y ⟨hy_U, hy_nd⟩
      have hy_crit : y ∈ f.criticalSet :=
        f.nonDegenerateCriticalSet_subset hy_nd
      have hy_in : y ∈ U ∩ f.criticalSet := ⟨hy_U, hy_crit⟩
      rw [hU_eq] at hy_in
      simpa using hy_in
  -- Closedness + compactness ⇒ finite.
  exact ContMDiff.Owed.degree.criticalSet_finite_of_isDiscrete_of_isClosed
    h_closed h_disc

/-! ## Conditional headline statements (residuals named) -/

/-- **Conditional headline (criticalSet).**

If for the non-constant `f : MeromorphicNonzero X`, the residuals
(R-MN: per-point chart-pullback witness exists) and (R-Closed:
critical set is closed) are supplied as a `CriticalSetWitness`, then
`f.criticalSet` is finite.

This is the renaming hand-off for the downstream `Degree.lean`
consumer. -/
theorem criticalSet_finite_of_nonconstant
    (f : MeromorphicNonzero X)
    (_hnc : ¬ Jacobians.Discharge.IsConstantMap f.toRiemannSphere)
    (w : CriticalSetWitness f) :
    f.criticalSet.Finite :=
  criticalSet_finite_of_witness f w

/-- **Conditional headline (criticalValues).** Image-finiteness from
`criticalSet_finite_of_nonconstant`. -/
theorem criticalValues_finite_of_nonconstant
    (f : MeromorphicNonzero X)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap f.toRiemannSphere)
    (w : CriticalSetWitness f) :
    f.criticalValues.Finite :=
  criticalValues_finite_of_criticalSet_finite f
    (criticalSet_finite_of_nonconstant f hnc w)

end MeromorphicNonzero

end Jacobians.Discharge

end

end
