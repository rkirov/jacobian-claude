/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.Discharge.Manifold.CriticalSetDefinition

set_option autoImplicit true


/-! # Closedness of `MeromorphicNonzero.criticalSet` (R-Closed)

This file discharges the `R-Closed` residual identified in
`CriticalSetWitnessSupplier`: the `criticalSet` of the pole-extension
`f̃ := f.toRiemannSphere` is closed in `X`.

## Argument

`criticalSet f = { x | ¬ ∃ U ∈ 𝓝 x, InjOn f̃ U }` (definition in
`CriticalSetDefinition`). The complement — the **regular set**, namely the
set of points where `f̃` is locally injective — is open: if `x` admits an
open injectivity neighbourhood, *every* point in that neighbourhood does as
well, since the same neighbourhood works (a smaller open subset is still
locally injective and is a neighbourhood of any of its points).

The argument is purely topological / set-theoretic and does not use
analyticity or smoothness; it only uses that "neighbourhood of `x`
witnessing `InjOn`" is a property whose witness can be shrunk to an open
set and propagated.

## What this file ships

* `MeromorphicNonzero.regularSet` — the topological complement of
  `criticalSet`.
* `MeromorphicNonzero.regularSet_eq_compl_criticalSet` and
  `MeromorphicNonzero.criticalSet_eq_compl_regularSet`.
* `MeromorphicNonzero.isOpen_regularSet` — the regular set is open.
* `MeromorphicNonzero.isClosed_criticalSet` — **the headline residual**:
  `IsClosed f.criticalSet`.

No `sorry`. No `axiom`. No signature changes outside this file. -/

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

/-- **Regular set.** Points where `f̃ = f.toRiemannSphere` is locally
injective — i.e. some neighbourhood `U` satisfies `Set.InjOn f̃ U`. By
construction this is exactly the complement of `criticalSet f`. -/
def regularSet (f : MeromorphicNonzero X) : Set X :=
  { x : X | ∃ U ∈ 𝓝 x, Set.InjOn f.toRiemannSphere U }

/-- The regular set is the set-theoretic complement of the critical set. -/
lemma regularSet_eq_compl_criticalSet (f : MeromorphicNonzero X) :
    f.regularSet = (f.criticalSet)ᶜ := by
  ext x
  unfold regularSet criticalSet
  simp [Set.mem_compl_iff, Set.mem_setOf_eq, Classical.not_not]

/-- The critical set is the set-theoretic complement of the regular set. -/
lemma criticalSet_eq_compl_regularSet (f : MeromorphicNonzero X) :
    f.criticalSet = (f.regularSet)ᶜ := by
  rw [regularSet_eq_compl_criticalSet, compl_compl]

/-- **R-Closed lemma 1: the regular set is open.**

If `x ∈ f.regularSet`, pick `U ∈ 𝓝 x` with `Set.InjOn f̃ U`. Shrink to an
open subset `V ⊆ U` with `x ∈ V`. Then `V ⊆ f.regularSet`: for any
`y ∈ V`, the same `V` is a neighbourhood of `y` (since `V` is open) and
`InjOn f̃ V` (restriction of `InjOn f̃ U` to `V ⊆ U`). -/
theorem isOpen_regularSet (f : MeromorphicNonzero X) :
    IsOpen f.regularSet := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  -- Unpack the injectivity witness at `x`.
  obtain ⟨U, hU_mem, hU_inj⟩ := hx
  -- Shrink `U` to an open neighbourhood of `x`.
  obtain ⟨V, hV_subU, hV_open, hxV⟩ := mem_nhds_iff.mp hU_mem
  -- We claim `V ⊆ f.regularSet`. Then `V ∈ 𝓝 x` since `V` is open and
  -- contains `x`, hence `f.regularSet ∈ 𝓝 x`.
  have hV_sub_reg : V ⊆ f.regularSet := by
    intro y hyV
    refine ⟨V, hV_open.mem_nhds hyV, ?_⟩
    exact hU_inj.mono hV_subU
  exact Filter.mem_of_superset (hV_open.mem_nhds hxV) hV_sub_reg

/-- **R-Closed (headline).** The critical set of `f̃ = f.toRiemannSphere`
is closed in `X`.

Direct corollary: `criticalSet = (regularSet)ᶜ` and `regularSet` is open
by `isOpen_regularSet`. -/
theorem isClosed_criticalSet (f : MeromorphicNonzero X) :
    IsClosed f.criticalSet := by
  rw [criticalSet_eq_compl_regularSet]
  exact (isOpen_regularSet f).isClosed_compl

end MeromorphicNonzero

end Jacobians.Discharge

end

end
