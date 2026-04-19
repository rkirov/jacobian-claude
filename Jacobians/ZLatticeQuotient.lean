import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Jacobians.ChartedSpaceOfLocalHomeomorph

/-!
# Quotient of a finite-dimensional normed space by a `ZLattice`

Supporting theory for the `Jacobian X` construction.
Given `Λ : Submodule ℤ E` with `[DiscreteTopology Λ]` and `[IsZLattice ℝ Λ]`:

* `AddCommGroup (E ⧸ Λ.toAddSubgroup)` — automatic.
* `TopologicalSpace`, `T2Space`, `T3Space`, `IsTopologicalAddGroup` — automatic
  (via `AddSubgroup.isClosed_of_discrete` and `QuotientAddGroup.instT3Space`).
* `CompactSpace (E ⧸ Λ.toAddSubgroup)` — proven via
  `IsZLattice.isCompact_range_of_periodic`.
* `QuotientAddGroup.mk : E → E ⧸ Λ` is a covering map / local homeomorphism,
  which will be the foundation for the (still-to-come) `ChartedSpace E (E ⧸ Λ)`
  and `LieAddGroup` instances.

## References

Lee, *Introduction to Smooth Manifolds*, Ch. 21 (quotient Lie groups).
-/

namespace Jacobians.ZLatticeQuotient

/-! ### Covering-map structure

Works for any commutative topological group `E` with a discrete subgroup `Λ` —
no normed / finite-dim assumption needed. -/
section CoveringMap

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  (Λ : AddSubgroup E) [DiscreteTopology Λ]

/-- The quotient map `E → E ⧸ Λ` is a covering map. -/
theorem isCoveringMap_mk : IsCoveringMap (QuotientAddGroup.mk : E → E ⧸ Λ) :=
  (AddSubgroup.isAddQuotientCoveringMap_of_comm _
    DiscreteTopology.isDiscrete).isCoveringMap

/-- The quotient map `E → E ⧸ Λ` is a local homeomorphism. -/
theorem isLocalHomeomorph_mk :
    IsLocalHomeomorph (QuotientAddGroup.mk : E → E ⧸ Λ) :=
  (isCoveringMap_mk Λ).isLocalHomeomorph

/-- The quotient map `E → E ⧸ Λ` is an open map. -/
theorem isOpenMap_mk : IsOpenMap (QuotientAddGroup.mk : E → E ⧸ Λ) :=
  (isLocalHomeomorph_mk Λ).isOpenMap

/-- Charted space structure on `E ⧸ Λ` modelled on `E`, coming from the fact
that the quotient map is a surjective local homeomorphism. -/
noncomputable instance chartedSpaceQuotient : ChartedSpace E (E ⧸ Λ) :=
  (isLocalHomeomorph_mk Λ).chartedSpace QuotientAddGroup.mk_surjective

end CoveringMap

/-! ### Lie-group scaffolding instances on `E ⧸ Λ`

For `E` a finite-dim normed real space and `Λ` a `ZLattice`. -/
section ZLatticeInstances

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- `DiscreteTopology` transfers from `Λ : Submodule ℤ E` to `Λ.toAddSubgroup`. -/
instance : DiscreteTopology Λ.toAddSubgroup := ‹DiscreteTopology Λ›

/-- The quotient `E ⧸ Λ` is compact. The quotient map is continuous,
periodic with respect to `Λ`, and surjective, so its range (the whole
quotient) is compact by `IsZLattice.isCompact_range_of_periodic`. -/
instance instCompactSpaceQuotient : CompactSpace (E ⧸ Λ.toAddSubgroup) := by
  rw [← isCompact_univ_iff,
      ← Set.range_eq_univ.mpr (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup))]
  refine IsZLattice.isCompact_range_of_periodic Λ _
    QuotientAddGroup.continuous_mk ?_
  intro z w hw
  exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using hw)

example : AddCommGroup (E ⧸ Λ.toAddSubgroup) := inferInstance
example : TopologicalSpace (E ⧸ Λ.toAddSubgroup) := inferInstance
example : IsTopologicalAddGroup (E ⧸ Λ.toAddSubgroup) := inferInstance
example : T2Space (E ⧸ Λ.toAddSubgroup) := inferInstance
example : T3Space (E ⧸ Λ.toAddSubgroup) := inferInstance
example : CompactSpace (E ⧸ Λ.toAddSubgroup) := inferInstance
noncomputable example : ChartedSpace E (E ⧸ Λ.toAddSubgroup) := inferInstance

end ZLatticeInstances

/-! ### Manifold and Lie-group instances (sorried, proof-sketch documented)

The `IsManifold` and `LieAddGroup` instances on `E ⧸ Λ` are not yet closed;
they reduce to "transition maps between quotient charts are analytic",
which requires a locally-constant-lattice-translation argument that is a
substantial formalization step. Sketched below and left as TODO.

## Proof sketch for `IsManifold 𝓘(𝕜, E) n (E ⧸ Λ)`

Apply `isManifold_of_contDiffOn`. Charts `e, e'` in the atlas come from
`IsLocalHomeomorph.chartedSpace`, so each is `P.symm` for some
`P : OpenPartialHomeomorph E (E ⧸ Λ)` agreeing with `QuotientAddGroup.mk`
on its source. The transition `e.symm ≫ₕ e' = P ≫ₕ P'.symm : E → E`
sends `x ∈ P.source` with `mk x ∈ P'.target` to the unique `y ∈ P'.source`
with `mk y = mk x`, i.e. `y = x + λ` for some `λ ∈ Λ`.

Since `Λ` is discrete and the transition is continuous, the map `x ↦ λ`
is locally constant — on each connected component of the overlap, the
transition is literally `x ↦ x + λ₀` for a fixed `λ₀ ∈ Λ`. Translations
are analytic, so the transition is `ContDiffOn 𝕜 ω`.

## Proof sketch for `LieAddGroup`

`LieAddGroup` extends `ContMDiffAdd` and requires `ContMDiff_neg`. Both
reduce to the analyticity of addition / negation on `E ⧸ Λ`. These lift
from the analyticity of addition / negation on `E` via the quotient map,
using the fact that `QuotientAddGroup.mk` is a local homeomorphism. -/

section ManifoldStubs

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
  {n : WithTop ℕ∞}

/-- The analytic manifold structure on `E ⧸ Λ`. **TODO**: see the proof
sketch in the module docstring. -/
noncomputable instance instIsManifoldQuotient :
    IsManifold 𝓘(𝕜, E) n (E ⧸ Λ.toAddSubgroup) := sorry

/-- The analytic Lie-group structure on `E ⧸ Λ`. **TODO**: see the proof
sketch. -/
noncomputable instance instLieAddGroupQuotient :
    LieAddGroup 𝓘(𝕜, E) n (E ⧸ Λ.toAddSubgroup) := sorry

end ManifoldStubs

end Jacobians.ZLatticeQuotient
