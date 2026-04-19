import Mathlib

/-!
# Quotient of a finite-dimensional normed space by a `ZLattice`

This file develops the Lie-group structure on `E ⧸ Λ` where `E` is a
finite-dimensional normed space over `ℝ` (or a normed field `𝕜 ∈ {ℝ, ℂ}`
extending `ℝ`), and `Λ : Submodule ℤ E` is a full-rank discrete lattice
(`IsZLattice ℝ Λ`).

Session 2+ progress — currently establishes the "cheap" instances
(`CompactSpace`) and stubs the manifold / `LieAddGroup` instances.

## Outline

Given `Λ : Submodule ℤ E` with `[DiscreteTopology Λ]` and `[IsZLattice ℝ Λ]`:

* `AddCommGroup (E ⧸ Λ.toAddSubgroup)` — automatic from `QuotientAddGroup`.
* `TopologicalSpace (E ⧸ Λ.toAddSubgroup)` — automatic.
* `T2Space (E ⧸ Λ.toAddSubgroup)` — automatic via `AddSubgroup.isClosed_of_discrete`
  and `QuotientAddGroup.instT3Space`.
* `CompactSpace (E ⧸ Λ.toAddSubgroup)` — via
  `IsZLattice.isCompact_range_of_periodic`.
* `ChartedSpace E (E ⧸ Λ.toAddSubgroup)` — **TODO** (requires a charted-space
  constructor from `IsLocalHomeomorph`, which is a candidate Mathlib contribution).
* `IsManifold 𝓘(𝕜, E) ω (E ⧸ Λ.toAddSubgroup)` — **TODO** (after `ChartedSpace`).
* `LieAddGroup 𝓘(𝕜, E) ω (E ⧸ Λ.toAddSubgroup)` — **TODO**.

## References

Lee, *Introduction to Smooth Manifolds*, Ch. 21 (quotient Lie groups).
-/

namespace Jacobians.ZLatticeQuotient

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

/-- The quotient `E ⧸ Λ` is compact: the quotient map is continuous, periodic with
respect to `Λ`, and surjective, so its range (the whole quotient) is compact by
`IsZLattice.isCompact_range_of_periodic`. -/
instance instCompactSpaceQuotient : CompactSpace (E ⧸ Λ.toAddSubgroup) := by
  rw [← isCompact_univ_iff,
      ← Set.range_eq_univ.mpr (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup))]
  refine IsZLattice.isCompact_range_of_periodic Λ _
    QuotientAddGroup.continuous_mk ?_
  intro z w hw
  exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using hw)

section Freebies

/-! The following instances are automatic once `E ⧸ Λ.toAddSubgroup` is spelled out.
They are recorded as `example`s so regressions are caught at build time. -/

example : AddCommGroup (E ⧸ Λ.toAddSubgroup) := inferInstance
example : TopologicalSpace (E ⧸ Λ.toAddSubgroup) := inferInstance
example : IsTopologicalAddGroup (E ⧸ Λ.toAddSubgroup) := inferInstance
example : T2Space (E ⧸ Λ.toAddSubgroup) := inferInstance
example : CompactSpace (E ⧸ Λ.toAddSubgroup) := inferInstance

end Freebies

/-- TODO: the quotient `E ⧸ Λ` is a charted space modelled on `E`.
This requires a charted-space-from-local-homeomorphism constructor
that does not currently exist in Mathlib; see `Mathlib/Topology/Covering/`.
The local homeomorphism we want is `QuotientAddGroup.mk : E → E ⧸ Λ`,
which is a covering map by `AddSubgroup.isAddQuotientCoveringMap_of_comm`. -/
@[implicit_reducible]
def chartedSpace : ChartedSpace E (E ⧸ Λ.toAddSubgroup) := sorry

end Jacobians.ZLatticeQuotient
