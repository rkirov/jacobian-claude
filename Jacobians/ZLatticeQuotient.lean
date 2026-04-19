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

section Manifold

open scoped Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
  {n : WithTop ℕ∞}

/-- The analytic manifold structure on `E ⧸ Λ`.

**Proof outline** (deferred): apply `isManifold_of_contDiffOn`. Transitions
between charts in `IsLocalHomeomorph.chartedSpace` have the form
`P ≫ₕ P'.symm` where `P`, `P'` are `OpenPartialHomeomorph`s with
`P = P' = QuotientAddGroup.mk` as functions. The composition sends
`y ↦ y'` with `y' - y ∈ Λ`. Since `Λ` is discrete and the composition
is continuous, `y ↦ y' - y` is locally constant, so the transition is
locally a translation by a fixed lattice element. Translations are
analytic (`contDiff_id.add contDiff_const`). Hence the transition is
`ContDiffOn 𝕜 n`. -/
noncomputable instance instIsManifoldQuotient :
    IsManifold 𝓘(𝕜, E) n (E ⧸ Λ.toAddSubgroup) := sorry

/-- The analytic Lie-group structure on `E ⧸ Λ` — follows from
`IsManifold` plus analyticity of addition/negation on `E`, descended
through the quotient map via `QuotientAddGroup.mk` being a local
homeomorphism (`isLocalHomeomorph_mk`). -/
noncomputable instance instLieAddGroupQuotient :
    LieAddGroup 𝓘(𝕜, E) n (E ⧸ Λ.toAddSubgroup) := sorry

end Manifold

/-! ### Descent of linear maps to morphisms between ZLattice quotients

Given a lattice-respecting continuous ℝ-linear map between ambient spaces,
this section builds the induced group morphism between the corresponding
quotient tori and proves functoriality + the descent of the "degree
identity" `Φ ∘ Ψ = d • id` from the ambient to the quotient.

This is what makes the challenge's `pushforward_pullback = deg • id`
tractable once we have the ambient linear maps with the right degree
identity — the quotient side is structurally automatic. -/

section LatticeMorphisms

noncomputable section

/-- The descended pushforward map on quotient tori, from a lattice-respecting
ambient linear map. -/
def pushforward {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) (ΛY : Submodule ℤ (Fin gY → ℂ))
    (Φ : (Fin gX → ℂ) →L[ℝ] (Fin gY → ℂ))
    (hΦ : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ.toAddMonoidHom) :
    ((Fin gX → ℂ) ⧸ ΛX.toAddSubgroup) →ₜ+ ((Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) where
  toFun := QuotientAddGroup.map _ _ Φ.toAddMonoidHom hΦ
  map_zero' := (QuotientAddGroup.map _ _ Φ.toAddMonoidHom hΦ).map_zero
  map_add' := (QuotientAddGroup.map _ _ Φ.toAddMonoidHom hΦ).map_add
  continuous_toFun :=
    continuous_quot_lift _ (QuotientAddGroup.continuous_mk.comp Φ.continuous)

/-- The descended pullback map (dual direction). Defined via `pushforward`. -/
def pullback {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) (ΛY : Submodule ℤ (Fin gY → ℂ))
    (Ψ : (Fin gY → ℂ) →L[ℝ] (Fin gX → ℂ))
    (hΨ : ΛY.toAddSubgroup ≤ ΛX.toAddSubgroup.comap Ψ.toAddMonoidHom) :
    ((Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) →ₜ+ ((Fin gX → ℂ) ⧸ ΛX.toAddSubgroup) :=
  pushforward ΛY ΛX Ψ hΨ

/-- Headline: the degree identity `Φ ∘ Ψ = d • id` on the ambient
descends to `pushforward ∘ pullback = d • id` on the quotient. -/
theorem pushforward_pullback_of_ambient
    {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) (ΛY : Submodule ℤ (Fin gY → ℂ))
    (Φ : (Fin gX → ℂ) →L[ℝ] (Fin gY → ℂ))
    (Ψ : (Fin gY → ℂ) →L[ℝ] (Fin gX → ℂ))
    (hΦ : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ.toAddMonoidHom)
    (hΨ : ΛY.toAddSubgroup ≤ ΛX.toAddSubgroup.comap Ψ.toAddMonoidHom)
    (d : ℕ)
    (hΦΨ : ∀ y : (Fin gY → ℂ), Φ (Ψ y) = (d : ℕ) • y)
    (P : (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) :
    pushforward ΛX ΛY Φ hΦ (pullback ΛX ΛY Ψ hΨ P) = d • P := by
  induction P using QuotientAddGroup.induction_on with
  | H y =>
    show (QuotientAddGroup.mk (Φ (Ψ y)) : _) = d • (QuotientAddGroup.mk y : _)
    rw [hΦΨ y]
    simp

/-- Functoriality: ambient identity descends to quotient identity. -/
theorem pushforward_id_of_ambient
    {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ))
    (hΦΛ : Λ.toAddSubgroup ≤ Λ.toAddSubgroup.comap Φ.toAddMonoidHom)
    (hΦid : ∀ x : (Fin g → ℂ), Φ x = x)
    (P : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) :
    pushforward Λ Λ Φ hΦΛ P = P := by
  induction P using QuotientAddGroup.induction_on with
  | H x =>
    show (QuotientAddGroup.mk (Φ x) : _) = _
    rw [hΦid]

/-- Functoriality: ambient composition descends to quotient composition. -/
theorem pushforward_comp_of_ambient
    {gX gY gZ : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) (ΛY : Submodule ℤ (Fin gY → ℂ))
    (ΛZ : Submodule ℤ (Fin gZ → ℂ))
    (Φ₁ : (Fin gX → ℂ) →L[ℝ] (Fin gY → ℂ))
    (Φ₂ : (Fin gY → ℂ) →L[ℝ] (Fin gZ → ℂ))
    (hΦ₁ : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ₁.toAddMonoidHom)
    (hΦ₂ : ΛY.toAddSubgroup ≤ ΛZ.toAddSubgroup.comap Φ₂.toAddMonoidHom)
    (hΦ₁₂ : ΛX.toAddSubgroup ≤ ΛZ.toAddSubgroup.comap (Φ₂.comp Φ₁).toAddMonoidHom)
    (P : (Fin gX → ℂ) ⧸ ΛX.toAddSubgroup) :
    pushforward ΛX ΛZ (Φ₂.comp Φ₁) hΦ₁₂ P =
      pushforward ΛY ΛZ Φ₂ hΦ₂ (pushforward ΛX ΛY Φ₁ hΦ₁ P) := by
  induction P using QuotientAddGroup.induction_on with
  | H x => rfl

end

end LatticeMorphisms

end Jacobians.ZLatticeQuotient
