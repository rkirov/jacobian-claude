import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.LocallyConstant.Basic
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

open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
  {n : WithTop ℕ∞}

/-! ### Transitions between `mk`-matching partial homs are locally translations

Any two `OpenPartialHomeomorph E (E ⧸ Λ.toAddSubgroup)` whose `toFun`s
equal `QuotientAddGroup.mk` have a composition `P ≫ₕ P'.symm : E → E`
that satisfies `(P ≫ₕ P'.symm) y - y ∈ Λ`. Since `Λ` is discrete and
the composition is continuous, the difference is locally constant,
hence the composition is locally a translation. -/

/-- Step 1: transition displacement lies in the lattice. -/
theorem transition_sub_mem_lattice
    (P P' : OpenPartialHomeomorph E (E ⧸ Λ.toAddSubgroup))
    (hP : (P : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk)
    (hP' : (P' : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk)
    {y : E} (hy : y ∈ (P ≫ₕ P'.symm).source) :
    (P ≫ₕ P'.symm) y - y ∈ Λ.toAddSubgroup := by
  rw [← QuotientAddGroup.eq_iff_sub_mem]
  -- Goal: (mk ((P ≫ₕ P'.symm) y) : E⧸Λ) = mk y.
  rw [OpenPartialHomeomorph.trans_apply]
  -- Goal: (mk (P'.symm (P y)) : _) = mk y.
  rw [OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      OpenPartialHomeomorph.symm_source] at hy
  -- hy : y ∈ P.source ∧ P y ∈ P'.target.
  have hPy : P y ∈ P'.target := hy.2
  have key : (P' (P'.symm (P y)) : E ⧸ Λ.toAddSubgroup) = P y :=
    P'.right_inv hPy
  calc (QuotientAddGroup.mk (P'.symm (P y)) : E ⧸ Λ.toAddSubgroup)
      = P' (P'.symm (P y)) := by rw [← hP']
    _ = P y               := key
    _ = QuotientAddGroup.mk y := by rw [hP]

/-- Step 2 + 3: the displacement `y ↦ transition y - y` is continuous. -/
theorem transition_displacement_continuousOn
    (P P' : OpenPartialHomeomorph E (E ⧸ Λ.toAddSubgroup)) :
    ContinuousOn (fun y : E => (P ≫ₕ P'.symm) y - y) (P ≫ₕ P'.symm).source :=
  ((P ≫ₕ P'.symm).continuousOn).sub continuousOn_id

/-- Step 4: near any point of the source, the displacement is constant.

Proof: displacement `d` is continuous on `T.source` (open) into `E`,
with values in `Λ`. `Λ` is discrete in `E`, so near `y₀` the value
`d y` must equal `d y₀`. -/
theorem transition_displacement_eventuallyEq
    (P P' : OpenPartialHomeomorph E (E ⧸ Λ.toAddSubgroup))
    (hP : (P : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk)
    (hP' : (P' : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk)
    {y₀ : E} (hy₀ : y₀ ∈ (P ≫ₕ P'.symm).source) :
    ∀ᶠ y in 𝓝 y₀, (P ≫ₕ P'.symm) y - y = (P ≫ₕ P'.symm) y₀ - y₀ := by
  set T := P ≫ₕ P'.symm
  set d : E → E := fun y => T y - y
  -- The restriction of `d` to `T.source` is a continuous map into `Λ.toAddSubgroup`
  -- (a subtype with the discrete topology).
  let drestr : T.source → (Λ.toAddSubgroup : Set E) :=
    fun ⟨y, hy⟩ => ⟨d y, transition_sub_mem_lattice Λ P P' hP hP' hy⟩
  have hd_cont : ContinuousOn d T.source :=
    transition_displacement_continuousOn Λ P P'
  have hdrestr_cont : Continuous drestr := by
    refine continuous_induced_rng.mpr ?_
    exact hd_cont.comp_continuous continuous_subtype_val Subtype.property
  -- Target has the discrete topology (as a subspace of E via the Λ coercion).
  -- So `drestr` is locally constant.
  have hlc : IsLocallyConstant drestr :=
    (IsLocallyConstant.iff_continuous drestr).mpr hdrestr_cont
  -- From local constancy on the subtype we get eventual equality within 𝓝 ⟨y₀, hy₀⟩.
  have hsub := hlc.eventually_eq ⟨y₀, hy₀⟩
  -- Transport to 𝓝 y₀ via the open-embedding `Subtype.val : T.source → E`.
  have hopen : IsOpen (T.source : Set E) := T.open_source
  have hemb : Topology.IsOpenEmbedding (Subtype.val : T.source → E) :=
    hopen.isOpenEmbedding_subtypeVal
  -- The filter `𝓝 y₀` on E, restricted to the image, corresponds to the
  -- subtype filter at ⟨y₀, hy₀⟩.
  -- Specifically, `𝓝 (⟨y₀, hy₀⟩ : T.source) = Filter.comap Subtype.val (𝓝 y₀)`.
  rw [hemb.nhds_eq_comap ⟨y₀, hy₀⟩] at hsub
  -- Push through via `Filter.eventually_comap` to get the result on E.
  filter_upwards [hopen.mem_nhds hy₀, Filter.eventually_comap.mp hsub] with y hy_src hy_eq
  have := hy_eq ⟨y, hy_src⟩ rfl
  exact congrArg Subtype.val this

/-- Step 5: the transition between `mk`-matching partial homs is
`ContDiffOn 𝕜 n` on its source. Near any point of the source, the
transition equals a translation by a fixed lattice element (step 4),
and translations are `ContDiff`. -/
theorem transition_contDiffOn_of_agrees_with_mk
    (P P' : OpenPartialHomeomorph E (E ⧸ Λ.toAddSubgroup))
    (hP : (P : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk)
    (hP' : (P' : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk) :
    ContDiffOn 𝕜 n (P ≫ₕ P'.symm : E → E) (P ≫ₕ P'.symm).source := by
  intro y₀ hy₀
  set T := P ≫ₕ P'.symm
  -- The transition equals a translation in a neighborhood of y₀
  have heq : (fun y : E => T y) =ᶠ[𝓝 y₀] (fun y : E => y + (T y₀ - y₀)) := by
    filter_upwards [transition_displacement_eventuallyEq Λ P P' hP hP' hy₀] with y hy
    -- hy : T y - y = T y₀ - y₀.  Rearranging: T y = y + (T y₀ - y₀).
    have : T y = y + (T y - y) := by abel
    rw [this, hy]
  -- Translation is ContDiff
  have htrans : ContDiff 𝕜 n (fun y : E => y + (T y₀ - y₀)) :=
    contDiff_id.add contDiff_const
  -- Combine
  exact (htrans.contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt

/-- The analytic manifold structure on `E ⧸ Λ`. -/
noncomputable instance instIsManifoldQuotient :
    IsManifold 𝓘(𝕜, E) n (E ⧸ Λ.toAddSubgroup) := by
  refine isManifold_of_contDiffOn _ _ _ ?_
  intro e e' he he'
  obtain ⟨q₁, rfl⟩ := he
  obtain ⟨q₂, rfl⟩ := he'
  set x₁ := Classical.choose (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) q₁)
  set x₂ := Classical.choose (QuotientAddGroup.mk_surjective (s := Λ.toAddSubgroup) q₂)
  set P₁ := IsLocalHomeomorph.chartAtPreimage (isLocalHomeomorph_mk Λ.toAddSubgroup) x₁
  set P₂ := IsLocalHomeomorph.chartAtPreimage (isLocalHomeomorph_mk Λ.toAddSubgroup) x₂
  have hP₁ : (P₁ : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimage (isLocalHomeomorph_mk Λ.toAddSubgroup) x₁).symm
  have hP₂ : (P₂ : E → E ⧸ Λ.toAddSubgroup) = QuotientAddGroup.mk :=
    (IsLocalHomeomorph.eq_chartAtPreimage (isLocalHomeomorph_mk Λ.toAddSubgroup) x₂).symm
  -- Simplify away the trivial model / range-of-model
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Set.range_id, Set.preimage_id, id_eq,
    Set.inter_univ, OpenPartialHomeomorph.symm_symm]
  exact transition_contDiffOn_of_agrees_with_mk Λ P₁ P₂ hP₁ hP₂

/-- The analytic Lie-group structure on `E ⧸ Λ`. -/
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
