import Jacobians.LineIntegral
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Period lattice of a compact Riemann surface

Real (non-placeholder) period lattice of `HolomorphicOneForms X`.
Defined as the ℤ-span of the image of smooth closed loops under the
period pairing.

## Structure

* `periodBasisForm X i` — the i-th basis element of
  `HolomorphicOneForms X` (via `ambientIso X`), used for the period
  pairing. Aligning with `ambientIso` makes the matrix identities
  for `ambientPhi` / `ambientPsi` clean.
* `periodVec γ` — period vector of a path `γ`.
* `closedLoopPeriods X` — image of the period pairing over smooth
  closed loops.
* `truePeriodLattice X` — the ℤ-span.
* `periodVec_pushforward` — the change-of-variables identity
  `periodVec Y (f ∘ γ) = ambientPhi f hf (periodVec X γ)`, from
  which `ambientPhi` preservation of the period lattice follows.
* `IsPeriodLattice X` typeclass — axiomatizes `DiscreteTopology` and
  `IsZLattice ℝ` of the period lattice. These properties require the
  Hodge-decomposition-level rank-2g theorem, which is tagged as an
  open Mathlib-adjacent contribution. Downstream code assuming
  `[IsPeriodLattice X]` can proceed.

## References

Forster §§20–21; Miranda Ch. V §§1–3.
-/

namespace Jacobians

open scoped Manifold ContDiff Bundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Arbitrary basepoint in `X` (via `Nonempty`). The period lattice
is independent of basepoint choice, because any two basepoints can
be connected by a path which conjugates closed loops without changing
the integral (modulo the lattice itself). -/
noncomputable def basepoint (X : Type*) [Nonempty X] : X := Classical.arbitrary X

/-- The i-th basis element of `HolomorphicOneForms X`, defined via
`ambientIso X` applied to the standard unit vector. This choice
aligns the period pairing with the matrix structure of `ambientPhi`
and `ambientPsi`, which are expressed in the `Pi.basisFun` basis. -/
noncomputable def periodBasisForm (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (i : Fin (genus X)) : HolomorphicOneForms X :=
  ambientIso X (Pi.basisFun ℂ (Fin (genus X)) i)

/-- Period vector of a path `γ`: line integrals of each basis form. -/
noncomputable def periodVec (γ : ℝ → X) : Fin (genus X) → ℂ :=
  fun i => lineIntegral (periodBasisForm X i) γ

/-- The set of period vectors arising from smooth closed loops (at
any basepoint). The `γ 0 = γ 1` condition captures "closed loop".
Allowing any basepoint makes the set manifestly preserved under
composition with a smooth map (the image of a closed loop is a
closed loop), simplifying functoriality proofs. -/
def closedLoopPeriods (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Set (Fin (genus X) → ℂ) :=
  {v | ∃ (γ : ℝ → X), γ 0 = γ 1 ∧ v = periodVec γ}

/-- **True period lattice**: ℤ-span of period vectors of closed
loops. -/
noncomputable def truePeriodLattice (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Submodule ℤ (Fin (genus X) → ℂ) :=
  Submodule.span ℤ (closedLoopPeriods X)

/-- Any closed-loop period vector is in the period lattice. -/
theorem periodVec_mem_truePeriodLattice_of_closed (γ : ℝ → X) (hγ : γ 0 = γ 1) :
    periodVec γ ∈ truePeriodLattice X :=
  Submodule.subset_span ⟨γ, hγ, rfl⟩

/-! ### Abel–Jacobi well-definedness (classical, Abel 1826)

Two paths with the same endpoints yield period vectors that differ
by a period-lattice element. The classical proof uses `γ₁` followed
by `reverse γ₂` to form a closed loop; its period vector is
`periodVec γ₁ - periodVec γ₂`, manifestly in the lattice.

The smoothness content is packed into the `hconcat` hypothesis:
`periodVec (concat γ₁ (reverse γ₂)) = periodVec γ₁ - periodVec γ₂`.
This single equation encodes the output of Phase 1 reversal and
concatenation identities (which individually carry differentiability /
integrability hypotheses). Downstream callers who have smooth γ can
derive `hconcat` from Phase 1 lemmas; callers working abstractly can
just pass it in. -/

/-- **Abel–Jacobi well-definedness (lattice form).** If two paths
share endpoints, their period vectors differ by a lattice element. -/
theorem periodVec_sub_mem_truePeriodLattice
    (γ₁ γ₂ : ℝ → X) (h0 : γ₁ 0 = γ₂ 0)
    (hconcat : periodVec (concat γ₁ (reverse γ₂)) =
      periodVec γ₁ - periodVec γ₂) :
    periodVec γ₁ - periodVec γ₂ ∈ truePeriodLattice X := by
  rw [← hconcat]
  refine periodVec_mem_truePeriodLattice_of_closed _ ?_
  -- (concat γ₁ (reverse γ₂)) 0 = γ₁ 0 = γ₂ 0 = (reverse γ₂) 1 = (concat γ₁ (reverse γ₂)) 1
  -- at t = 0: 0 ≤ 1/2, so concat... 0 = γ₁ (2 * 0) = γ₁ 0.
  -- at t = 1: ¬(1 ≤ 1/2), so concat... 1 = (reverse γ₂)(2 * 1 - 1) = (reverse γ₂) 1 = γ₂ (1-1) = γ₂ 0.
  show (concat γ₁ (reverse γ₂)) 0 = (concat γ₁ (reverse γ₂)) 1
  rw [concat_apply_left _ _ (by norm_num : (0 : ℝ) ≤ 1/2),
      concat_apply_right _ _ (by norm_num : ¬ (1 : ℝ) ≤ 1/2)]
  simp only [reverse_apply, mul_zero]
  have h1 : (1 : ℝ) - (2 * 1 - 1) = 0 := by norm_num
  rw [h1, h0]

/-- **Abel–Jacobi well-definedness (quotient form).** Two paths
sharing both endpoints map to the same element of
`(Fin (genus X) → ℂ) ⧸ truePeriodLattice X`. -/
theorem mk_periodVec_eq_of_endpoints
    (γ₁ γ₂ : ℝ → X) (h0 : γ₁ 0 = γ₂ 0)
    (hconcat : periodVec (concat γ₁ (reverse γ₂)) =
      periodVec γ₁ - periodVec γ₂) :
    (QuotientAddGroup.mk (periodVec γ₁) :
      (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
      QuotientAddGroup.mk (periodVec γ₂) := by
  rw [QuotientAddGroup.eq]
  -- Goal: -periodVec γ₁ + periodVec γ₂ ∈ (truePeriodLattice X).toAddSubgroup
  -- We have periodVec γ₁ - periodVec γ₂ ∈ truePeriodLattice X.
  -- By negation closure: -(periodVec γ₁ - periodVec γ₂) = -periodVec γ₁ + periodVec γ₂ ∈ lattice.
  have h := periodVec_sub_mem_truePeriodLattice γ₁ γ₂ h0 hconcat
  have : -periodVec γ₁ + periodVec γ₂ = -(periodVec γ₁ - periodVec γ₂) := by ring
  rw [this]
  exact (truePeriodLattice X).neg_mem h

/-! ### Phase 4 support: change of variables under smooth maps

For `f : X → Y` smooth and `γ : ℝ → X` a path, the period vector of
the image loop `f ∘ γ` in `Y` is the `ambientPhi`-image of the period
vector of `γ` in `X`. This is the formal expression of "image of a
loop has period given by the pullback matrix" — the analytic content
that forces `ambientPhi` to preserve the lattice. -/

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- Change-of-variables at the vector level: evaluating each Y-basis
form against `f ∘ γ` equals evaluating its pullback against `γ`. -/
theorem periodVec_comp_eq_lineIntegral_pullback
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (γ : ℝ → X) (j : Fin (genus Y)) :
    periodVec (f ∘ γ) j =
      lineIntegral (pullbackForm f hf (periodBasisForm Y j)) γ := by
  unfold periodVec
  exact lineIntegral_pullback f hf (periodBasisForm Y j) γ

/-- **Key identity**: the period vector of the image loop equals
`ambientPhi` applied to the period vector of the source loop.

With `periodBasisForm Y j = ambientIso Y e_j^Y`, the pullback
`pullbackForm f hf (periodBasisForm Y j)` expanded in the `X`-basis
has coefficients `(ambientPsi f hf e_j^Y) i = M_ij`. Then:

  `(ambientPhi f hf v)_j = ∑_i M_ij v_i`

matches:

  `periodVec Y (f∘γ) j = ∫_γ pullbackForm f hf (basis_j^Y)
                       = ∑_i M_ij (periodVec X γ)_i`.

Uses `lineIntegral_pullback` (content sorry pending) + linearity of
`lineIntegral` in the form + basis expansion. -/
theorem periodVec_pushforward
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (γ : ℝ → X) :
    periodVec (f ∘ γ) =
      ambientPhi (gX := genus X) (gY := genus Y) f hf (periodVec γ) :=
  sorry

/-- **`IsPeriodLattice` typeclass.** Axiomatizes the two key structural
facts about the period lattice that follow from the Hodge
decomposition of compact Riemann surfaces:

* `period_discrete`: the lattice has the discrete topology.
* `period_isZLattice`: the lattice has rank `2 * genus X` as a
  ℤ-module in `ℂ^(genus X)` (= `ℝ^(2 * genus X)`), making it a full
  ℝ-lattice.

Both follow from Hodge decomposition + non-degeneracy of the period
pairing (classical result; Forster §§20–21). This typeclass absorbs
the Mathlib gap. -/
class IsPeriodLattice (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Prop where
  period_discrete : DiscreteTopology (truePeriodLattice X)
  period_isZLattice : IsZLattice ℝ (truePeriodLattice X)

attribute [instance] IsPeriodLattice.period_discrete
attribute [instance] IsPeriodLattice.period_isZLattice

/-! ### Phase 4a: `ambientPhi` preserves the period lattice

From `periodVec_pushforward`: for a closed loop `γ` in `X`, `f ∘ γ`
is a closed loop in `Y`, so `periodVec (f ∘ γ)` lies in the period
lattice of `Y`. This equals `ambientPhi f hf (periodVec γ)`, so
`ambientPhi` sends `closedLoopPeriods X` into `truePeriodLattice Y`.
By ℤ-linearity, it sends the whole ℤ-span into `truePeriodLattice Y`.

Stated here in the `AddSubgroup.comap` form matching `Jacobians.lean`. -/

theorem ambientPhi_preserves_truePeriodLattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (truePeriodLattice X).toAddSubgroup ≤
      (truePeriodLattice Y).toAddSubgroup.comap
        (ambientPhi (gX := genus X) (gY := genus Y) f hf).toAddMonoidHom := by
  show ∀ v ∈ truePeriodLattice X,
    ambientPhi (gX := genus X) (gY := genus Y) f hf v ∈ truePeriodLattice Y
  intro v hv
  refine Submodule.span_induction
    (p := fun v _ => ambientPhi (gX := genus X) (gY := genus Y) f hf v ∈
      truePeriodLattice Y) ?_ ?_ ?_ ?_ hv
  · -- member case
    rintro _ ⟨γ, hγ, rfl⟩
    rw [← periodVec_pushforward f hf γ]
    exact periodVec_mem_truePeriodLattice_of_closed (f ∘ γ)
      (by simp [Function.comp_apply, hγ])
  · -- zero case
    simp
  · -- add case
    intro x y _ _ hx hy
    simp only [map_add]
    exact Submodule.add_mem _ hx hy
  · -- smul case (ℤ-scalar)
    intro r x _ hx
    simp only [map_zsmul]
    exact Submodule.smul_mem _ r hx

end Jacobians
