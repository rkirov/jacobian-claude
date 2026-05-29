import Jacobians.LineIntegral
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Connected.LocPathConnected
import Jacobians.Discharge.Manifold.CriticalValuesFiniteGeneral
import Jacobians.Discharge.Manifold.RegularValueExistsRegUnconditional
import Jacobians.SmoothPath
import Jacobians.SmoothPathCore
import Jacobians.ZLatticeQuotient
import Mathlib.Analysis.Complex.OpenMapping

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
* `DiscreteTopology`/`IsZLattice ℝ` of `truePeriodLattice X` — these are the
  two open instances (S2/S3) supplied as `sorry` instances below. They hold
  classically (the period lattice is a full-rank ℤ-lattice in `ℝ^(2g)`) but
  require the Hodge / Riemann-bilinear-relations theorem (Forster §§19–20),
  not yet in Mathlib. NOTE: there is no `IsPeriodLattice` typeclass — these are
  unconditional `sorry` instances, so every `Jacobian`-as-torus consequence
  rests on them; a future refactor could gate them behind an explicit
  hypothesis class instead.

## References

Forster §§20–21; Miranda Ch. V §§1–3.
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology
open Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- The foundational smoothPath-independent declarations (`basepoint`,
-- path-connectedness instances, `continuousPath`, `periodBasisForm`,
-- `periodVec`, `IsClosedSmoothLoop`, `closedLoopPeriods`, `IsSmoothPath`
-- + `toClosedSmoothLoop`/`reverse`/`isSmoothPath_const`, and
-- `IsClosedSmoothLoop.reverse`) have moved UPSTREAM to
-- `Jacobians/SmoothPathCore.lean`, so the chart-ball-hop machinery there
-- can be constructed without depending on this file. They remain in the
-- `Jacobians` namespace and are available here via `import
-- Jacobians.SmoothPathCore`.

-- The smoothPath definition and its properties have moved below
-- `periodVec_mem_truePeriodLattice_of_closed`, where they can all
-- be derived from a single consolidated existence theorem
-- (`exists_smoothPath_family`). The previous chart-cover-piecewise
-- scaffolding (`Jacobians.smoothPathRaw`) remains in
-- `Jacobians/SmoothPath.lean` for future explicit-construction work
-- to discharge the consolidated existence.

/-- **True period lattice**: ℤ-span of period vectors of closed
loops. -/
noncomputable def truePeriodLattice (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Submodule ℤ (Fin (genus X) → ℂ) :=
  Submodule.span ℤ (closedLoopPeriods X)

/-- Any closed-smooth-loop period vector is in the period lattice. -/
theorem periodVec_mem_truePeriodLattice_of_closed (γ : ℝ → X)
    (hγ : IsClosedSmoothLoop γ) :
    periodVec γ ∈ truePeriodLattice X :=
  Submodule.subset_span ⟨γ, hγ, rfl⟩


/-- **Constant-path period vector is zero.** Classical fact: the
tangent of a constant curve is zero, so every integrand is zero. -/
theorem periodVec_const (P : X) : periodVec (fun _ : ℝ => P) = 0 := by
  funext i
  exact lineIntegral_const _ P

/-- **Period vector reverses sign under path reversal.** Classical
fact: `∫_{reverse γ} ω = -∫_γ ω`. Applied componentwise to the basis
forms. The α-independent differentiability hypothesis is inherited
from `lineIntegral_reverse`. -/
theorem periodVec_reverse (γ : ℝ → X)
    (hdiff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ (1 - t))).toFun ∘ γ) (1 - t)) :
    periodVec (reverse γ) = -periodVec γ := by
  funext i
  exact lineIntegral_reverse (periodBasisForm X i) γ hdiff

open MeasureTheory in
/-- **Period vector is additive under path concatenation.** Classical
fact: `∫_{γ ∗ γ'} ω = ∫_γ ω + ∫_{γ'} ω`. Applied componentwise to
basis forms. Hypotheses (integrability per basis form + pointwise
a.e. identities from the `pathSpeed` chain rule on each half) are
per-i quantified versions of `lineIntegral_concat`'s hypotheses. -/
theorem periodVec_concat (γ γ' : ℝ → X)
    (hint_γ : ∀ i : Fin (genus X), IntervalIntegrable
      (fun u => (periodBasisForm X i).toFun (γ u) (pathSpeed γ u)) volume 0 1)
    (hint_γ' : ∀ i : Fin (genus X), IntervalIntegrable
      (fun u => (periodBasisForm X i).toFun (γ' u) (pathSpeed γ' u)) volume 0 1)
    (hint_concat_left : ∀ i : Fin (genus X), IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun ((concat γ γ') t)
        (pathSpeed (concat γ γ') t)) volume 0 (1/2))
    (hint_concat_right : ∀ i : Fin (genus X), IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun ((concat γ γ') t)
        (pathSpeed (concat γ γ') t)) volume (1/2) 1)
    (h_ae_left : ∀ i : Fin (genus X), ∀ᵐ t ∂(volume.restrict (Set.uIoc (0 : ℝ) (1/2))),
      (periodBasisForm X i).toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t) =
        (2 : ℂ) * (periodBasisForm X i).toFun (γ (2 * t)) (pathSpeed γ (2 * t)))
    (h_ae_right : ∀ i : Fin (genus X), ∀ᵐ t ∂(volume.restrict (Set.uIoc ((1 : ℝ)/2) 1)),
      (periodBasisForm X i).toFun ((concat γ γ') t) (pathSpeed (concat γ γ') t) =
        (2 : ℂ) * (periodBasisForm X i).toFun (γ' (2 * t - 1)) (pathSpeed γ' (2 * t - 1))) :
    periodVec (concat γ γ') = periodVec γ + periodVec γ' := by
  funext i
  exact lineIntegral_concat (periodBasisForm X i) γ γ'
    (hint_γ i) (hint_γ' i)
    (hint_concat_left i) (hint_concat_right i)
    (h_ae_left i) (h_ae_right i)

/-- **Closed-loop period is zero in the Jacobian.** Classical fact:
integrating any form along a closed smooth loop gives an element of
the period lattice, which is the zero class in the Jacobian quotient. -/
theorem mk_periodVec_closed_loop_zero (γ : ℝ → X) (hγ : IsClosedSmoothLoop γ) :
    (QuotientAddGroup.mk (periodVec γ) :
      (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).mpr
    (periodVec_mem_truePeriodLattice_of_closed γ hγ)

/-- **Constant-path Jacobian class is zero.** Corollary of
`periodVec_const`: the quotient class of the zero vector is zero. -/
theorem mk_periodVec_const_zero (P : X) :
    (QuotientAddGroup.mk (periodVec (fun _ : ℝ => P)) :
      (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) = 0 := by
  rw [periodVec_const]
  exact QuotientAddGroup.mk_zero _

/-- **Abel-Jacobi additivity under concatenation.** Classical fact:
concatenating a path `P → Q` with a path `Q → R` corresponds to
adding their Jacobian-valued classes. Takes the same per-basis-form
hypotheses as `periodVec_concat`. -/
theorem mk_periodVec_concat_eq_add
    (γ γ' : ℝ → X) (hperiod : periodVec (concat γ γ') = periodVec γ + periodVec γ') :
    (QuotientAddGroup.mk (periodVec (concat γ γ')) :
      (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
      QuotientAddGroup.mk (periodVec γ) + QuotientAddGroup.mk (periodVec γ') := by
  rw [hperiod]
  rfl

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

/-- **Abel–Jacobi well-definedness (lattice form).** If two smooth
paths share endpoints, their period vectors differ by a lattice
element. The concatenation `γ₁ ∗ reverse γ₂` must itself be a closed
smooth loop (passed in as `hsmooth`). -/
theorem periodVec_sub_mem_truePeriodLattice
    (γ₁ γ₂ : ℝ → X) (_h0 : γ₁ 0 = γ₂ 0)
    (hsmooth : IsClosedSmoothLoop (concat γ₁ (reverse γ₂)))
    (hconcat : periodVec (concat γ₁ (reverse γ₂)) =
      periodVec γ₁ - periodVec γ₂) :
    periodVec γ₁ - periodVec γ₂ ∈ truePeriodLattice X := by
  rw [← hconcat]
  exact periodVec_mem_truePeriodLattice_of_closed _ hsmooth

/-- **Abel–Jacobi well-definedness (quotient form).** Two smooth
paths sharing both endpoints map to the same element of
`(Fin (genus X) → ℂ) ⧸ truePeriodLattice X`. -/
theorem mk_periodVec_eq_of_endpoints
    (γ₁ γ₂ : ℝ → X) (h0 : γ₁ 0 = γ₂ 0)
    (hsmooth : IsClosedSmoothLoop (concat γ₁ (reverse γ₂)))
    (hconcat : periodVec (concat γ₁ (reverse γ₂)) =
      periodVec γ₁ - periodVec γ₂) :
    (QuotientAddGroup.mk (periodVec γ₁) :
      (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
      QuotientAddGroup.mk (periodVec γ₂) := by
  rw [QuotientAddGroup.eq]
  have h := periodVec_sub_mem_truePeriodLattice γ₁ γ₂ h0 hsmooth hconcat
  have : -periodVec γ₁ + periodVec γ₂ = -(periodVec γ₁ - periodVec γ₂) := by ring
  rw [this]
  exact (truePeriodLattice X).neg_mem h

/-- **Period vector is additive under concatenation of two smooth paths.**
Packages the 6 hypotheses of `periodVec_concat` for smooth paths sharing an
endpoint (no zero-velocity needed — additivity holds for any smooth paths). -/
theorem periodVec_concat_of_smooth {P Q R : X} {g₁ g₂ : ℝ → X}
    (h₁ : IsSmoothPath P Q g₁) (h₂ : IsSmoothPath Q R g₂) :
    periodVec (Jacobians.concat g₁ g₂) = periodVec g₁ + periodVec g₂ := by
  have h_ae_neq : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), t ≠ (1/2 : ℝ) := by
    rw [MeasureTheory.ae_iff]; simp
  refine periodVec_concat g₁ g₂ (fun i => h₁.integrable i) (fun i => h₂.integrable i) ?_ ?_ ?_ ?_
  · intro i
    have h_Ψ₁_shift : IntervalIntegrable
        (fun t => (periodBasisForm X i).toFun (g₁ (2 * t)) (pathSpeed g₁ (2 * t)))
        MeasureTheory.volume 0 (1/2) := by
      have h_mul := (h₁.integrable i).comp_mul_left (c := 2)
      convert h_mul using 2 <;> norm_num
    refine (h_Ψ₁_shift.const_mul (2:ℂ)).congr_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [h_ae_neq] with t h_neq ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at ht
    have h_lt : t < 1/2 := lt_of_le_of_ne ht.2 h_neq
    have h_2t_uIcc : 2 * t ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨by linarith [ht.1], by linarith⟩
    have h_ca : Jacobians.concat g₁ g₂ t = g₁ (2 * t) :=
      Jacobians.concat_apply_left _ _ (le_of_lt h_lt)
    have h_ps : pathSpeed (Jacobians.concat g₁ g₂) t = 2 * pathSpeed g₁ (2 * t) :=
      Jacobians.pathSpeed_concat_left _ _ t h_lt (h₁.diff (2 * t) h_2t_uIcc)
    show (2:ℂ) * (periodBasisForm X i).toFun (g₁ (2*t)) (pathSpeed g₁ (2*t)) =
      (periodBasisForm X i).toFun (Jacobians.concat g₁ g₂ t) (pathSpeed (Jacobians.concat g₁ g₂) t)
    rw [h_ca, h_ps]
    have h_lin := ((periodBasisForm X i).toFun (g₁ (2*t))).map_smul (2:ℂ) (pathSpeed g₁ (2*t))
    simp only [smul_eq_mul] at h_lin
    exact h_lin.symm
  · intro i
    have h_Ψ₂_shift : IntervalIntegrable
        (fun t => (periodBasisForm X i).toFun (g₂ (2 * t)) (pathSpeed g₂ (2 * t)))
        MeasureTheory.volume 0 (1/2) := by
      have h_mul := (h₂.integrable i).comp_mul_left (c := 2)
      convert h_mul using 2 <;> norm_num
    have h_Ψ₂_shift_2 : IntervalIntegrable
        (fun t => (periodBasisForm X i).toFun (g₂ (2 * t - 1)) (pathSpeed g₂ (2 * t - 1)))
        MeasureTheory.volume (1/2) 1 := by
      have h_sub := h_Ψ₂_shift.comp_sub_right (1/2)
      rw [show (0:ℝ) + 1/2 = 1/2 from by norm_num, show (1/2:ℝ) + 1/2 = 1 from by norm_num] at h_sub
      have h_fn_eq : (fun t : ℝ => (periodBasisForm X i).toFun (g₂ (2 * (t - 1/2)))
            (pathSpeed g₂ (2 * (t - 1/2)))) =
          (fun t : ℝ => (periodBasisForm X i).toFun (g₂ (2 * t - 1)) (pathSpeed g₂ (2 * t - 1))) := by
        funext t; rw [show (2:ℝ) * (t - 1/2) = 2 * t - 1 from by ring]
      rw [h_fn_eq] at h_sub; exact h_sub
    refine (h_Ψ₂_shift_2.const_mul (2:ℂ)).congr_ae ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [h_ae_neq] with t _h_neq ht
    rw [Set.uIoc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
    have h_gt : 1/2 < t := ht.1
    have h_2tm1_uIcc : 2 * t - 1 ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨by linarith, by linarith [ht.2]⟩
    have h_ca : Jacobians.concat g₁ g₂ t = g₂ (2 * t - 1) :=
      Jacobians.concat_apply_right _ _ (not_le.mpr h_gt)
    have h_ps : pathSpeed (Jacobians.concat g₁ g₂) t = 2 * pathSpeed g₂ (2 * t - 1) :=
      Jacobians.pathSpeed_concat_right _ _ t h_gt (h₂.diff (2 * t - 1) h_2tm1_uIcc)
    show (2:ℂ) * (periodBasisForm X i).toFun (g₂ (2*t-1)) (pathSpeed g₂ (2*t-1)) =
      (periodBasisForm X i).toFun (Jacobians.concat g₁ g₂ t) (pathSpeed (Jacobians.concat g₁ g₂) t)
    rw [h_ca, h_ps]
    have h_lin := ((periodBasisForm X i).toFun (g₂ (2*t-1))).map_smul (2:ℂ) (pathSpeed g₂ (2*t-1))
    simp only [smul_eq_mul] at h_lin
    exact h_lin.symm
  · intro i
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [h_ae_neq] with t h_neq ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1/2)] at ht
    have h_lt : t < 1/2 := lt_of_le_of_ne ht.2 h_neq
    have h_2t_uIcc : 2 * t ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨by linarith [ht.1], by linarith⟩
    have h_ca : Jacobians.concat g₁ g₂ t = g₁ (2 * t) :=
      Jacobians.concat_apply_left _ _ (le_of_lt h_lt)
    have h_ps : pathSpeed (Jacobians.concat g₁ g₂) t = 2 * pathSpeed g₁ (2 * t) :=
      Jacobians.pathSpeed_concat_left _ _ t h_lt (h₁.diff (2 * t) h_2t_uIcc)
    show (periodBasisForm X i).toFun (Jacobians.concat g₁ g₂ t) (pathSpeed (Jacobians.concat g₁ g₂) t) =
      (2:ℂ) * (periodBasisForm X i).toFun (g₁ (2*t)) (pathSpeed g₁ (2*t))
    rw [h_ca, h_ps]
    have h_lin := ((periodBasisForm X i).toFun (g₁ (2*t))).map_smul (2:ℂ) (pathSpeed g₁ (2*t))
    simp only [smul_eq_mul] at h_lin
    exact h_lin
  · intro i
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards [h_ae_neq] with t _h_neq ht
    rw [Set.uIoc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
    have h_gt : 1/2 < t := ht.1
    have h_2tm1_uIcc : 2 * t - 1 ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨by linarith, by linarith [ht.2]⟩
    have h_ca : Jacobians.concat g₁ g₂ t = g₂ (2 * t - 1) :=
      Jacobians.concat_apply_right _ _ (not_le.mpr h_gt)
    have h_ps : pathSpeed (Jacobians.concat g₁ g₂) t = 2 * pathSpeed g₂ (2 * t - 1) :=
      Jacobians.pathSpeed_concat_right _ _ t h_gt (h₂.diff (2 * t - 1) h_2tm1_uIcc)
    show (periodBasisForm X i).toFun (Jacobians.concat g₁ g₂ t) (pathSpeed (Jacobians.concat g₁ g₂) t) =
      (2:ℂ) * (periodBasisForm X i).toFun (g₂ (2*t-1)) (pathSpeed g₂ (2*t-1))
    rw [h_ca, h_ps]
    have h_lin := ((periodBasisForm X i).toFun (g₂ (2*t-1))).map_smul (2:ℂ) (pathSpeed g₂ (2*t-1))
    simp only [smul_eq_mul] at h_lin
    exact h_lin

/-- Membership helper: `t ∈ [0,1] → 1 - t ∈ [0,1]`. -/
private lemma one_sub_mem_uIcc {t : ℝ} (ht : t ∈ Set.uIcc (0:ℝ) 1) :
    (1:ℝ) - t ∈ Set.uIcc (0:ℝ) 1 := by
  rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht ⊢
  exact ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩

/-! ## Consolidated existence of a smooth-path family

The classical theorem (Forster §§1–2, 21): on a compact connected Riemann
surface there is a family of smooth paths between every pair of points with
(1) `IsSmoothPath P Q (sp P Q)` and (2) the basepoint-change cocycle
`[sp(P₀,A)] = [sp(P,A)] + [sp(P₀,P)]` mod the period lattice.

As of 2026-05-29 this is **no longer a single monolithic sorry**: it is
reduced (`exists_smoothPath_family`, proven below) to the focused kernel
`exists_zeroVel_smoothPath` (existence of a smooth path with zero endpoint
velocity), using `IsSmoothPath.concat`, `periodVec_concat_of_smooth`, and
`mk_periodVec_eq_of_endpoints`. The cocycle holds because the Jacobian class
depends only on endpoints and is additive under concatenation.

The provably-false third conjunct (unquotiented smoothness of
`Q ↦ periodVec (sp P Q)`) was removed 2026-05-28; see the project memory
`project_smoothpath_math_error`. -/
/-- A valid chart-ball hop `Q₀ → Q`: `Q` is in `Q₀`'s chart source and the
affine segment between their chart images stays in the chart target. Exactly
the hypotheses `ChartBallPathSmooth` needs. -/
def HopValid (Q₀ Q : X) : Prop :=
  Q ∈ (chartAt (H := ℂ) Q₀).source ∧
  ∀ s ∈ Set.Icc (0 : ℝ) 1,
    ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
      (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target

/-- A valid hop yields a smooth path with zero velocity at both endpoints
(`ChartBallPathSmooth` is smoothstep-reparametrized). -/
theorem zeroVelHop {Q₀ Q : X} (h : HopValid Q₀ Q) :
    IsSmoothPath Q₀ Q (ChartBallPathSmooth Q₀ Q) ∧
    pathSpeed (ChartBallPathSmooth Q₀ Q) 0 = 0 ∧
    pathSpeed (ChartBallPathSmooth Q₀ Q) 1 = 0 := by
  obtain ⟨hsrc, haff⟩ := h
  refine ⟨OfCurveSkeleton.isSmoothPath_ChartBallPathSmooth Q₀ Q hsrc haff, ?_, ?_⟩
  · show pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q ∘ smoothStep01) 0 = 0
    rw [OfCurveSkeleton.pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath Q₀ Q₀ Q) 0
        (Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q (smoothStep01 0)
          (haff (smoothStep01 0) (Jacobians.smoothStep01_mem_unit 0))),
      smoothStep01_deriv_zero, Complex.ofReal_zero, zero_mul]
  · show pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q ∘ smoothStep01) 1 = 0
    rw [OfCurveSkeleton.pathSpeed_smoothStep01_comp_eq (Jacobians.ChartBallPath Q₀ Q₀ Q) 1
        (Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q (smoothStep01 1)
          (haff (smoothStep01 1) (Jacobians.smoothStep01_mem_unit 1))),
      smoothStep01_deriv_one, Complex.ofReal_zero, zero_mul]

/-- Generic neighborhood cover of a path: given an open-neighborhood assignment
`W y ∋ y`, a continuous `γ` is covered segment-by-segment, each segment landing
in some `W (x k)`. (Generalizes `exists_chartCover` from chart sources to `W`.) -/
theorem exists_nbhd_cover (γ : ℝ → X) (hγ : Continuous γ)
    (W : X → Set X) (hW_open : ∀ y, IsOpen (W y)) (hW_mem : ∀ y, y ∈ W y) :
    ∃ (n : ℕ) (_hn : 0 < n) (x : Fin n → X),
      ∀ (k : Fin n) (s : ℝ),
        (k : ℝ) / n ≤ s → s ≤ ((k : ℝ) + 1) / n → γ s ∈ W (x k) := by
  set scc : Set ℝ := Set.Icc (0 : ℝ) 1 with hs_def
  set U : scc → Set ℝ := fun t => γ ⁻¹' W (γ t.1) with hU_def
  have hU_open : ∀ t : scc, IsOpen (U t) := fun t => (hW_open (γ t.1)).preimage hγ
  have hU_cover : scc ⊆ ⋃ t : scc, U t := by
    intro t ht
    exact Set.mem_iUnion.mpr ⟨⟨t, ht⟩, hW_mem (γ t)⟩
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric isCompact_Icc hU_open hU_cover
  obtain ⟨n, hn_gt⟩ : ∃ n : ℕ, 1 / δ < (n : ℝ) := exists_nat_gt _
  have hn_pos : 0 < n := by
    have h1 : (0 : ℝ) < 1 / δ := by positivity
    exact_mod_cast lt_trans h1 hn_gt
  have key : ∀ k : Fin n, ∃ x : X, ∀ y : ℝ,
      (k : ℝ) / n ≤ y → y ≤ ((k : ℝ) + 1) / n → γ y ∈ W x := by
    intro k
    set m : ℝ := ((k : ℝ) + 1/2) / n with hm_def
    have hm_mem : m ∈ scc := by
      refine ⟨?_, ?_⟩
      · apply div_nonneg
        · have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
          linarith
        · exact Nat.cast_nonneg _
      · rw [hm_def, div_le_one (by exact_mod_cast hn_pos)]
        have hk : (k : ℝ) + 1 ≤ n := by
          have : (k.val + 1 : ℕ) ≤ n := k.isLt
          exact_mod_cast this
        linarith
    obtain ⟨t₀, ht₀⟩ := hδ m hm_mem
    refine ⟨γ t₀.1, fun y hy_low hy_high => ?_⟩
    apply ht₀
    show y ∈ Metric.ball m δ
    rw [Metric.mem_ball, Real.dist_eq]
    have hn : (1 : ℝ) / n < δ := by
      have hn_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
      rw [div_lt_iff₀ hn_R]
      have h := mul_lt_mul_of_pos_left hn_gt hδ_pos
      have h_simp : δ * (1 / δ) = 1 := by field_simp
      linarith
    have h_dist : |y - m| ≤ 1 / (2 * n) := by
      rw [abs_sub_le_iff]
      refine ⟨?_, ?_⟩
      · have : y - m ≤ ((k : ℝ) + 1) / n - ((k : ℝ) + 1/2) / n := by linarith
        have heq : ((k : ℝ) + 1) / n - ((k : ℝ) + 1/2) / n = 1 / (2 * n) := by
          field_simp; ring
        linarith
      · have : m - y ≤ ((k : ℝ) + 1/2) / n - (k : ℝ) / n := by linarith
        have heq : ((k : ℝ) + 1/2) / n - (k : ℝ) / n = 1 / (2 * n) := by
          field_simp; ring
        linarith
    have h1 : (1 : ℝ) / (2 * n) ≤ 1 / n := by
      apply div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hn_pos)
      have hnn : (0 : ℝ) < n := by exact_mod_cast hn_pos
      nlinarith
    linarith
  classical
  exact ⟨n, hn_pos, fun k => (key k).choose,
    fun k y h1 h2 => (key k).choose_spec y h1 h2⟩

/-- Common-anchor segment: if a point `w` validly hops to both `u` and `v`,
then there is a zero-endpoint-velocity smooth path `u → v` (go `u → w` via the
reversed hop, then `w → v` via the forward hop). -/
theorem exists_zeroVelPath_of_common_anchor {w u v : X}
    (hu : HopValid w u) (hv : HopValid w v) :
    ∃ γ, IsSmoothPath u v γ ∧ pathSpeed γ 0 = 0 ∧ pathSpeed γ 1 = 0 := by
  obtain ⟨hu_sm, hu_v0, hu_v1⟩ := zeroVelHop hu
  obtain ⟨hv_sm, hv_v0, hv_v1⟩ := zeroVelHop hv
  have h0uIcc : (0:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_refl _, zero_le_one⟩
  have h1uIcc : (1:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
  -- reversed hop u → w, zero velocity at both ends
  have hrev_sm : IsSmoothPath u w (Jacobians.reverse (ChartBallPathSmooth w u)) := hu_sm.reverse
  have hrev_v0 : pathSpeed (Jacobians.reverse (ChartBallPathSmooth w u)) 0 = 0 := by
    rw [Jacobians.pathSpeed_reverse _ 0
        (by rw [show (1:ℝ)-0 = 1 from by norm_num]; exact hu_sm.diff 1 h1uIcc),
      show (1:ℝ)-0 = 1 from by norm_num, hu_v1, neg_zero]
  have hrev_v1 : pathSpeed (Jacobians.reverse (ChartBallPathSmooth w u)) 1 = 0 := by
    rw [Jacobians.pathSpeed_reverse _ 1
        (by rw [show (1:ℝ)-1 = 0 from by norm_num]; exact hu_sm.diff 0 h0uIcc),
      show (1:ℝ)-1 = 0 from by norm_num, hu_v0, neg_zero]
  refine ⟨Jacobians.concat (Jacobians.reverse (ChartBallPathSmooth w u)) (ChartBallPathSmooth w v),
    hrev_sm.concat hv_sm hrev_v1 hv_v0, ?_, ?_⟩
  · have hd : DifferentiableAt ℝ
        ((chartAt (H := ℂ) (Jacobians.reverse (ChartBallPathSmooth w u) (2 * 0))).toFun ∘
          Jacobians.reverse (ChartBallPathSmooth w u)) (2 * 0) := by
      rw [show (2:ℝ)*0 = 0 from by norm_num]; exact hrev_sm.diff 0 h0uIcc
    rw [Jacobians.pathSpeed_concat_left _ _ 0 (by norm_num) hd,
      show (2:ℝ)*0 = 0 from by norm_num, hrev_v0, mul_zero]
  · have hd : DifferentiableAt ℝ
        ((chartAt (H := ℂ) (ChartBallPathSmooth w v (2 * 1 - 1))).toFun ∘
          ChartBallPathSmooth w v) (2 * 1 - 1) := by
      rw [show (2:ℝ)*1-1 = 1 from by norm_num]; exact hv_sm.diff 1 h1uIcc
    rw [Jacobians.pathSpeed_concat_right _ (ChartBallPathSmooth w v) 1 (by norm_num) hd,
      show (2:ℝ)*1-1 = 1 from by norm_num, hv_v1, mul_zero]

/-- The `HopValid`-validity neighborhood of `y` (open, contains `y`). -/
def hopNbhd (y : X) : Set X := interior {Q | HopValid y Q}

theorem isOpen_hopNbhd (y : X) : IsOpen (hopNbhd y) := isOpen_interior

theorem self_mem_hopNbhd (y : X) : y ∈ hopNbhd y := by
  rw [hopNbhd, mem_interior_iff_mem_nhds]
  exact (OfCurveSkeleton.Q_in_chart_source_eventually y).and
    (OfCurveSkeleton.affine_in_target_eventually y)

theorem hopValid_of_mem_hopNbhd {y Q : X} (h : Q ∈ hopNbhd y) : HopValid y Q :=
  interior_subset (s := {Q' : X | HopValid y Q'}) h

/-- **Chart-ball cover (S1-B)**: a chain of zero-velocity smooth-path hops from
`P` to `Q`. Lebesgue-number cover of `continuousPath P Q`; each segment's
endpoints are reached from a common Lebesgue anchor via `exists_zeroVelPath_of_common_anchor`. -/
theorem exists_smoothChain (P Q : X) :
    ∃ (n : ℕ) (a : ℕ → X), a 0 = P ∧ a n = Q ∧
      ∀ k, k < n → ∃ γ, IsSmoothPath (a k) (a (k+1)) γ ∧
        pathSpeed γ 0 = 0 ∧ pathSpeed γ 1 = 0 := by
  set c : ℝ → X := fun t => (continuousPath P Q).extend t with hc_def
  have hc_cont : Continuous c := (continuousPath P Q).continuous_extend
  have hc0 : c 0 = P := Path.extend_zero _
  have hc1 : c 1 = Q := Path.extend_one _
  obtain ⟨n, hn_pos, x, hx⟩ :=
    exists_nbhd_cover c hc_cont hopNbhd isOpen_hopNbhd self_mem_hopNbhd
  refine ⟨n, fun j => c ((j : ℝ) / n), ?_, ?_, ?_⟩
  · show c (((0 : ℕ) : ℝ) / (n : ℝ)) = P
    rw [Nat.cast_zero, zero_div]; exact hc0
  · show c (((n : ℕ) : ℝ) / (n : ℝ)) = Q
    rw [div_self (by exact_mod_cast hn_pos.ne' : (n : ℝ) ≠ 0)]; exact hc1
  · intro k hk
    have hkn : (k : ℝ) / n ≤ (k : ℝ) / n := le_refl _
    have hk1n : (k : ℝ) / n ≤ ((k : ℝ) + 1) / n := by
      gcongr
      linarith
    have hkk1 : ((k : ℝ) + 1) / n ≤ ((k : ℝ) + 1) / n := le_refl _
    -- both endpoints land in hopNbhd (x ⟨k,hk⟩)
    have hu : HopValid (x ⟨k, hk⟩) (c ((k : ℝ) / n)) :=
      hopValid_of_mem_hopNbhd (hx ⟨k, hk⟩ ((k : ℝ) / n) hkn hk1n)
    have hv : HopValid (x ⟨k, hk⟩) (c (((k : ℝ) + 1) / n)) :=
      hopValid_of_mem_hopNbhd (hx ⟨k, hk⟩ (((k : ℝ) + 1) / n) hk1n hkk1)
    obtain ⟨γ, hγsm, hγv0, hγv1⟩ := exists_zeroVelPath_of_common_anchor hu hv
    refine ⟨γ, ?_, hγv0, hγv1⟩
    have hcast : ((k : ℝ) + 1) / n = ((k + 1 : ℕ) : ℝ) / n := by push_cast; ring
    rw [hcast] at hγsm
    exact hγsm

/-- **Generalized n-piece glue**: a chain of zero-velocity smooth-path hops
glues to a single zero-velocity smooth path, by induction on the chain length. -/
theorem exists_zeroVel_smoothPath_aux (a : ℕ → X) :
    ∀ n, (∀ k, k < n → ∃ γ, IsSmoothPath (a k) (a (k+1)) γ ∧
          pathSpeed γ 0 = 0 ∧ pathSpeed γ 1 = 0) →
      ∃ γ, IsSmoothPath (a 0) (a n) γ ∧ pathSpeed γ 0 = 0 ∧ pathSpeed γ 1 = 0 := by
  intro n
  induction n with
  | zero =>
    intro _
    exact ⟨fun _ => a 0, isSmoothPath_const (a 0),
      by rw [pathSpeed_const], by rw [pathSpeed_const]⟩
  | succ m ih =>
    intro hstep
    obtain ⟨γ, hγsm, hγv0, hγv1⟩ := ih (fun k hk => hstep k (by omega))
    obtain ⟨g, hgsm, hgv0, hgv1⟩ := hstep m (by omega)
    have h0uIcc : (0:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨le_refl _, zero_le_one⟩
    have h1uIcc : (1:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
    refine ⟨Jacobians.concat γ g, hγsm.concat hgsm hγv1 hgv0, ?_, ?_⟩
    · have hd : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ (2 * 0))).toFun ∘ γ) (2 * 0) := by
        rw [show (2:ℝ)*0 = 0 from by norm_num]; exact hγsm.diff 0 h0uIcc
      rw [Jacobians.pathSpeed_concat_left γ g 0 (by norm_num) hd,
        show (2:ℝ)*0 = 0 from by norm_num, hγv0, mul_zero]
    · have hd : DifferentiableAt ℝ ((chartAt (H := ℂ) (g (2 * 1 - 1))).toFun ∘ g) (2 * 1 - 1) := by
        rw [show (2:ℝ)*1-1 = 1 from by norm_num]; exact hgsm.diff 1 h1uIcc
      rw [Jacobians.pathSpeed_concat_right γ g 1 (by norm_num) hd,
        show (2:ℝ)*1-1 = 1 from by norm_num, hgv1, mul_zero]

/-- **S1 kernel, fully proven**: a zero-endpoint-velocity smooth path exists
between any two points (chart-ball cover glued by the n-piece induction). -/
theorem exists_zeroVel_smoothPath (P Q : X) :
    ∃ γ, IsSmoothPath P Q γ ∧ pathSpeed γ 0 = 0 ∧ pathSpeed γ 1 = 0 := by
  obtain ⟨n, a, ha0, han, hstep⟩ := exists_smoothChain P Q
  obtain ⟨γ, hsm, hv0, hv1⟩ := exists_zeroVel_smoothPath_aux a n hstep
  exact ⟨γ, ha0 ▸ han ▸ hsm, hv0, hv1⟩

theorem exists_smoothPath_family
    (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    ∃ sp : X → X → ℝ → X,
      (∀ P Q, IsSmoothPath P Q (sp P Q)) ∧
      (∀ P P₀ A,
        (QuotientAddGroup.mk (periodVec (sp P₀ A)) :
          (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
        QuotientAddGroup.mk (periodVec (sp P A)) +
        QuotientAddGroup.mk (periodVec (sp P₀ P))) := by
  choose sp hS hv0 hv1 using fun P Q => exists_zeroVel_smoothPath (X := X) P Q
  refine ⟨sp, hS, fun P P₀ A => ?_⟩
  have hadd : periodVec (Jacobians.concat (sp P₀ P) (sp P A)) =
      periodVec (sp P₀ P) + periodVec (sp P A) :=
    periodVec_concat_of_smooth (hS P₀ P) (hS P A)
  have hcc : IsSmoothPath P₀ A (Jacobians.concat (sp P₀ P) (sp P A)) :=
    (hS P₀ P).concat (hS P A) (hv1 P₀ P) (hv0 P A)
  have h1uIcc : (1:ℝ) ∈ Set.uIcc (0:ℝ) 1 := by
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨zero_le_one, le_refl _⟩
  have hcc_v1 : pathSpeed (Jacobians.concat (sp P₀ P) (sp P A)) 1 = 0 := by
    rw [Jacobians.pathSpeed_concat_right (sp P₀ P) (sp P A) 1 (by norm_num)
        (by rw [show (2:ℝ)*1-1 = 1 from by norm_num]; exact (hS P A).diff 1 h1uIcc),
      show (2:ℝ)*1-1 = 1 from by norm_num, hv1 P A, mul_zero]
  have hrev : IsSmoothPath A P₀ (Jacobians.reverse (Jacobians.concat (sp P₀ P) (sp P A))) :=
    hcc.reverse
  have hrev_v0 : pathSpeed (Jacobians.reverse (Jacobians.concat (sp P₀ P) (sp P A))) 0 = 0 := by
    rw [Jacobians.pathSpeed_reverse _ 0
        (by rw [show (1:ℝ)-0 = 1 from by norm_num]; exact hcc.diff 1 h1uIcc),
      show (1:ℝ)-0 = 1 from by norm_num, hcc_v1, neg_zero]
  have hloop : IsClosedSmoothLoop
      (Jacobians.concat (sp P₀ A) (Jacobians.reverse (Jacobians.concat (sp P₀ P) (sp P A)))) :=
    ((hS P₀ A).concat hrev (hv1 P₀ A) hrev_v0).toClosedSmoothLoop
  have hrevpv : periodVec (Jacobians.reverse (Jacobians.concat (sp P₀ P) (sp P A))) =
      -periodVec (Jacobians.concat (sp P₀ P) (sp P A)) :=
    Jacobians.periodVec_reverse _ (fun t ht => hcc.diff (1 - t) (one_sub_mem_uIcc ht))
  have hep : (QuotientAddGroup.mk (periodVec (sp P₀ A)) :
        (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
      QuotientAddGroup.mk (periodVec (Jacobians.concat (sp P₀ P) (sp P A))) := by
    refine mk_periodVec_eq_of_endpoints (sp P₀ A) (Jacobians.concat (sp P₀ P) (sp P A))
      ?_ hloop ?_
    · rw [(hS P₀ A).start, Jacobians.concat_apply_left _ _ (by norm_num : (0:ℝ) ≤ 1/2),
          show (2:ℝ)*0 = 0 from by norm_num, (hS P₀ P).start]
    · rw [periodVec_concat_of_smooth (hS P₀ A) hrev, hrevpv]; ring
  rw [hep, mk_periodVec_concat_eq_add (sp P₀ P) (sp P A) hadd, add_comm]

/-- The smooth path between `P` and `Q`, extracted via `Classical.choice`
from `exists_smoothPath_family`. -/
noncomputable def smoothPath (P Q : X) : ℝ → X :=
  (exists_smoothPath_family X).choose P Q

/-- The chosen smooth path satisfies `IsSmoothPath`. -/
theorem isSmoothPath_smoothPath (P Q : X) : IsSmoothPath P Q (smoothPath P Q) :=
  (exists_smoothPath_family X).choose_spec.1 P Q

/-- Boundary value: `smoothPath P Q 0 = P`. -/
@[simp] lemma smoothPath_zero (P Q : X) : smoothPath P Q 0 = P :=
  (isSmoothPath_smoothPath P Q).start

/-- Boundary value: `smoothPath P Q 1 = Q`. -/
@[simp] lemma smoothPath_one (P Q : X) : smoothPath P Q 1 = Q :=
  (isSmoothPath_smoothPath P Q).finish

/-- The `periodVec` of the smooth path from `P` to `P` is in the period
lattice (it's a closed smooth loop). -/
theorem periodVec_smoothPath_self_mem_lattice (P : X) :
    periodVec (smoothPath P P) ∈ truePeriodLattice X :=
  periodVec_mem_truePeriodLattice_of_closed _
    (isSmoothPath_smoothPath P P).toClosedSmoothLoop

/-- **Basepoint change for `smoothPath` modulo the period lattice**
(classical, Forster §21). Extracted from the second conjunct of
`exists_smoothPath_family`. -/
theorem smoothPath_basepoint_change (P P₀ A : X) :
    (QuotientAddGroup.mk (periodVec (smoothPath P₀ A)) :
      (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
    QuotientAddGroup.mk (periodVec (smoothPath P A)) +
    QuotientAddGroup.mk (periodVec (smoothPath P₀ P)) :=
  (exists_smoothPath_family X).choose_spec.2 P P₀ A

/-! ### Phase 4 support: change of variables under smooth maps

For `f : X → Y` smooth and `γ : ℝ → X` a path, the period vector of
the image loop `f ∘ γ` in `Y` is the `ambientPhi`-image of the period
vector of `γ` in `X`. This is the formal expression of "image of a
loop has period given by the pullback matrix" — the analytic content
that forces `ambientPhi` to preserve the lattice. -/

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Pullback of a `Y`-basis form via `f`, expressed in the `X`
basis coordinates.** Classical linear-algebra identity tying
`pullbackForm` to `ambientPsi`. Pure manipulation of the
`ambientIso`-based definitions; no analytic content. -/
theorem pullbackForm_periodBasisForm_eq (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (j : Fin (genus Y)) :
    pullbackForm f hf (periodBasisForm Y j) =
      ambientIso X (ambientPsi (gX := genus X) (gY := genus Y) f hf
        (Pi.basisFun ℂ (Fin (genus Y)) j)) := by
  unfold ambientPsi
  set_option linter.unusedSimpArgs false in
  simp only [dif_pos rfl]
  show pullbackForm f hf (periodBasisForm Y j) =
    ambientIso X (((ambientIso X).symm.toLinearMap.comp
      ((pullbackForm f hf).comp (ambientIso Y).toLinearMap) : _ →ₗ[_] _)
        (Pi.basisFun ℂ (Fin (genus Y)) j))
  simp [periodBasisForm, LinearMap.comp_apply]

/-- **Smooth loops compose with smooth maps.** If `γ : ℝ → X` is a
closed smooth loop and `f : X → Y` is smooth, then `f ∘ γ` is a
closed smooth loop in `Y`. Sub-lemmas:
1. Closedness: from `γ 0 = γ 1`.
2. Continuity: from continuity of `f` and `γ`.
3. Chart-pullback differentiability of `chart_Y ∘ (f ∘ γ)` at `t`:
   via the chart chain rule `f_loc ∘ (chart_X ∘ γ)` (proved inside
   `pathSpeed_comp_eq_mfderiv`).
4. Integrability of each Y-basis form along `f ∘ γ`: via
   `lineIntegral_pullback`, the integrand equals
   `(pullbackForm f hf (periodBasisForm Y j)).toFun (γ t) (pathSpeed γ t)`
   (at least a.e.), which is a ℂ-linear combination of X-basis
   integrands — each integrable by hypothesis.

**Content sorry**: the sub-lemmas 3 and 4 require replaying the
chart chain rule + linear-algebra arguments from elsewhere in the
file. Bounded but ~100 lines. -/
theorem IsClosedSmoothLoop.comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    {γ : ℝ → X} (hγ : IsClosedSmoothLoop γ) :
    IsClosedSmoothLoop (f ∘ γ) where
  closed := by simp [Function.comp_apply, hγ.closed]
  cont := hf.continuous.comp hγ.cont
  diff := by
    intro t ht
    -- Near t, (chartAt ℂ (f (γ t))).toFun ∘ (f ∘ γ) = f_loc ∘ (chart_X ∘ γ).
    set φ_X := chartAt (H := ℂ) (γ t)
    set φ_Y := chartAt (H := ℂ) (f (γ t))
    set f_loc : ℂ → ℂ := fun z => φ_Y (f (φ_X.symm z))
    set g_X : ℝ → ℂ := φ_X.toFun ∘ γ
    have hγ_source : ∀ᶠ s in 𝓝 t, γ s ∈ φ_X.source :=
      hγ.cont.continuousAt.eventually
        (φ_X.open_source.mem_nhds (mem_chart_source ℂ (γ t)))
    have h_eq : (φ_Y.toFun ∘ (f ∘ γ)) =ᶠ[𝓝 t] f_loc ∘ g_X := by
      filter_upwards [hγ_source] with s hs
      simp only [Function.comp_apply]
      congr 2
      exact (φ_X.left_inv hs).symm
    have hf_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (γ t) :=
      hf.mdifferentiableAt (by decide : ω ≠ 0)
    have hf_loc_diff_ℂ : DifferentiableAt ℂ f_loc (g_X t) := by
      have h1 := hf_mdiff.differentiableWithinAt_writtenInExtChartAt
      rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
      convert h1 using 2
    -- Bypass the ℝ/ℂ diamond: construct ℝ-HasFDerivAt manually.
    have hf_loc_hasFD_ℂ : HasFDerivAt f_loc (fderiv ℂ f_loc (g_X t)) (g_X t) :=
      hf_loc_diff_ℂ.hasFDerivAt
    have hf_loc_hasFD_ℝ : HasFDerivAt f_loc
        ((fderiv ℂ f_loc (g_X t)).restrictScalars ℝ) (g_X t) := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hf_loc_hasFD_ℂ ⊢
      simp only [ContinuousLinearMap.coe_restrictScalars']
      exact hf_loc_hasFD_ℂ
    have hf_loc_diff_ℝ : DifferentiableAt ℝ f_loc (g_X t) :=
      hf_loc_hasFD_ℝ.differentiableAt
    have h_comp_diff : DifferentiableAt ℝ (f_loc ∘ g_X) t :=
      hf_loc_diff_ℝ.comp t (hγ.diff t ht)
    exact (h_eq.differentiableAt_iff).mpr h_comp_diff
  integrable := by
    intro j
    -- The integrand for f ∘ γ equals the integrand of pullbackForm f hf (periodBasisForm Y j)
    -- along γ, via the pointwise chain rule (pathSpeed_comp_eq_mfderiv).
    -- The pullbackForm is a ℂ-linear combination of periodBasisForm X i, each of whose
    -- integrands is integrable against γ (by hγ.integrable).
    have h_pw : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        (periodBasisForm Y j).toFun ((f ∘ γ) t) (pathSpeed (f ∘ γ) t) =
          (pullbackForm f hf (periodBasisForm Y j)).toFun (γ t) (pathSpeed γ t) := by
      intro t ht
      show (periodBasisForm Y j).toFun (f (γ t)) (pathSpeed (f ∘ γ) t) =
        ((periodBasisForm Y j).toFun (f (γ t))).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) f (γ t))
          (pathSpeed γ t)
      rw [ContinuousLinearMap.comp_apply,
        pathSpeed_comp_eq_mfderiv f hf γ t hγ.cont.continuousAt (hγ.diff t ht)]
    -- Pullback form as a sum: ambientIso X v with v = ambientPsi f hf e_j.
    set v := ambientPsi (gX := genus X) (gY := genus Y) f hf
      (Pi.basisFun ℂ (Fin (genus Y)) j)
    have h_pullback_sum : pullbackForm f hf (periodBasisForm Y j) =
        ∑ i, v i • periodBasisForm X i := by
      rw [pullbackForm_periodBasisForm_eq]
      show ambientIso X v = _
      have h_v_decomp : v = ∑ i, v i • Pi.basisFun ℂ (Fin (genus X)) i := by
        have := pi_eq_sum_univ' v
        convert this using 2
        simp [Pi.basisFun_apply]
      conv_lhs => rw [h_v_decomp, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_smul]
      rfl
    -- The integrand along γ of the sum is the sum of integrands.
    have h_integrand_sum : ∀ t,
        (pullbackForm f hf (periodBasisForm Y j)).toFun (γ t) (pathSpeed γ t) =
          ∑ i, v i * (periodBasisForm X i).toFun (γ t) (pathSpeed γ t) := by
      intro t
      rw [h_pullback_sum]
      -- Same Finset induction as in periodVec_pushforward_of_smooth.
      induction (Finset.univ : Finset (Fin (genus X))) using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        show (0 : HolomorphicOneForms X).toFun (γ t) (pathSpeed γ t) = 0
        rfl
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        show ((v a • periodBasisForm X a) + ∑ i ∈ s, v i • periodBasisForm X i).toFun (γ t)
            (pathSpeed γ t) = _
        rw [show ((v a • periodBasisForm X a) + ∑ i ∈ s, v i • periodBasisForm X i).toFun (γ t) =
            (v a • periodBasisForm X a).toFun (γ t) +
              (∑ i ∈ s, v i • periodBasisForm X i).toFun (γ t) from rfl,
          ContinuousLinearMap.add_apply, ih]
        rfl
    -- Integrability of the sum via Finset.sum of integrable summands.
    have h_sum_integrable : IntervalIntegrable
        (fun t => ∑ i, v i * (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
        MeasureTheory.volume 0 1 := by
      rw [show (fun t => ∑ i, v i * (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)) =
        ∑ i : Fin (genus X),
          (fun t => v i * (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)) from by
        funext t; simp [Finset.sum_apply]]
      refine IntervalIntegrable.sum _ (fun i _ => ?_)
      exact (hγ.integrable i).const_mul (v i)
    -- Combine: h_pw + h_integrand_sum give a.e. equality; use congr.
    refine h_sum_integrable.congr_ae ?_
    rw [Filter.EventuallyEq]
    refine (MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr ?_
    filter_upwards with t ht
    rw [← h_integrand_sum]
    exact (h_pw t (Set.uIoc_subset_uIcc ht)).symm

/-- Change-of-variables at the vector level: evaluating each Y-basis
form against `f ∘ γ` equals evaluating its pullback against `γ`.
Requires path regularity hypotheses (inherited from `lineIntegral_pullback`). -/
theorem periodVec_comp_eq_lineIntegral_pullback
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (γ : ℝ → X) (j : Fin (genus Y))
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) :
    periodVec (f ∘ γ) j =
      lineIntegral (pullbackForm f hf (periodBasisForm Y j)) γ := by
  unfold periodVec
  exact lineIntegral_pullback f hf (periodBasisForm Y j) γ hγ_cont hγ_diff

/-- **Key identity**: the period vector of the image loop equals
`ambientPhi` applied to the period vector of the source loop.

With `periodBasisForm Y j = ambientIso Y e_j^Y`, the pullback
`pullbackForm f hf (periodBasisForm Y j)` expanded in the `X`-basis
has coefficients `(ambientPsi f hf e_j^Y) i = M_ij`. Then:

  `(ambientPhi f hf v)_j = ∑_i M_ij v_i`

matches:

  `periodVec Y (f∘γ) j = ∫_γ pullbackForm f hf (basis_j^Y)
                       = ∑_i M_ij (periodVec X γ)_i`.

Uses `lineIntegral_pullback` + linearity of `lineIntegral` via basis
expansion. Requires path regularity (the hypotheses of
`IsClosedSmoothLoop`). -/
theorem periodVec_pushforward
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (γ : ℝ → X)
    (hγ_cont : Continuous γ)
    (hγ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t)
    (hint_X : ∀ i : Fin (genus X), IntervalIntegrable
      (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
        MeasureTheory.volume 0 1) :
    periodVec (f ∘ γ) =
      ambientPhi (gX := genus X) (gY := genus Y) f hf (periodVec γ) := by
  funext j
  show lineIntegral (periodBasisForm Y j) (f ∘ γ) =
    ambientPhi (gX := genus X) (gY := genus Y) f hf (periodVec γ) j
  rw [lineIntegral_pullback f hf _ γ hγ_cont hγ_diff]
  rw [pullbackForm_periodBasisForm_eq]
  -- Goal: lineIntegral (ambientIso X (ambientPsi f hf e_j^Y)) γ = (ambientPhi f hf (periodVec γ)) j
  set v := ambientPsi (gX := genus X) (gY := genus Y) f hf
    (Pi.basisFun ℂ (Fin (genus Y)) j) with hv_def
  -- Step 1: ambientIso X v = ∑ i, v i • periodBasisForm X i
  have h_iso_sum : ambientIso X v = ∑ i, v i • periodBasisForm X i := by
    have h_v_decomp : v = ∑ i, v i • Pi.basisFun ℂ (Fin (genus X)) i := by
      have := pi_eq_sum_univ' v
      convert this using 2
      simp [Pi.basisFun_apply]
    conv_lhs => rw [h_v_decomp, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul]
    rfl
  rw [h_iso_sum]
  -- Step 2: lineIntegral distributes over the Finset sum (needs integrability).
  have h_sum_lineIntegral : lineIntegral (∑ i, v i • periodBasisForm X i) γ =
      ∑ i, v i * lineIntegral (periodBasisForm X i) γ := by
    unfold lineIntegral
    have h_pw : ∀ t : ℝ,
        (∑ i, v i • periodBasisForm X i).toFun (γ t) (pathSpeed γ t) =
          ∑ i, v i * (periodBasisForm X i).toFun (γ t) (pathSpeed γ t) := by
      intro t
      -- Unfold toFun on a finset sum of smul'd sections.
      induction (Finset.univ : Finset (Fin (genus X))) using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        show (0 : HolomorphicOneForms X).toFun (γ t) (pathSpeed γ t) = 0
        rfl
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        show ((v a • periodBasisForm X a) + ∑ i ∈ s, v i • periodBasisForm X i).toFun (γ t)
            (pathSpeed γ t) = _
        rw [show ((v a • periodBasisForm X a) + ∑ i ∈ s, v i • periodBasisForm X i).toFun (γ t) =
            (v a • periodBasisForm X a).toFun (γ t) +
              (∑ i ∈ s, v i • periodBasisForm X i).toFun (γ t) from rfl,
          ContinuousLinearMap.add_apply, ih]
        show v a * (periodBasisForm X a).toFun (γ t) (pathSpeed γ t) +
            ∑ i ∈ s, v i * (periodBasisForm X i).toFun (γ t) (pathSpeed γ t) =
          v a * (periodBasisForm X a).toFun (γ t) (pathSpeed γ t) +
            ∑ i ∈ s, v i * (periodBasisForm X i).toFun (γ t) (pathSpeed γ t)
        rfl
    simp_rw [h_pw]
    rw [intervalIntegral.integral_finset_sum (s := Finset.univ)
      (f := fun i t => v i * (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
      (fun i _ => (hint_X i).const_mul (v i))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact intervalIntegral.integral_const_mul _ _
  rw [h_sum_lineIntegral]
  -- Step 3: (ambientPhi f hf (periodVec γ)) j = ∑ i, v i * (periodVec γ) i (matrix transpose).
  show ∑ i, v i * lineIntegral (periodBasisForm X i) γ =
    (ambientPhi f hf (periodVec γ)) j
  have h_ambientPhi : (ambientPhi f hf (periodVec γ)) j = ∑ i, v i * (periodVec γ) i := by
    show (Matrix.transpose (LinearMap.toMatrix
      (Pi.basisFun ℂ (Fin (genus Y))) (Pi.basisFun ℂ (Fin (genus X)))
      (ambientPsi f hf).toLinearMap)).mulVecLin (periodVec γ) j =
      ∑ i, v i * (periodVec γ) i
    rw [Matrix.mulVecLin_apply]
    show ∑ i, (Matrix.transpose (LinearMap.toMatrix _ _ _)) j i * (periodVec γ) i =
      ∑ i, v i * (periodVec γ) i
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    show (LinearMap.toMatrix (Pi.basisFun ℂ (Fin (genus Y)))
      (Pi.basisFun ℂ (Fin (genus X))) (ambientPsi f hf).toLinearMap) i j = v i
    rw [LinearMap.toMatrix_apply]
    show ((Pi.basisFun ℂ (Fin (genus X))).repr
      (ambientPsi f hf (Pi.basisFun ℂ (Fin (genus Y)) j))) i = v i
    rw [Pi.basisFun_repr]
  rw [h_ambientPhi]
  -- Goal: ∑ i, v i * lineIntegral (periodBasisForm X i) γ = ∑ i, v i * (periodVec γ) i
  rfl

/-- **Discrete topology on the period lattice** — classical fact
(Forster §§20–21). Follows from Hodge decomposition + non-degeneracy
of the period pairing. Not currently in Mathlib. -/
instance : DiscreteTopology (truePeriodLattice X) := sorry

/-- **Period lattice is a ℤ-lattice of full real rank** — classical
fact (Forster §§20–21). Rank `2 * genus X` in `ℂ^(genus X) = ℝ^(2 g)`.
Follows from Hodge decomposition + non-degeneracy of the period pairing.
Not currently in Mathlib. -/
instance : IsZLattice ℝ (truePeriodLattice X) := sorry

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
  · -- member case: γ ∈ closedLoopPeriods carries IsClosedSmoothLoop.
    rintro _ ⟨γ, hγ, rfl⟩
    rw [← periodVec_pushforward f hf γ hγ.cont hγ.diff hγ.integrable]
    -- f ∘ γ is IsClosedSmoothLoop via `IsClosedSmoothLoop.comp`.
    exact periodVec_mem_truePeriodLattice_of_closed (f ∘ γ) (hγ.comp f hf)
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

/-! ### Phase 4b: `ambientPsi` preserves the period lattice

This is the **trace / pullback-of-cycle direction**. Split by whether
`f` is constant:

**Constant case (real)**: if `f x = y₀` for all `x`, then
`mfderiv f x = 0` (by `mfderiv_const`), so `pullbackForm f hf = 0`
(pointwise composition with zero), so `ambientPsi f hf = 0`. Hence
the image is `0 ∈ truePeriodLattice X` for free.

**Non-constant case (content-gated)**: `f` is a branched cover of
some degree `d ≥ 1`; the preimage `f⁻¹(δ)` is a ℤ-cycle in `X` and
the trace identity places `ambientPsi (periodVec δ)` in the period
lattice (Forster §10.11). Real infrastructure required: branched-cover
lift existence + trace adjunction (~200–500 lines not yet in place). -/

/-- **pullbackForm of a constant map is zero.** If `f` is constant,
then `mfderiv f x = 0` everywhere, making the pointwise composition
`α(f x) ∘ mfderiv f x = 0`. -/
theorem pullbackForm_eq_zero_of_const
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hconst : ∃ y₀ : Y, ∀ x, f x = y₀) :
    pullbackForm f hf = 0 := by
  obtain ⟨y₀, hy₀⟩ := hconst
  ext α
  apply ContMDiffSection.ext
  intro x
  show (α.toFun (f x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x) = 0
  have : mfderiv 𝓘(ℂ) 𝓘(ℂ) f x = 0 := by
    have hfconst : f = fun _ => y₀ := funext hy₀
    rw [hfconst]
    exact mfderiv_const
  rw [this, ContinuousLinearMap.comp_zero]

/-- **ambientPsi of a constant map is zero.** Follows from
`pullbackForm_eq_zero_of_const`: `ambientPsi = iso⁻¹ ∘ pullbackForm ∘ iso`,
and composition with zero is zero. -/
theorem ambientPsi_eq_zero_of_const
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hconst : ∃ y₀ : Y, ∀ x, f x = y₀) :
    ambientPsi (gX := genus X) (gY := genus Y) f hf = 0 := by
  unfold ambientPsi
  simp only [dite_true]
  rw [pullbackForm_eq_zero_of_const f hf hconst]
  ext v i
  simp

/-- A **preimage cycle** witnessing the trace identity: a finite
ℤ-combination of closed smooth loops in `X` whose period-vector sum
equals `ambientPsi f hf (periodVec δ)`.

Classically: for non-constant holomorphic `f : X → Y` between compact
Riemann surfaces, `f` is a branched cover of some degree `d ≥ 1`,
and the set-theoretic preimage `f⁻¹(δ)` of a loop `δ` (avoiding
branch points) is `d` disjoint closed loops in `X` whose signed sum
realizes `ambientPsi (periodVec δ)` (Forster §10.11).

Defining `PreimageCycle` as a bundle of (loops + coefficients +
trace equation) lets us isolate the classical content: the theorem
`ambientPsi_periodVec_mem_truePeriodLattice_of_preimageCycle` is
real and purely algebraic; only *producing* a `PreimageCycle` for
each non-constant `f, δ` is content-gated. -/
structure PreimageCycle (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (δ : ℝ → Y) where
  /-- Number of lifts. -/
  n : ℕ
  /-- The lifted closed loops in X. -/
  loops : Fin n → ℝ → X
  /-- Each lift is a closed smooth loop. -/
  loops_smooth : ∀ i, IsClosedSmoothLoop (loops i)
  /-- Integer coefficients (signed lifts / branching multiplicities). -/
  coeffs : Fin n → ℤ
  /-- The trace identity: `ambientPsi` on `periodVec δ` equals the
  ℤ-combination of `periodVec`s of the lifts. -/
  trace_eq : ambientPsi (gX := genus X) (gY := genus Y) f hf (periodVec δ) =
    ∑ i, coeffs i • periodVec (loops i)

/-- **Trace identity — algebraic reduction.** Given a `PreimageCycle`
witness for `(f, δ)`, the pulled-back period vector
`ambientPsi (periodVec δ)` lies in `truePeriodLattice X`: each
`periodVec` of a closed smooth loop is in the lattice, and the
lattice is closed under ℤ-linear combinations. -/
theorem ambientPsi_periodVec_mem_truePeriodLattice_of_preimageCycle
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (δ : ℝ → Y) (c : PreimageCycle f hf δ) :
    ambientPsi (gX := genus X) (gY := genus Y) f hf (periodVec δ) ∈
      truePeriodLattice X := by
  rw [c.trace_eq]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ (c.coeffs i)
      (periodVec_mem_truePeriodLattice_of_closed _ (c.loops_smooth i))

/-! #### Branched-cover infrastructure (incremental)

For non-constant holomorphic `f : X → Y` between compact connected
Riemann surfaces:

* `criticalSet f` := `{x | mfderiv f x = 0}` — the ramification locus.
* `branchLocus f` := `f '' criticalSet f` — image of critical points.

Classical facts (partially in place, partially axiomatized):
* `criticalSet` is closed (preimage of `{0}` under the continuous
  `mfderiv` section).
* For non-constant `f`, `criticalSet f ≠ Set.univ` (open mapping
  theorem applied locally in charts).
* `criticalSet` is discrete in `X` (isolated zeros of a non-zero
  analytic function in local coords).
* Being closed + discrete in compact `X`, `criticalSet` is FINITE.
* On `X ∖ criticalSet`, `f` is a local diffeomorphism (inverse
  function theorem).
* On `Y ∖ branchLocus`, `f` restricts to a finite covering.
* Closed loops in `Y ∖ branchLocus` admit lifts to closed loops in
  `X ∖ criticalSet` (covering-space path lifting).
* Loops meeting `branchLocus` can be homotoped off it (removing
  finitely many points from a connected manifold preserves π₁ access).

Each step below is stated as a theorem; real proofs fill in in
subsequent commits. -/

/-- **Critical set of a holomorphic map** between complex 1-manifolds.

Defined as `Jacobians.Discharge.Manifold.criticalSetGeneral f` — the set of
points at which `f` is not locally injective. Classically equivalent to
`{x | mfderiv f x = 0}` for analytic maps between complex 1-manifolds
(the planar bridge ZZ99 / Forster §I.7); the local-injectivity definition is
the one supported by the imported discharge infrastructure, which gives us
closedness, ne-univ, and finiteness directly. -/
def criticalSet (f : X → Y) : Set X :=
  Jacobians.Discharge.Manifold.criticalSetGeneral f

/-- **Branch locus**: the image of the critical set. -/
def branchLocus (f : X → Y) : Set Y :=
  f '' criticalSet f

/-- **Critical set is closed.** The not-locally-injective set is closed via
the discharge's `isClosed_criticalSetGeneral` (CriticalSetClosed). -/
theorem isClosed_criticalSet (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    IsClosed (criticalSet f) :=
  Jacobians.Discharge.Manifold.isClosed_criticalSetGeneral f

/-- **Critical set of a non-constant map is not everything.** Discharge
proves `(criticalSet f).Finite`; `X` is infinite (a compact connected
complex 1-manifold has an open chart into ℂ which contains an open ball,
hence infinitely many points); so `criticalSet f ≠ univ`. -/
theorem criticalSet_ne_univ_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    criticalSet f ≠ Set.univ := by
  intro h_eq
  have h_fin : (criticalSet f).Finite :=
    Jacobians.Discharge.Manifold.criticalSet_finite_general f hf hnonconst
  rw [h_eq] at h_fin
  haveI : Infinite X :=
    Jacobians.Discharge.ContMDiff.Degree.y_infinite_of_chartedSpace_complex
  exact Set.infinite_univ.not_finite h_fin

/-- **Critical set is finite** (Forster §4 / isolated-zeros). For
non-constant holomorphic `f`, `criticalSet f` is finite. Direct forward
to discharge's `criticalSet_finite_general`. -/
theorem finite_criticalSet_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    (criticalSet f).Finite :=
  Jacobians.Discharge.Manifold.criticalSet_finite_general f hf hnonconst

/-- **Branch locus is finite.** Image of a finite set is finite. -/
theorem finite_branchLocus_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    (branchLocus f).Finite :=
  (finite_criticalSet_of_nonconstant f hf hnonconst).image f

/-! ## §1 Local structure of non-constant holomorphic maps

Non-constant holomorphic maps between Riemann surfaces are open and discrete
(Forster §4.2); off the branch locus they are local homeomorphisms (§4.4), and
since a compact source makes them proper, they restrict to finite-sheeted
coverings off the branch locus (§4.22–4.23). The open-mapping half is proven
below (`isOpenMap_of_nonconstant`). -/

/-- Chart pullback of `f` at `x`. -/
noncomputable def chartPullback (f : X → Y) (x : X) : ℂ → ℂ :=
  (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm

theorem analyticAt_chartPullback (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x : X) :
    AnalyticAt ℂ (chartPullback f x) ((chartAt ℂ x) x) :=
  Jacobians.Discharge.ContMDiff.Degree.contMDiffAt_omega_analyticAt_chart_pullback (hf x)

/-- **Local open mapping at `x`** (provided the chart pullback is not locally
constant there): `f` sends neighborhoods of `x` to neighborhoods of `f x`. This
is the heart of the open mapping theorem, transferred through the charts. -/
theorem nhds_le_map_of_chartPullback_not_eventuallyConst
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x : X)
    (hnc : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x), chartPullback f x z = chartPullback f x ((chartAt ℂ x) x)) :
    𝓝 (f x) ≤ Filter.map f (𝓝 x) := by
  set φ := chartAt ℂ x with hφ
  set ψ := chartAt ℂ (f x) with hψ
  set g := chartPullback f x with hg
  have hxφ : x ∈ φ.source := mem_chart_source ℂ x
  have hfxψ : f x ∈ ψ.source := mem_chart_source ℂ (f x)
  -- g is open at φ x: from analyticity + not-locally-constant, `nhds_le_map_nhds`.
  have hgA : AnalyticAt ℂ g (φ x) := analyticAt_chartPullback f hf x
  have hg_open : 𝓝 (g (φ x)) ≤ Filter.map g (𝓝 (φ x)) :=
    hgA.eventually_constant_or_nhds_le_map_nhds.resolve_left hnc
  -- g (φ x) = ψ (f x).
  have hgφx : g (φ x) = ψ (f x) := by
    simp only [hg, chartPullback, Function.comp_apply]
    rw [φ.left_inv hxφ]
  -- 𝓝 x = map φ.symm (𝓝 (φ x)).
  have hnx : Filter.map φ.symm (𝓝 (φ x)) = 𝓝 x := φ.symm_map_nhds_eq hxφ
  -- 𝓝 (f x) = map ψ.symm (𝓝 (ψ (f x))).
  have hnfx : Filter.map ψ.symm (𝓝 (ψ (f x))) = 𝓝 (f x) := ψ.symm_map_nhds_eq hfxψ
  -- f ∘ φ.symm =ᶠ[𝓝 (φ x)] ψ.symm ∘ g  near φ x.
  have hev : (f ∘ φ.symm) =ᶠ[𝓝 (φ x)] (ψ.symm ∘ g) := by
    have hφxtarget : φ x ∈ φ.target := φ.map_source hxφ
    have hcont : ContinuousAt (fun z => f (φ.symm z)) (φ x) :=
      hf.continuous.continuousAt.comp
        (φ.continuousOn_symm.continuousAt (φ.open_target.mem_nhds hφxtarget))
    have hval : f (φ.symm (φ x)) = f x := by rw [φ.left_inv hxφ]
    have hsrc_nhds : ψ.source ∈ 𝓝 (f (φ.symm (φ x))) := by
      rw [hval]; exact ψ.open_source.mem_nhds hfxψ
    have hpre : ∀ᶠ z in 𝓝 (φ x), f (φ.symm z) ∈ ψ.source :=
      hcont.preimage_mem_nhds hsrc_nhds
    filter_upwards [hpre] with z hz
    show f (φ.symm z) = ψ.symm (g z)
    simp only [hg, chartPullback, Function.comp_apply]
    rw [ψ.left_inv hz]
  -- assemble: 𝓝 (f x) ≤ map f (𝓝 x)
  calc 𝓝 (f x) = Filter.map ψ.symm (𝓝 (ψ (f x))) := hnfx.symm
    _ ≤ Filter.map ψ.symm (Filter.map g (𝓝 (φ x))) := by
          rw [← hgφx]; exact Filter.map_mono hg_open
    _ = Filter.map (ψ.symm ∘ g) (𝓝 (φ x)) := by rw [Filter.map_map]
    _ = Filter.map (f ∘ φ.symm) (𝓝 (φ x)) := by rw [Filter.map_congr hev.symm]
    _ = Filter.map f (Filter.map φ.symm (𝓝 (φ x))) := by rw [Filter.map_map]
    _ = Filter.map f (𝓝 x) := by rw [hnx]

/-- **[open]** The chart pullback of a non-constant holomorphic map is
not locally constant at any chart image. This is the *globalized identity
theorem*: from `f` non-constant globally, walk analytic continuation across a
chain of overlapping charts (a path from `x` to a point where `f` differs) to
rule out local constancy at `x`. The repo's `AnalyticContinuationGlobalization`
isolates exactly this as deferred (the local within-chart version
`not_eventually_const_at_chartImage` is proven there; the cross-chart
globalization is the remaining analytic input). -/
theorem chartPullback_not_eventuallyConst (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (x : X) :
    ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x),
      chartPullback f x z = chartPullback f x ((chartAt ℂ x) x) :=
  sorry

/-- **[PROVEN modulo `chartPullback_not_eventuallyConst`]** A non-constant
holomorphic map between Riemann surfaces is an open map. Assembled from the
proven open-mapping transfer `nhds_le_map_of_chartPullback_not_eventuallyConst`
and the (refined) non-constancy lemma. -/
theorem isOpenMap_of_nonconstant (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    IsOpenMap f := by
  rw [isOpenMap_iff_nhds_le]
  intro x
  exact nhds_le_map_of_chartPullback_not_eventuallyConst f hf x
    (chartPullback_not_eventuallyConst f hf hnonconst x)

/-- **[PROVEN]** A non-constant holomorphic map between compact connected
Riemann surfaces is surjective: its range is open (open mapping), closed
(continuous image of compact in a T2 space), and nonempty, hence clopen, hence
all of the connected target `Y`. -/
theorem surjective_of_nonconstant (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    Function.Surjective f := by
  have hopen : IsOpen (Set.range f) := (isOpenMap_of_nonconstant f hf hnonconst).isOpen_range
  have hclosed : IsClosed (Set.range f) := (isCompact_range hf.continuous).isClosed
  have hclopen : IsClopen (Set.range f) := ⟨hclosed, hopen⟩
  rcases isClopen_iff.mp hclopen with h | h
  · exact absurd h (Set.range_nonempty f).ne_empty
  · exact Set.range_eq_univ.mp h

/-! ## §2 Homotopy invariance and genericity

The supporting classical fact (stated only in prose to avoid an unsound
placeholder lemma): **`periodVec` is homotopy-invariant** — homotopic closed
smooth loops have equal period vectors, because the period forms are closed
holomorphic 1-forms and `∫_γ ω` depends only on the homotopy class by Stokes on
the homotopy cylinder (Forster §10.5; Mathlib lacks manifold Stokes). Stating
it as a Lean lemma requires the right smooth-homotopy hypothesis (a genuine
homotopy of loops), which we fold directly into `exists_loop_off_branchLocus`
below rather than asserting separately. -/

/-- **[open]** A closed smooth loop in `Y` can be homotoped off the finite
branch locus without changing its period vector. Genericity: `branchLocus f`
is finite (`finite_branchLocus_of_nonconstant`), hence has real codimension 2
in the surface `Y`, so a generic loop avoids it; homotopy invariance of
`periodVec` (see §2 note) preserves the period. -/
theorem exists_loop_off_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    ∃ δ', IsClosedSmoothLoop δ' ∧ periodVec δ' = periodVec δ ∧
      (∀ t : ℝ, δ' t ∉ branchLocus f) :=
  sorry

/-! ## §3 Lifting and the preimage cycle -/

/-- **[open]** A closed smooth loop off the branch locus lifts to a preimage
cycle. Construction (Forster §4.22–4.23 + §4.14): on compact `X`, non-constant
holomorphic `f` is proper, so off the branch locus it restricts to a finite
unbranched covering `X ∖ f⁻¹(B) → Y ∖ B` (proper local homeo ⇒ covering map);
lift `δ` from each sheet (`IsCoveringMap.liftPath`, Forster §4.14); group the
lifts into closed loops along the monodromy permutation's orbits (smoothness of
each lift from the local-diffeo covering); the period trace identity
`ambientPsi (periodVec δ) = ∑ periodVec (orbit loop)` holds because pulling back
the basis forms along the sheets and summing reproduces `ambientPsi` (the
change-of-variables / trace of `pullbackForm`). The covering structure
(`IsCoveringMapOn f (univ ∖ branchLocus f)`) is the natural sub-lemma to
re-introduce here, proven via Mathlib's proper-map/covering API. -/
theorem exists_preimageCycle_of_off_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f) :
    Nonempty (PreimageCycle f hf δ) :=
  sorry

/-! ## §4 Proven glue + assembly -/

/-- **[PROVEN]** A `PreimageCycle` depends on `δ` only through `periodVec δ`
(the only place `δ` enters the data is the trace identity's left-hand side).
Transporting along a period-vector equality reuses the same loops/coeffs. -/
def PreimageCycle.congr_periodVec {f : X → Y} {hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f}
    {δ δ' : ℝ → Y} (h : periodVec δ = periodVec δ') (c : PreimageCycle f hf δ') :
    PreimageCycle f hf δ where
  n := c.n
  loops := c.loops
  loops_smooth := c.loops_smooth
  coeffs := c.coeffs
  trace_eq := by rw [h]; exact c.trace_eq

/-- **[PROVEN]** `exists_preimageCycle_of_nonconstant`, assembled: homotope `δ`
off the branch locus (B2), lift it to a preimage cycle (C), and transport back
along the period-vector equality (`congr_periodVec`). -/
theorem exists_preimageCycle_of_nonconstant (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    Nonempty (PreimageCycle f hf δ) := by
  obtain ⟨δ', hδ', hpv, havoid⟩ := exists_loop_off_branchLocus f hf hnonconst δ hδ
  obtain ⟨c⟩ := exists_preimageCycle_of_off_branchLocus f hf hnonconst δ' hδ' havoid
  exact ⟨PreimageCycle.congr_periodVec hpv.symm c⟩

/-- **Trace identity — member case.** For a closed smooth loop `δ`
in `Y`, the pulled-back period vector `ambientPsi (periodVec δ)` lies
in `truePeriodLattice X`. Case-splits on constancy of `f`:

* If `f` is constant, `ambientPsi f hf = 0` (`ambientPsi_eq_zero_of_const`),
  so the image is `0`, which is in any submodule.
* If `f` is non-constant, extract a preimage cycle witness via
  `exists_preimageCycle_of_nonconstant`, then apply the algebraic trace
  identity `ambientPsi_periodVec_mem_truePeriodLattice_of_preimageCycle`. -/
theorem ambientPsi_periodVec_mem_truePeriodLattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    ambientPsi (gX := genus X) (gY := genus Y) f hf (periodVec δ) ∈
      truePeriodLattice X := by
  by_cases hconst : ∃ y₀ : Y, ∀ x, f x = y₀
  · -- Constant case: ambientPsi = 0.
    rw [ambientPsi_eq_zero_of_const f hf hconst]
    simp
  · -- Non-constant case: extract a preimage cycle and apply the algebraic
    -- reduction.
    obtain ⟨c⟩ := exists_preimageCycle_of_nonconstant f hf hconst δ hδ
    exact ambientPsi_periodVec_mem_truePeriodLattice_of_preimageCycle f hf δ c

/-- `ambientPsi` preserves the period lattice. Reduces to
`ambientPsi_periodVec_mem_truePeriodLattice` on closed-loop generators,
extended to the ℤ-span by `Submodule.span_induction` and `ambientPsi`'s
ℤ-linearity. (Mirrors the structure of `ambientPhi_preserves_truePeriodLattice`.) -/
theorem ambientPsi_preserves_truePeriodLattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (truePeriodLattice Y).toAddSubgroup ≤
      (truePeriodLattice X).toAddSubgroup.comap
        (ambientPsi (gX := genus X) (gY := genus Y) f hf).toAddMonoidHom := by
  show ∀ v ∈ truePeriodLattice Y,
    ambientPsi (gX := genus X) (gY := genus Y) f hf v ∈ truePeriodLattice X
  intro v hv
  refine Submodule.span_induction
    (p := fun v _ => ambientPsi (gX := genus X) (gY := genus Y) f hf v ∈
      truePeriodLattice X) ?_ ?_ ?_ ?_ hv
  · -- Generator case: v = periodVec δ for a closed smooth loop δ in Y.
    rintro _ ⟨δ, hδ, rfl⟩
    exact ambientPsi_periodVec_mem_truePeriodLattice f hf δ hδ
  · -- Zero case.
    simp
  · -- Additive case.
    intro x y _ _ hx hy
    simp only [map_add]
    exact Submodule.add_mem _ hx hy
  · -- ℤ-scalar case.
    intro r x _ hx
    simp only [map_zsmul]
    exact Submodule.smul_mem _ r hx

end Jacobians
