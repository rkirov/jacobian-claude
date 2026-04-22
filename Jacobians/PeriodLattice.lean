import Jacobians.LineIntegral
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Connected.LocPathConnected

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

open scoped Manifold ContDiff Bundle Topology
open Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Arbitrary basepoint in `X` (via `Nonempty`). The period lattice
is independent of basepoint choice, because any two basepoints can
be connected by a path which conjugates closed loops without changing
the integral (modulo the lattice itself). -/
noncomputable def basepoint (X : Type*) [Nonempty X] : X := Classical.arbitrary X

/-! ### Path-connectedness of a compact Riemann surface (classical)

A connected manifold over a locally-path-connected model is itself
path-connected. Specifically: `ChartedSpace ℂ X` inherits
`LocPathConnectedSpace X` from `ℂ` via chart-local homeomorphisms
(`ChartedSpace.locPathConnectedSpace`), and combined with
`ConnectedSpace X` gives `PathConnectedSpace X`
(`pathConnectedSpace_iff_connectedSpace`).

From this we get `Path P Q` for any `P Q : X` — a continuous path
between any two points on a compact connected Riemann surface. -/

/-- `X` is locally path-connected, inherited from `ℂ` via charts. -/
instance instLocPathConnectedSpaceOfChartedSpaceC
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] :
    LocPathConnectedSpace X :=
  ChartedSpace.locPathConnectedSpace ℂ X

/-- `X` is path-connected (connected + locally path-connected). -/
instance instPathConnectedSpaceOfConnectedChartedSpace
    (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X] [ConnectedSpace X] :
    PathConnectedSpace X :=
  pathConnectedSpace_iff_connectedSpace.mpr inferInstance

/-- **Classical fact**: for any two points on a connected compact
Riemann surface, there exists a continuous path between them.

This is just `PathConnectedSpace.somePath`; captured as an explicit
theorem for readability and for consumption by downstream Abel-Jacobi
definitions. Upgrading to a *smooth* path requires additional
content (smooth-approximation theorem — a known Mathlib gap for
general manifolds). -/
noncomputable def continuousPath (P Q : X) : Path P Q :=
  (PathConnectedSpace.somePath P Q)

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

/-- Regularity predicate for a closed loop in `X`: closed endpoints
+ continuity + chart-pullback differentiability + integrability of
each basis-form integrand. Packages what's needed for the
`lineIntegral` machinery (Phase 1 identities, chain rule, basis
expansion) to apply sensibly. -/
structure IsClosedSmoothLoop (γ : ℝ → X) : Prop where
  closed : γ 0 = γ 1
  cont : Continuous γ
  diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
    DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t
  integrable : ∀ i : Fin (genus X), IntervalIntegrable
    (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
      MeasureTheory.volume 0 1

/-- The set of period vectors arising from closed smooth loops (at
any basepoint). Requires `IsClosedSmoothLoop` regularity so that the
Phase 1 line-integral identities + chain rule apply. -/
def closedLoopPeriods (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Set (Fin (genus X) → ℂ) :=
  {v | ∃ (γ : ℝ → X), IsClosedSmoothLoop γ ∧ v = periodVec γ}

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
    (γ₁ γ₂ : ℝ → X) (h0 : γ₁ 0 = γ₂ 0)
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

/-! ### Phase 4 support: change of variables under smooth maps

For `f : X → Y` smooth and `γ : ℝ → X` a path, the period vector of
the image loop `f ∘ γ` in `Y` is the `ambientPhi`-image of the period
vector of `γ` in `X`. This is the formal expression of "image of a
loop has period given by the pullback matrix" — the analytic content
that forces `ambientPhi` to preserve the lattice. -/

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

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
  integrable := sorry

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
  simp only [dif_pos rfl]
  show pullbackForm f hf (periodBasisForm Y j) =
    ambientIso X (((ambientIso X).symm.toLinearMap.comp
      ((pullbackForm f hf).comp (ambientIso Y).toLinearMap) : _ →ₗ[_] _)
        (Pi.basisFun ℂ (Fin (genus Y)) j))
  simp [periodBasisForm, LinearMap.comp_apply]

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

end Jacobians
