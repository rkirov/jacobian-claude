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

/-- **Smooth path between two points** with `periodVec`-integrability.
Contains exactly the data needed to apply `periodVec` / `lineIntegral`
machinery to the path; the endpoint hypotheses ensure the path goes
from `P` to `Q`. -/
structure IsSmoothPath (P Q : X) (γ : ℝ → X) : Prop where
  /-- Path starts at `P`. -/
  start : γ 0 = P
  /-- Path ends at `Q`. -/
  finish : γ 1 = Q
  /-- Continuity of the path. -/
  cont : Continuous γ
  /-- Chart-pullback differentiability at each point of `[0,1]`. -/
  diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
    DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t
  /-- Integrability of each basis-form integrand. -/
  integrable : ∀ i : Fin (genus X), IntervalIntegrable
    (fun t => (periodBasisForm X i).toFun (γ t) (pathSpeed γ t))
      MeasureTheory.volume 0 1

/-- A smooth path from `P` to itself is a closed smooth loop. -/
theorem IsSmoothPath.toClosedSmoothLoop {P : X} {γ : ℝ → X}
    (h : IsSmoothPath P P γ) : IsClosedSmoothLoop γ where
  closed := h.start.trans h.finish.symm
  cont := h.cont
  diff := h.diff
  integrable := h.integrable

/-- **Typeclass axiomatizing smooth-path existence.** For any two points
`P, Q` on a compact connected Riemann surface, a smooth path from `P`
to `Q` exists (satisfying the regularity needed for `periodVec` to be
well-defined).

Classical fact (Forster §§1-2): compact Riemann surfaces are smoothly
path-connected — covered by finitely many charts, each biholomorphic
to an open subset of ℂ, and smooth paths in charts patch via
continuity at chart overlaps. Real instance is bounded construction
(~100-200 lines); axiomatized here as typeclass content. -/
class HasSmoothPaths (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Prop where
  /-- For every pair of points, a smooth path exists between them. -/
  exists_smooth_path : ∀ (P Q : X), ∃ γ : ℝ → X, IsSmoothPath P Q γ

/-- The smooth path between `P` and `Q` (choice via `Classical.choose`
of `HasSmoothPaths.exists_smooth_path`). -/
noncomputable def smoothPath [HasSmoothPaths X] (P Q : X) : ℝ → X :=
  Classical.choose (HasSmoothPaths.exists_smooth_path (X := X) P Q)

/-- The chosen smooth path satisfies `IsSmoothPath`. -/
theorem isSmoothPath_smoothPath [HasSmoothPaths X] (P Q : X) :
    IsSmoothPath P Q (smoothPath P Q) :=
  Classical.choose_spec (HasSmoothPaths.exists_smooth_path (X := X) P Q)

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

/-- The `periodVec` of the smooth path from `P` to `P` is in the
period lattice (it's a closed smooth loop). -/
theorem periodVec_smoothPath_self_mem_lattice [HasSmoothPaths X] (P : X) :
    periodVec (smoothPath P P) ∈ truePeriodLattice X :=
  periodVec_mem_truePeriodLattice_of_closed _
    (isSmoothPath_smoothPath P P).toClosedSmoothLoop

/-- **Basepoint change for `smoothPath` modulo the period lattice**
(classical, Forster §21). The path from `P₀` to `A` differs from
the concatenation `P₀ → P → A` by a closed smooth loop, whose
`periodVec` is in the lattice. Quotienting gives the identity.

Content: needs `mk_periodVec_eq_of_endpoints` + `periodVec_concat`
with the hypothesis bundle for smoothness+integrability of the
concat `sp(P₀, P) ⊕ sp(P, A)` and the closed-loop construction.
Left as a focused classical sorry — the core path-algebra content
is a ~50-line proof once the concat smoothness machinery is
established. -/
theorem smoothPath_basepoint_change [HasSmoothPaths X] (P P₀ A : X) :
    (QuotientAddGroup.mk (periodVec (smoothPath P₀ A)) :
      (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
    QuotientAddGroup.mk (periodVec (smoothPath P A)) +
    QuotientAddGroup.mk (periodVec (smoothPath P₀ P)) := sorry

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
lattice (Forster §10.11). Real infrastructure required:
`pushforwardForm` + branched-cover lift existence + trace adjunction
(~200–500 lines not yet in place). -/

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

/-- **Critical set of a holomorphic map** between complex 1-manifolds:
points where `mfderiv` vanishes. Classically the ramification locus. -/
def criticalSet (f : X → Y) : Set X :=
  {x | mfderiv 𝓘(ℂ) 𝓘(ℂ) f x = 0}

/-- **Branch locus**: the image of the critical set. -/
def branchLocus (f : X → Y) : Set Y :=
  f '' criticalSet f

/-- **Critical set is closed.** At each point `x₀`, near `x₀` the
map `x ↦ fderiv ℂ (local rep) (chart x)` is continuous (analytic
in chart coords; chart continuous), so the zero set is closed. The
argument needs care because the chart source varies with `x`; we
use a fixed chart at `x₀` on an open neighborhood. -/
theorem isClosed_criticalSet (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    IsClosed (criticalSet f) := by
  -- Strategy: criticalSet f = {x | mfderiv f x 1 = 0} ∈ X (scalar form).
  -- mfderiv f x 1 as a function X → ℂ is continuous; zero is closed; preimage closed.
  have hset : criticalSet f = (fun x => mfderiv 𝓘(ℂ) 𝓘(ℂ) f x (1 : ℂ)) ⁻¹' {0} := by
    ext x
    simp only [criticalSet, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro h; rw [h]; rfl
    · intro h
      -- TangentSpace 𝓘(ℂ, ℂ) x = ℂ, so mfderiv is a CLM ℂ →L[ℂ] ℂ, determined by value at 1.
      exact ContinuousLinearMap.ext_ring h
  rw [hset]
  -- Show the complement is open; then the preimage of {0} is closed.
  rw [← isOpen_compl_iff]
  rw [show ((fun x => mfderiv 𝓘(ℂ) 𝓘(ℂ) f x (1 : ℂ)) ⁻¹' ({0} : Set ℂ))ᶜ =
      {x | mfderiv 𝓘(ℂ) 𝓘(ℂ) f x ≠ 0} from ?_]
  · -- Key: criticalSet complement = {x | mfderiv f x ≠ 0}. Use ContMDiffAt of
    -- the inCoordinates form of mfderiv to get local openness.
    rw [isOpen_iff_mem_nhds]
    intro x₀ hx₀  -- hx₀ : mfderiv f x₀ ≠ 0
    -- ContMDiffAt of the coordinate form.
    have hmf : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
        (fun x => ContinuousLinearMap.inCoordinates ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := X)) ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := Y))
          x₀ x (f x₀) (f x) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) x₀ :=
      (hf x₀).mfderiv_const (le_refl _)
    -- ContMDiffAt → ContinuousAt.
    have hcont : ContinuousAt (fun x => ContinuousLinearMap.inCoordinates ℂ
        (TangentSpace 𝓘(ℂ, ℂ) (M := X)) ℂ
        (TangentSpace 𝓘(ℂ, ℂ) (M := Y))
        x₀ x (f x₀) (f x) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) x₀ :=
      hmf.continuousAt
    -- Key observation: mfderiv f x₀ ≠ 0 implies inCoordinates(mfderiv f x₀) ≠ 0,
    -- because inCoordinates is conjugation by bijective trivializations.
    -- Rather than proving the full iff, use the contrapositive inline:
    -- if inCoordinates(mfderiv f x) = 0, then mfderiv f x = 0 (bijection).
    have hbase_X : (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet ∈ 𝓝 x₀ :=
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ℂ _ x₀)
    have hbase_Y : f ⁻¹' (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) (f x₀)).baseSet ∈ 𝓝 x₀ :=
      hf.continuous.continuousAt.preimage_mem_nhds
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) (f x₀)).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt ℂ _ (f x₀)))
    -- At x₀, inCoordinates ≠ 0 (mfderiv ≠ 0 + trivialization bijection).
    -- Key tactic: conjugate out the trivialization factors.
    have hinCoord_ne_x₀ : ContinuousLinearMap.inCoordinates ℂ
        (TangentSpace 𝓘(ℂ, ℂ) (M := X)) ℂ
        (TangentSpace 𝓘(ℂ, ℂ) (M := Y))
        x₀ x₀ (f x₀) (f x₀) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x₀) ≠ 0 := by
      intro h
      apply hx₀
      -- `h` is a CLM equation; evaluate at `continuousLinearMapAt 1` and use
      -- `symmL_continuousLinearMapAt = id`.
      have hmem_X : x₀ ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet :=
        mem_baseSet_trivializationAt ℂ _ x₀
      have hmem_Y : f x₀ ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) (f x₀)).baseSet :=
        mem_baseSet_trivializationAt ℂ _ (f x₀)
      apply ContinuousLinearMap.ext
      intro v
      show (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x₀) v = 0
      -- Apply h at `continuousLinearMapAt (triv X) x₀ v : ℂ`.
      have happ := congr_arg
        (fun L : ℂ →L[ℂ] ℂ =>
          L ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).continuousLinearMapAt ℂ x₀ v))
        h
      simp only [ContinuousLinearMap.zero_apply] at happ
      simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply] at happ
      rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hmem_X] at happ
      -- happ : continuousLinearMapAt (triv Y) (f x₀) (mfderiv f x₀ v) = 0
      -- Apply symmL to both sides to cancel the continuousLinearMapAt.
      have := congr_arg
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) (f x₀)).symmL ℂ (f x₀)) happ
      rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hmem_Y] at this
      -- `this : (mfderiv f x₀) v = (triv Y).symm (f x₀) 0`
      -- Need: (triv Y).symm (f x₀) 0 = 0, which holds because
      -- symmL is a CLM (hence map_zero) and coincides with symm on baseSet.
      have hzero : ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) (f x₀)).symmL ℂ (f x₀)) 0
          = (0 : TangentSpace 𝓘(ℂ, ℂ) (M := Y) (f x₀)) :=
        ContinuousLinearMap.map_zero _
      -- Convert via the (symmL vs symm) coincidence lemma.
      calc (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x₀) v
          = _ := this
        _ = ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) (f x₀)).symmL ℂ (f x₀)) 0 := by
              simp [Bundle.Trivialization.symmL]
        _ = 0 := hzero
    -- By continuity, inCoordinates ≠ 0 in a nbhd.
    have hnbhd : (fun x => ContinuousLinearMap.inCoordinates ℂ
        (TangentSpace 𝓘(ℂ, ℂ) (M := X)) ℂ
        (TangentSpace 𝓘(ℂ, ℂ) (M := Y))
        x₀ x (f x₀) (f x) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x)) ⁻¹' {0}ᶜ ∈ 𝓝 x₀ :=
      hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hinCoord_ne_x₀)
    -- Pull back: inCoordinates ≠ 0 → mfderiv ≠ 0 (composition with 0 = 0).
    filter_upwards [hnbhd] with x hx hmf_zero
    apply hx
    simp [ContinuousLinearMap.inCoordinates, hmf_zero,
      ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp]
  · -- Set equality: complement of "mfderiv f x 1 = 0" = "mfderiv f x ≠ 0".
    ext x
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
    constructor
    · intro h hmf_zero
      apply h
      rw [hmf_zero]; rfl
    · intro h hval_zero
      apply h
      exact ContinuousLinearMap.ext_ring hval_zero

/-- **Critical set of a non-constant map is not everything.** If
`criticalSet f = Set.univ` (i.e., `mfderiv f = 0` everywhere), then
`f` is locally constant; since `X` is connected, `f` is globally
constant. -/
theorem criticalSet_ne_univ_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (_hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    criticalSet f ≠ Set.univ := by
  -- Contrapositive: criticalSet = univ ⇒ mfderiv f ≡ 0 ⇒ f locally constant ⇒
  -- (X connected) ⇒ f constant.
  intro h_univ
  apply _hnonconst
  -- mfderiv f x = 0 for all x.
  have hmfderiv_zero : ∀ x, mfderiv 𝓘(ℂ) 𝓘(ℂ) f x = 0 := fun x => by
    have : x ∈ criticalSet f := h_univ.symm ▸ Set.mem_univ x
    exact this
  -- Compose with chart of Y to get ℂ-valued MDifferentiable function locally,
  -- which by MVT in charts is locally constant; hence f is locally constant.
  -- Use `IsLocallyConstant.exists_eq_const` on preconnected X.
  have hlc : IsLocallyConstant f := by
    intro y
    -- Show f ⁻¹' {y} is open.
    rw [isOpen_iff_mem_nhds]
    intro x₀ hx₀
    -- Find nbhd of x₀ where f ≡ f x₀. We'll use a small ball in chart target.
    -- In chart at x₀, with chart at f x₀, f corresponds to a holomorphic f_loc : ℂ → ℂ
    -- with fderiv ℂ f_loc = 0, hence constant on a ball.
    -- ~30 lines of chart-ball MVT plumbing — left as deeper sub-sorry.
    sorry
  -- Connected (hence preconnected) + Nonempty → constant.
  exact hlc.exists_eq_const.imp fun y₀ heq x => (congr_fun heq x)

/-- **Critical set is finite.** In local charts, `mfderiv f` becomes
a nonvanishing analytic function near any non-critical point, so
critical points are isolated zeros of an analytic function. On
compact `X`, the discrete set of zeros is finite. -/
theorem finite_criticalSet_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (_hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    (criticalSet f).Finite := sorry

/-- **Branch locus is finite.** Image of a finite set is finite. -/
theorem finite_branchLocus_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    (branchLocus f).Finite :=
  (finite_criticalSet_of_nonconstant f hf hnonconst).image f

/-- **Existence of preimage cycle for non-constant maps** — the main
content sorry. Classically (Forster §10.11): pick `δ` or homotope it
to avoid the finite `branchLocus`; locally lift via the unbranched
cover on `Y ∖ branchLocus`; patch the lifts globally via the
covering structure. Requires real branched-cover infrastructure; the
intermediate pieces above reduce the problem to covering-space path
lifting on a compact 1-manifold minus a finite set. -/
theorem exists_preimageCycle_of_nonconstant
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (_hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (_hδ : IsClosedSmoothLoop δ) :
    Nonempty (PreimageCycle f hf δ) := sorry

/-- **Trace identity — member case.** For a closed smooth loop `δ`
in `Y`, the pulled-back period vector `ambientPsi (periodVec δ)` lies
in `truePeriodLattice X`.

Case-split: constant case proven via `ambientPsi_eq_zero_of_const`;
non-constant case reduced to `exists_preimageCycle_of_nonconstant`
(classical branched-cover content) + the algebraic lemma
`ambientPsi_periodVec_mem_truePeriodLattice_of_preimageCycle`. -/
theorem ambientPsi_periodVec_mem_truePeriodLattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    ambientPsi (gX := genus X) (gY := genus Y) f hf (periodVec δ) ∈
      truePeriodLattice X := by
  by_cases hconst : ∃ y₀ : Y, ∀ x, f x = y₀
  · -- Constant case: ambientPsi = 0, image is 0 ∈ lattice.
    rw [ambientPsi_eq_zero_of_const f hf hconst]
    simp
  · -- Non-constant case: extract preimage cycle, reduce algebraically.
    obtain ⟨c⟩ := exists_preimageCycle_of_nonconstant f hf hconst δ hδ
    exact ambientPsi_periodVec_mem_truePeriodLattice_of_preimageCycle f hf δ c

/-- `ambientPsi` preserves the period lattice. Reduces to the member
case (`ambientPsi_periodVec_mem_truePeriodLattice`) via span induction;
zero/add/smul cases are immediate ℤ-linearity. -/
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
  · -- member case: δ ∈ closedLoopPeriods Y. Delegated to content sorry.
    rintro _ ⟨δ, hδ, rfl⟩
    exact ambientPsi_periodVec_mem_truePeriodLattice f hf δ hδ
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
