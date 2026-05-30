/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.TraceForm
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The Jacobian pullback in ambient coordinates, driven by the geometric trace

This file sits **downstream of the genuine geometric trace** `traceForm`
(`Jacobians/TraceForm.lean`) and turns it into the data the Jacobian `pullback`
consumes:

* `ambientTrace` — `traceFormTotal` read in the `ambientIso` basis coordinates
  (matrix `T`, direction `gX → gY`);
* `ambientPullbackJac` — the transpose `Tᵀ` (direction `gY → gX`), the genuine
  Jacobian pullback in ambient coordinates. By the projection formula it realises
  `periodVec δ ↦ periodVec(preimage cycle)`.

It also hosts the **§3 lift chain** (relocated here from `PeriodLattice.lean`,
whose covering / fibre-finiteness infrastructure is still imported through
`TraceForm`): the `PreimageCycle` structure whose `pullback_eq` field references
`ambientPullbackJac`, and the lemmas that conclude `ambientPullbackJac` preserves
the period lattice.

## Architecture note

Previously `ambientPullbackJac` was driven by an **opaque stub**
`pushforwardForm := if const then 0 else sorry` in `HolomorphicForms.lean`. That
stub is gone: the single source of truth is now the geometric trace `traceForm`,
and `traceFormTotal` is only its constant-map bookkeeping wrapper (`0` on constant
maps). So the Jacobian pullback is now genuinely the transpose of the geometric
trace of forms.

## References

Forster §§4, 10 (the trace / branched cover); Griffiths–Harris Ch. 2 §2.7
(the trace map for forms, and `f₊ ∘ f* = deg • id`).
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology
open Filter Set

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-! ## Trace-coordinates layer

`ambientTrace` is the geometric trace `traceFormTotal` expressed in the chosen
basis coordinates (via `ambientIso`); `ambientPullbackJac` is its matrix transpose.
The construction is the exact dual of `ambientPsi`/`ambientPhi` for `pullbackForm`
(see `HolomorphicForms.lean`), but built from the genuine trace rather than the old
opaque stub. -/

/-- Coordinate form of the trace `f₊`, parallel to `ambientPsi` for `pullbackForm`:
`ambientTrace = (ambientIso Y)⁻¹ ∘ traceFormTotal f hf ∘ (ambientIso X)` (matrix
`T`, direction `gX → gY`; zero on the unused off-genus branch). Built from the
genuine geometric trace `traceFormTotal` (which is `traceForm` off the constant
locus and `0` on constant maps). -/
noncomputable def ambientTrace {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin gX → ℂ) →L[ℂ] (Fin gY → ℂ) := by
  classical
  by_cases hX : gX = genus X
  · by_cases hY : gY = genus Y
    · subst hX; subst hY
      refine LinearMap.toContinuousLinearMap
        ((ambientIso Y).symm.toLinearMap.comp
          ((traceFormTotal f hf).comp (ambientIso X).toLinearMap))
    · exact 0
  · exact 0

/-- The genuine Jacobian **pullback** in ambient coordinates: `Tᵀ`, the transpose
of `ambientTrace` (via the standard Pi basis). Direction `gY → gX`. By the
projection formula this realises `periodVec δ ↦ periodVec(preimage cycle)`; it
replaces the misformalized `ambientPsi`-as-pullback. As with `ambientPhi`, the
transpose makes contravariant `ambientPullbackJac_comp` automatic from covariant
`ambientTrace_comp`. -/
noncomputable def ambientPullbackJac {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin gY → ℂ) →L[ℂ] (Fin gX → ℂ) :=
  LinearMap.toContinuousLinearMap
    (LinearMap.toMatrix (Pi.basisFun ℂ (Fin gX)) (Pi.basisFun ℂ (Fin gY))
        (ambientTrace f hf).toLinearMap).transpose.mulVecLin

/-- `ambientTrace id = id`. Proven via `traceFormTotal_id`. -/
theorem ambientTrace_id (x : Fin (genus X) → ℂ) :
    ambientTrace (X := X) (Y := X) (gX := genus X) (gY := genus X) id contMDiff_id x = x := by
  unfold ambientTrace
  set_option linter.unusedSimpArgs false in
  simp only [dif_pos rfl]
  show (((ambientIso X).symm.toLinearMap.comp
      ((traceFormTotal (id : X → X) contMDiff_id).comp (ambientIso X).toLinearMap)) : _ →ₗ[_] _) x = x
  rw [show (traceFormTotal (id : X → X) contMDiff_id) = LinearMap.id from traceFormTotal_id]
  simp

/-- Covariant composition: `ambientTrace (g ∘ f) = ambientTrace g ∘ ambientTrace f`.
Proven via `traceFormTotal_comp`. -/
theorem ambientTrace_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f))
    (x : Fin (genus X) → ℂ) :
    ambientTrace (gX := genus X) (gY := genus Z) (g ∘ f) hgf x =
      ambientTrace (gX := genus Y) (gY := genus Z) g hg
        (ambientTrace (gX := genus X) (gY := genus Y) f hf x) := by
  unfold ambientTrace
  set_option linter.unusedSimpArgs false in
  simp only [dif_pos rfl]
  show (((ambientIso Z).symm.toLinearMap.comp
      ((traceFormTotal (g ∘ f) hgf).comp (ambientIso X).toLinearMap))) x = _
  rw [traceFormTotal_comp f hf g hg hgf]
  simp [LinearMap.comp_apply]

/-- `ambientPullbackJac id = id` — transpose of the identity matrix is the
identity, via `ambientTrace_id`. -/
theorem ambientPullbackJac_id (y : Fin (genus X) → ℂ) :
    ambientPullbackJac (X := X) (Y := X) (gX := genus X) (gY := genus X) id contMDiff_id y = y := by
  have htr : ambientTrace (X := X) (Y := X) (gX := genus X) (gY := genus X) id contMDiff_id
      = ContinuousLinearMap.id ℂ (Fin (genus X) → ℂ) :=
    ContinuousLinearMap.ext (fun x => ambientTrace_id x)
  unfold ambientPullbackJac
  rw [show (ambientTrace (X := X) (Y := X) (gX := genus X) (gY := genus X) id contMDiff_id).toLinearMap
      = LinearMap.id (R := ℂ) (M := Fin (genus X) → ℂ) from by rw [htr]; rfl]
  simp [Matrix.transpose_one, Matrix.mulVecLin_one]

/-- Contravariant composition: `ambientPullbackJac (g ∘ f) = ambientPullbackJac f ∘ ambientPullbackJac g`.
Follows from covariant `ambientTrace_comp` via matrix transpose reversing order. -/
theorem ambientPullbackJac_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f))
    (z : Fin (genus Z) → ℂ) :
    ambientPullbackJac (gX := genus X) (gY := genus Z) (g ∘ f) hgf z =
      ambientPullbackJac (gX := genus X) (gY := genus Y) f hf
        (ambientPullbackJac (gX := genus Y) (gY := genus Z) g hg z) := by
  have htr : ambientTrace (gX := genus X) (gY := genus Z) (g ∘ f) hgf =
      (ambientTrace (gX := genus Y) (gY := genus Z) g hg).comp
        (ambientTrace (gX := genus X) (gY := genus Y) f hf) :=
    ContinuousLinearMap.ext (fun x => ambientTrace_comp f hf g hg hgf x)
  unfold ambientPullbackJac
  rw [show (ambientTrace (gX := genus X) (gY := genus Z) (g ∘ f) hgf).toLinearMap =
      (ambientTrace (gX := genus Y) (gY := genus Z) g hg).toLinearMap ∘ₗ
      (ambientTrace (gX := genus X) (gY := genus Y) f hf).toLinearMap from by rw [htr]; rfl]
  rw [LinearMap.toMatrix_comp (Pi.basisFun ℂ (Fin (genus X))) (Pi.basisFun ℂ (Fin (genus Y)))
    (Pi.basisFun ℂ (Fin (genus Z)))]
  rw [Matrix.transpose_mul, Matrix.mulVecLin_mul]
  rfl

/-- **ambientTrace of a constant map is zero**, from `traceFormTotal_eq_zero_of_const`
(mirrors `ambientPsi_eq_zero_of_const`). -/
theorem ambientTrace_eq_zero_of_const (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hconst : ∃ y₀ : Y, ∀ x, f x = y₀) :
    ambientTrace (gX := genus X) (gY := genus Y) f hf = 0 := by
  unfold ambientTrace
  simp only [dite_true]
  rw [traceFormTotal_eq_zero_of_const f hf hconst]
  ext v i
  simp

/-- **ambientPullbackJac of a constant map is zero** (`Tᵀ = 0` when `T = 0`).
The constant-case input to `ambientPullbackJac_preserves_truePeriodLattice`. -/
theorem ambientPullbackJac_eq_zero_of_const (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hconst : ∃ y₀ : Y, ∀ x, f x = y₀) :
    ambientPullbackJac (gX := genus X) (gY := genus Y) f hf = 0 := by
  unfold ambientPullbackJac
  rw [show (ambientTrace (gX := genus X) (gY := genus Y) f hf).toLinearMap
      = (0 : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ)) from by
    rw [ambientTrace_eq_zero_of_const f hf hconst]; rfl]
  ext v i
  simp

/-- **Algebraic bridge (projection formula, period level).** The `i`-th component of
the genuine Jacobian pullback `ambientPullbackJac f hf (periodVec δ)` is the line
integral of the trace of the `i`-th basis form along `δ`:
`(Tᵀ · periodVec δ)ᵢ = ∫_δ traceFormTotal f hf (ωᵢ^X)`.

Pure linear algebra + linearity of `lineIntegral`, dual to `periodVec_pushforward`
(`PeriodLattice.lean`). With `w := (ambientIso Y).symm (traceFormTotal f hf ωᵢ^X)`:
the matrix entry `Tᵀ i j = (ambientTrace f hf eᵢ^X) j = w j` (`ambientTrace` is the
`ambientIso`-conjugate of `traceFormTotal`), so the LHS is `∑ⱼ wⱼ (periodVec δ)ⱼ`;
and `traceFormTotal f hf ωᵢ^X = ambientIso Y w = ∑ⱼ wⱼ • ωⱼ^Y`, so the RHS line
integral is `∑ⱼ wⱼ ∫_δ ωⱼ^Y = ∑ⱼ wⱼ (periodVec δ)ⱼ` by linearity. The integrability
hypothesis is the per-basis-form regularity of a closed smooth loop. -/
theorem ambientPullbackJac_periodVec_apply_eq_lineIntegral_traceFormTotal
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (δ : ℝ → Y) (i : Fin (genus X))
    (hint_Y : ∀ j : Fin (genus Y), IntervalIntegrable
      (fun t => (periodBasisForm Y j).toFun (δ t) (pathSpeed δ t)) MeasureTheory.volume 0 1) :
    ambientPullbackJac (gX := genus X) (gY := genus Y) f hf (periodVec δ) i =
      lineIntegral (traceFormTotal f hf (periodBasisForm X i)) δ := by
  classical
  set w := (ambientIso Y).symm (traceFormTotal f hf (periodBasisForm X i)) with hw_def
  -- The matrix-transpose action `(Tᵀ · periodVec δ)ᵢ = ∑ⱼ wⱼ (periodVec δ)ⱼ`.
  have hLHS : ambientPullbackJac (gX := genus X) (gY := genus Y) f hf (periodVec δ) i
      = ∑ j, w j * (periodVec δ) j := by
    show (Matrix.transpose (LinearMap.toMatrix (Pi.basisFun ℂ (Fin (genus X)))
        (Pi.basisFun ℂ (Fin (genus Y))) (ambientTrace f hf).toLinearMap)).mulVecLin
        (periodVec δ) i = ∑ j, w j * (periodVec δ) j
    rw [Matrix.mulVecLin_apply]
    show ∑ j, (Matrix.transpose (LinearMap.toMatrix _ _ _)) i j * (periodVec δ) j
        = ∑ j, w j * (periodVec δ) j
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    show (LinearMap.toMatrix (Pi.basisFun ℂ (Fin (genus X)))
      (Pi.basisFun ℂ (Fin (genus Y))) (ambientTrace f hf).toLinearMap) j i = w j
    rw [LinearMap.toMatrix_apply]
    show ((Pi.basisFun ℂ (Fin (genus Y))).repr
      (ambientTrace f hf (Pi.basisFun ℂ (Fin (genus X)) i))) j = w j
    rw [Pi.basisFun_repr]
    -- `ambientTrace f hf eᵢ^X = w` (ambientIso-conjugate of traceFormTotal).
    have hat : ambientTrace (gX := genus X) (gY := genus Y) f hf
        (Pi.basisFun ℂ (Fin (genus X)) i) = w := by
      rw [hw_def]
      unfold ambientTrace
      set_option linter.unusedSimpArgs false in simp only [dif_pos rfl]
      rfl
    rw [hat]
  -- The line integral of the trace form `= ∑ⱼ wⱼ (periodVec δ)ⱼ`.
  have hRHS : lineIntegral (traceFormTotal f hf (periodBasisForm X i)) δ
      = ∑ j, w j * (periodVec δ) j := by
    have h_iso : traceFormTotal f hf (periodBasisForm X i) = ambientIso Y w := by
      rw [hw_def]; exact ((ambientIso Y).apply_symm_apply _).symm
    rw [h_iso]
    have h_iso_sum : ambientIso Y w = ∑ j, w j • periodBasisForm Y j := by
      have h_w_decomp : w = ∑ j, w j • Pi.basisFun ℂ (Fin (genus Y)) j := by
        have := pi_eq_sum_univ' w
        convert this using 2
        simp [Pi.basisFun_apply]
      conv_lhs => rw [h_w_decomp, map_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [map_smul]; rfl
    rw [h_iso_sum]
    -- `lineIntegral (∑ⱼ wⱼ • ωⱼ^Y) δ = ∑ⱼ wⱼ ∫_δ ωⱼ^Y = ∑ⱼ wⱼ (periodVec δ)ⱼ`.
    have h_sum_lineIntegral : lineIntegral (∑ j, w j • periodBasisForm Y j) δ =
        ∑ j, w j * lineIntegral (periodBasisForm Y j) δ := by
      unfold lineIntegral
      have h_pw : ∀ t : ℝ,
          (∑ j, w j • periodBasisForm Y j).toFun (δ t) (pathSpeed δ t) =
            ∑ j, w j * (periodBasisForm Y j).toFun (δ t) (pathSpeed δ t) := by
        intro t
        induction (Finset.univ : Finset (Fin (genus Y))) using Finset.induction_on with
        | empty =>
          rw [Finset.sum_empty, Finset.sum_empty]
          show (0 : HolomorphicOneForms Y).toFun (δ t) (pathSpeed δ t) = 0
          rfl
        | @insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha]
          show ((w a • periodBasisForm Y a) + ∑ j ∈ s, w j • periodBasisForm Y j).toFun (δ t)
              (pathSpeed δ t) = _
          rw [show ((w a • periodBasisForm Y a) + ∑ j ∈ s, w j • periodBasisForm Y j).toFun (δ t) =
              (w a • periodBasisForm Y a).toFun (δ t) +
                (∑ j ∈ s, w j • periodBasisForm Y j).toFun (δ t) from rfl,
            ContinuousLinearMap.add_apply, ih]
          rfl
      simp_rw [h_pw]
      rw [intervalIntegral.integral_finset_sum (s := Finset.univ)
        (f := fun j t => w j * (periodBasisForm Y j).toFun (δ t) (pathSpeed δ t))
        (fun j _ => (hint_Y j).const_mul (w j))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact intervalIntegral.integral_const_mul _ _
    rw [h_sum_lineIntegral]
    rfl
  rw [hLHS, hRHS]

/-! ## §3 The preimage cycle and lattice preservation

Relocated here from `PeriodLattice.lean` (whose covering / fibre-finiteness
infrastructure is still imported via `TraceForm`): these are the parts of the §3
lift chain that reference the **genuine** `ambientPullbackJac` defined above. The
`PreimageCycle.pullback_eq` field is the projection-formula identity
`Tᵀ·periodVec δ = ∑ coeffs·periodVec loopsᵢ`. -/

/-- A **preimage cycle** witnessing the trace identity: a finite
ℤ-combination of closed smooth loops in `X` whose period-vector sum
realizes the genuine Jacobian pullback `ambientPullbackJac f hf (periodVec δ)`.

Classically: for non-constant holomorphic `f : X → Y` between compact
Riemann surfaces, `f` is a branched cover of some degree `d ≥ 1`,
and the set-theoretic preimage `f⁻¹(δ)` of a loop `δ` (avoiding
branch points) is `d` disjoint closed loops in `X` whose signed sum
realizes `Tᵀ (periodVec δ)` (Forster §10.11).

Defining `PreimageCycle` as a bundle of (loops + coefficients +
pullback/pushforward equations) lets us isolate the classical content: the theorem
`ambientPullbackJac_periodVec_mem_truePeriodLattice_of_preimageCycle` is
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
  /-- Sheet count of the cover (classically `= deg f`). -/
  sheets : ℕ
  /-- **Pullback identity** (projection formula): the genuine Jacobian pullback
  `ambientPullbackJac` (= `Tᵀ`) on `periodVec δ` equals the ℤ-combination of the
  lifts' period vectors `periodVec(Γ) = Tᵀ·periodVec δ`. -/
  pullback_eq : ambientPullbackJac (gX := genus X) (gY := genus Y) f hf (periodVec δ) =
    ∑ i, coeffs i • periodVec (loops i)
  /-- **Pushforward identity** (`f∘Γ = sheets·δ` on periods): the lifts project to
  `δ` with multiplicities summing to `sheets`. Feeds the S8 connection keystone. -/
  pushforward_eq : ∑ i, coeffs i • periodVec (f ∘ loops i) =
    (sheets : ℤ) • periodVec δ

/-- **Pullback identity — algebraic reduction.** Given a `PreimageCycle`
witness for `(f, δ)`, the pulled-back period vector
`ambientPullbackJac (periodVec δ)` lies in `truePeriodLattice X`: each
`periodVec` of a closed smooth loop is in the lattice, and the
lattice is closed under ℤ-linear combinations. -/
theorem ambientPullbackJac_periodVec_mem_truePeriodLattice_of_preimageCycle
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (δ : ℝ → Y) (c : PreimageCycle f hf δ) :
    ambientPullbackJac (gX := genus X) (gY := genus Y) f hf (periodVec δ) ∈
      truePeriodLattice X := by
  rw [c.pullback_eq]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ (c.coeffs i)
      (periodVec_mem_truePeriodLattice_of_closed _ (c.loops_smooth i))

/-- **[open]** A closed smooth loop in `Y` can be homotoped off the finite
branch locus without changing its period vector. Genericity: `branchLocus f`
is finite (`finite_branchLocus_of_nonconstant`), hence has real codimension 2
in the surface `Y`, so a generic loop avoids it; homotopy invariance of
`periodVec` preserves the period. -/
theorem exists_loop_off_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    ∃ δ', IsClosedSmoothLoop δ' ∧ periodVec δ' = periodVec δ ∧
      (∀ t : ℝ, δ' t ∉ branchLocus f) :=
  sorry

/-- **Continuous path-lift off the branch locus.** A path `δ` in `Y` that avoids the
branch locus lifts, through the proven covering
`(univ \ branchLocus f).restrictPreimage f`, to a continuous path `Γ` in `X` with
`f (Γ t) = δ t` on `[0,1]` and prescribed start `Γ 0 = e` (any fibre point over
`δ 0`). The lift is Mathlib's `IsCoveringMap.liftPath`, repackaged from the unit
interval to `ℝ → X` via `Set.projIcc`. Foundation for the smooth-loop assembly
(§3 sub-piece A).

The lift is `Set.projIcc`-clamped, so it is **constant outside `[0,1]`** (`= e` on
`(-∞,0]`, `= Γ 1` on `[1,∞)`); these two facts are exposed in the conclusion — they
give the two-sided endpoint control the seam-flattening construction needs. -/
theorem exists_continuous_lift_off_branchLocus
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ_cont : Continuous δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f)
    {e : X} (he : f e = δ 0) :
    ∃ Γ : ℝ → X, Continuous Γ ∧ (∀ t ∈ Set.Icc (0:ℝ) 1, f (Γ t) = δ t) ∧ Γ 0 = e ∧
      (∀ t : ℝ, t ≤ 0 → Γ t = e) ∧ (∀ t : ℝ, 1 ≤ t → Γ t = Γ 1) := by
  classical
  have cov : IsCoveringMap ((Set.univ \ branchLocus f).restrictPreimage f) :=
    isCoveringMap_restrictPreimage_compl_branchLocus f hf hnonconst
  -- `δ` lands in `s := univ \ branchLocus f` everywhere (it avoids the branch locus).
  have hδs : ∀ t : ℝ, δ t ∈ Set.univ \ branchLocus f := fun t => ⟨Set.mem_univ _, havoid t⟩
  -- Corestrict `δ` to the unit interval, as a continuous map into the subtype.
  let δ' : C(unitInterval, ↥(Set.univ \ branchLocus f)) :=
    ⟨fun t => ⟨δ t, hδs t⟩, (hδ_cont.comp continuous_subtype_val).subtype_mk _⟩
  -- The start point, lifted into the fibre subtype.
  have hes : e ∈ f ⁻¹' (Set.univ \ branchLocus f) := by
    show f e ∈ Set.univ \ branchLocus f; rw [he]; exact hδs 0
  let e' : ↥(f ⁻¹' (Set.univ \ branchLocus f)) := ⟨e, hes⟩
  have hγ0 : δ' 0 = (Set.univ \ branchLocus f).restrictPreimage f e' := by
    apply Subtype.ext
    show δ ((0 : unitInterval) : ℝ) = f e
    rw [Set.Icc.coe_zero, he]
  have hlifts := IsCoveringMap.liftPath_lifts cov δ' e' hγ0
  have hzero := IsCoveringMap.liftPath_zero cov δ' e' hγ0
  refine ⟨fun t => ((IsCoveringMap.liftPath cov δ' e' hγ0)
      (Set.projIcc 0 1 zero_le_one t) : X), ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.comp
      ((map_continuous (IsCoveringMap.liftPath cov δ' e' hγ0)).comp continuous_projIcc)
  · intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hδ'c : ∀ x : unitInterval, (↑(δ' x) : Y) = δ ↑x := fun _ => rfl
    have h := congrArg Subtype.val (congr_fun hlifts (Set.projIcc 0 1 zero_le_one t))
    simpa [Function.comp_apply, Set.restrictPreimage_coe, hδ'c, Set.coe_projIcc,
      min_eq_right ht1, max_eq_right ht0] using h
  · have h0 : Set.projIcc (0:ℝ) 1 zero_le_one 0 = 0 := by
      apply Subtype.ext; simp
    show ((IsCoveringMap.liftPath cov δ' e' hγ0)
      (Set.projIcc 0 1 zero_le_one 0) : X) = e
    rw [h0, hzero]
  · -- Clamp on `(-∞, 0]`: `projIcc` sends `t ≤ 0` to the left endpoint `0`, so `Γ t = e`.
    intro t ht
    show ((IsCoveringMap.liftPath cov δ' e' hγ0)
      (Set.projIcc 0 1 zero_le_one t) : X) = e
    have h0' : Set.projIcc (0:ℝ) 1 zero_le_one t = 0 := by
      rw [Set.projIcc_of_le_left _ ht]; rfl
    rw [h0', hzero]
  · -- Clamp on `[1, ∞)`: `projIcc` sends `1 ≤ t` to the right endpoint `1`, as it does `1`.
    intro t ht
    show ((IsCoveringMap.liftPath cov δ' e' hγ0)
        (Set.projIcc 0 1 zero_le_one t) : X) =
      ((IsCoveringMap.liftPath cov δ' e' hγ0)
        (Set.projIcc 0 1 zero_le_one 1) : X)
    have h1 : Set.projIcc (0:ℝ) 1 zero_le_one t = Set.projIcc (0:ℝ) 1 zero_le_one 1 := by
      rw [Set.projIcc_of_right_le _ ht, Set.projIcc_of_right_le _ le_rfl]
    rw [h1]

/-! ### Seam-flattening reparametrization (§3 step C)

A path-lift produced by `exists_continuous_lift_off_branchLocus` is `Set.projIcc`-
clamped (constant outside `[0,1]`), so it is *not* differentiable at the endpoints
`0,1`, and `differentiableAt_chart_lift_of_notMem_criticalSet` (B) only delivers
differentiability on the open `(0,1)`. To concatenate lifts into closed loops we
need lifts that are genuine smooth paths with *zero endpoint velocity*. The fix is
to reparametrize the base loop by `flatEndReparam`, which is **constant near each
endpoint** (a genuine plateau, not merely zero-derivative). Then the lift of the
reparametrized loop is *constant* near `0,1` (continuity + local injectivity of `f`),
hence trivially smooth with zero velocity there, while the interior is handled by B —
sidestepping any one-sided gluing. -/

/-- A smooth reparametrization of the unit interval, **constant near the endpoints**:
`flatEndReparam t = Real.smoothTransition (2 t - 1/2)`. It is `≡ 0` on `(-∞, 1/4]`,
`≡ 1` on `[3/4, ∞)`, smooth, monotone, maps `[0,1]` into `[0,1]`, and fixes the
endpoints (`0 ↦ 0`, `1 ↦ 1`). The end plateaus are what make a lift of
`δ ∘ flatEndReparam` constant near the seam. -/
noncomputable def flatEndReparam (t : ℝ) : ℝ := Real.smoothTransition (2 * t - 1 / 2)

@[simp] theorem flatEndReparam_zero : flatEndReparam 0 = 0 := by
  unfold flatEndReparam; rw [Real.smoothTransition.zero_of_nonpos (by norm_num)]

@[simp] theorem flatEndReparam_one : flatEndReparam 1 = 1 := by
  unfold flatEndReparam; rw [Real.smoothTransition.one_of_one_le (by norm_num)]

/-- `flatEndReparam` is `≡ 0` on the left plateau `(-∞, 1/4]`. -/
theorem flatEndReparam_eqZero_of_le {t : ℝ} (ht : t ≤ 1 / 4) : flatEndReparam t = 0 := by
  unfold flatEndReparam; exact Real.smoothTransition.zero_of_nonpos (by linarith)

/-- `flatEndReparam` is `≡ 1` on the right plateau `[3/4, ∞)`. -/
theorem flatEndReparam_eqOne_of_ge {t : ℝ} (ht : 3 / 4 ≤ t) : flatEndReparam t = 1 := by
  unfold flatEndReparam; exact Real.smoothTransition.one_of_one_le (by linarith)

theorem flatEndReparam_mem_unit (t : ℝ) : flatEndReparam t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem contDiff_flatEndReparam {n : ℕ∞} : ContDiff ℝ n flatEndReparam :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

theorem differentiable_flatEndReparam : Differentiable ℝ flatEndReparam :=
  (contDiff_flatEndReparam (n := 1)).differentiable (by norm_num)

theorem flatEndReparam_hasDerivAt (t : ℝ) :
    HasDerivAt flatEndReparam (deriv flatEndReparam t) t :=
  (differentiable_flatEndReparam t).hasDerivAt

theorem flatEndReparam_monotone : Monotone flatEndReparam := by
  intro a b hab; unfold flatEndReparam; exact Real.smoothTransition.monotone (by linarith)

theorem flatEndReparam_image_Icc : flatEndReparam '' Set.Icc (0:ℝ) 1 = Set.Icc 0 1 := by
  apply Set.eq_of_subset_of_subset
  · rintro u ⟨t, -, rfl⟩; exact flatEndReparam_mem_unit t
  · have h := intermediate_value_Icc (zero_le_one (α := ℝ))
      differentiable_flatEndReparam.continuous.continuousOn
    rwa [flatEndReparam_zero, flatEndReparam_one] at h

/-- Reparametrized pathSpeed (chain rule): `pathSpeed (γ ∘ flatEndReparam) t =
flatEndReparam'(t) · pathSpeed γ (flatEndReparam t)`. Mirrors
`pathSpeed_smoothStep01_comp_eq`. -/
theorem pathSpeed_flatEndReparam_comp_eq (γ : ℝ → X) (t : ℝ)
    (hγ_diff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (γ (flatEndReparam t))).toFun ∘ γ) (flatEndReparam t)) :
    pathSpeed (γ ∘ flatEndReparam) t =
      ((deriv flatEndReparam t : ℝ) : ℂ) * pathSpeed γ (flatEndReparam t) := by
  unfold pathSpeed
  have h_assoc : (chartAt (H := ℂ) ((γ ∘ flatEndReparam) t)).toFun ∘ (γ ∘ flatEndReparam) =
      ((chartAt (H := ℂ) (γ (flatEndReparam t))).toFun ∘ γ) ∘ flatEndReparam := by
    funext s; rfl
  rw [h_assoc]
  have hσ : HasDerivAt flatEndReparam (deriv flatEndReparam t) t := flatEndReparam_hasDerivAt t
  have hφ : HasDerivAt ((chartAt (H := ℂ) (γ (flatEndReparam t))).toFun ∘ γ)
      (pathSpeed γ (flatEndReparam t)) (flatEndReparam t) := hγ_diff.hasDerivAt
  have h_comp : HasDerivAt
      (((chartAt (H := ℂ) (γ (flatEndReparam t))).toFun ∘ γ) ∘ flatEndReparam)
      (deriv flatEndReparam t • pathSpeed γ (flatEndReparam t)) t := hφ.scomp t hσ
  have h_deriv := h_comp.deriv
  have h_lhs_eq : (fderiv ℝ
      (((chartAt (H := ℂ) (γ (flatEndReparam t))).toFun ∘ γ) ∘ flatEndReparam) t) 1 =
      deriv flatEndReparam t • pathSpeed γ (flatEndReparam t) := by rw [← h_deriv]; rfl
  rw [h_lhs_eq]; exact Complex.real_smul

/-- **Reparametrization-invariance of the line integral** (the textbook monotone
change of variables). Reparametrizing a (regular, integrable) path by the monotone
`flatEndReparam` leaves the line integral unchanged. Uses Mathlib's measure-theoretic
monotone CoV `integral_image_eq_integral_deriv_smul_of_monotoneOn` (valid for merely
*integrable* integrands — no `C¹` needed), exactly the value-level companion of the
`smoothStep01` integrability argument in `isSmoothPath_smoothPathSmooth`. The key to
transporting the preimage-cycle construction from `δ∘flatEndReparam` back to `δ`. -/
theorem lineIntegral_comp_flatEndReparam (α : HolomorphicOneForms X) (γ : ℝ → X)
    (hγ_diff : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) :
    lineIntegral α (γ ∘ flatEndReparam) = lineIntegral α γ := by
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  -- The monotone change-of-variables (value version) for the integrand of `γ`.
  have hcov := MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
    (s := Set.Icc (0:ℝ) 1) measurableSet_Icc (f := flatEndReparam) (f' := deriv flatEndReparam)
    (fun x _ => (flatEndReparam_hasDerivAt x).hasDerivWithinAt) (flatEndReparam_monotone.monotoneOn _)
    (fun u => α.toFun (γ u) (pathSpeed γ u))
  rw [flatEndReparam_image_Icc] at hcov
  -- `lineIntegral α γ` as a set integral over `Icc 0 1`.
  have hRHS : lineIntegral α γ = ∫ x in Set.Icc (0:ℝ) 1, α.toFun (γ x) (pathSpeed γ x) := by
    unfold lineIntegral
    rw [intervalIntegral.integral_of_le h01, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- `lineIntegral α (γ∘r)` as the reparametrized set integral over `Icc 0 1`.
  have hLHS : lineIntegral α (γ ∘ flatEndReparam) =
      ∫ x in Set.Icc (0:ℝ) 1,
        deriv flatEndReparam x • α.toFun (γ (flatEndReparam x)) (pathSpeed γ (flatEndReparam x)) := by
    unfold lineIntegral
    rw [intervalIntegral.integral_of_le h01, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
    have hrt : flatEndReparam t ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le h01]; exact flatEndReparam_mem_unit t
    have hps := pathSpeed_flatEndReparam_comp_eq γ t (hγ_diff (flatEndReparam t) hrt)
    show α.toFun (γ (flatEndReparam t)) (pathSpeed (γ ∘ flatEndReparam) t) =
      deriv flatEndReparam t • α.toFun (γ (flatEndReparam t)) (pathSpeed γ (flatEndReparam t))
    rw [hps]
    have h_lin : (α.toFun (γ (flatEndReparam t)))
          (((deriv flatEndReparam t : ℝ) : ℂ) * pathSpeed γ (flatEndReparam t)) =
        ((deriv flatEndReparam t : ℝ) : ℂ) *
          (α.toFun (γ (flatEndReparam t))) (pathSpeed γ (flatEndReparam t)) := by
      have h_ml := (α.toFun (γ (flatEndReparam t))).map_smul
        ((deriv flatEndReparam t : ℝ) : ℂ) (pathSpeed γ (flatEndReparam t))
      simp only [smul_eq_mul] at h_ml
      exact h_ml
    rw [h_lin, Complex.real_smul]
  rw [hLHS, hRHS]; exact hcov.symm

/-- **Period vector is `flatEndReparam`-invariant.** A closed smooth loop and its
seam-flattened reparametrization `γ ∘ flatEndReparam` have the same period vector
(componentwise `lineIntegral_comp_flatEndReparam`). This is what lets the
preimage-cycle construction, carried out for `δ ∘ flatEndReparam`, transport back to
`δ` (via `PreimageCycle.congr_periodVec`). -/
theorem periodVec_comp_flatEndReparam (γ : ℝ → X) (hγ : IsClosedSmoothLoop γ) :
    periodVec (γ ∘ flatEndReparam) = periodVec γ := by
  funext i
  exact lineIntegral_comp_flatEndReparam (periodBasisForm X i) γ hγ.diff


/-- **§3 sub-piece B — smoothness of the lift.** A continuous lift `Γ` of `δ`
through a non-critical point inherits `δ`'s chart-pullback differentiability.
Given `Γ` continuous at `t₀`, `f ∘ Γ = δ` near `t₀`, `Γ t₀` off the critical set,
and `δ` chart-pullback-differentiable at `t₀`, the lift `Γ` is chart-pullback
differentiable at `t₀`.

Proof: take the two-sided local inverse `g` at `Γ t₀`
(`exists_twoSided_localInverse`). Near `t₀`, `Γ = g ∘ δ` directly from `g∘f=id`
near `Γ t₀` + continuity of `Γ` + `f∘Γ=δ` (no lift-uniqueness needed). In charts,
`(chart_Γt₀)∘Γ =ᶠ G∘d` where `G = (chart_Γt₀)∘g∘(chart_δt₀).symm` is the chart
representation of the holomorphic `g` and `d = (chart_δt₀)∘δ`. `G` is `ℂ`-, hence
`ℝ`-differentiable (via `writtenInExtChartAt` + `restrictScalars`), so the chain
rule and `congr_of_eventuallyEq` conclude. Mirrors `IsClosedSmoothLoop.comp` /
`pathSpeed_comp_eq_mfderiv`. Foundation for assembling the lift into a smooth loop. -/
theorem differentiableAt_chart_lift_of_notMem_criticalSet
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (Γ : ℝ → X) {t₀ : ℝ}
    (hΓ_cont : ContinuousAt Γ t₀)
    (hfΓδ : ∀ᶠ t in 𝓝 t₀, f (Γ t) = δ t)
    (hΓcrit : Γ t₀ ∉ criticalSet f)
    (hδ_diff : DifferentiableAt ℝ ((chartAt (H := ℂ) (δ t₀)).toFun ∘ δ) t₀) :
    DifferentiableAt ℝ ((chartAt (H := ℂ) (Γ t₀)).toFun ∘ Γ) t₀ := by
  classical
  obtain ⟨g, V, hVopen, hfΓt₀V, hgfΓ, hsec, hg_smooth, hgf_id⟩ :=
    exists_twoSided_localInverse f hf hnonconst hΓcrit
  have hfΓt₀ : f (Γ t₀) = δ t₀ := hfΓδ.self_of_nhds
  have hδt₀V : δ t₀ ∈ V := hfΓt₀ ▸ hfΓt₀V
  have hgδt₀ : g (δ t₀) = Γ t₀ := hfΓt₀ ▸ hgfΓ
  -- Near `t₀`, the lift coincides with `g ∘ δ`.
  have hΓ_eq : Γ =ᶠ[𝓝 t₀] g ∘ δ := by
    have hgf_along : ∀ᶠ t in 𝓝 t₀, (g ∘ f) (Γ t) = id (Γ t) := hΓ_cont.tendsto.eventually hgf_id
    filter_upwards [hgf_along, hfΓδ] with t h1 h2
    show Γ t = g (δ t)
    rw [← h2]
    exact h1.symm
  -- `δ` is continuous at `t₀` (it equals `f ∘ Γ` near `t₀`).
  have hδ_contAt : ContinuousAt δ t₀ :=
    (hf.continuous.continuousAt.comp hΓ_cont).congr hfΓδ
  have hδ_source : ∀ᶠ t in 𝓝 t₀, δ t ∈ (chartAt (H := ℂ) (δ t₀)).source :=
    hδ_contAt.eventually_mem
      ((chartAt (H := ℂ) (δ t₀)).open_source.mem_nhds (mem_chart_source ℂ (δ t₀)))
  -- `g` is `MDifferentiableAt` at `δ t₀ ∈ V`.
  have hg_mdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (δ t₀) :=
    (hg_smooth.contMDiffAt (hVopen.mem_nhds hδt₀V)).mdifferentiableAt (by decide : ω ≠ 0)
  -- Chart representation `G` of `g` and chart pullback `d` of `δ`.
  set d : ℝ → ℂ := (chartAt (H := ℂ) (δ t₀)).toFun ∘ δ with hd_def
  set G : ℂ → ℂ :=
    fun z => (chartAt (H := ℂ) (Γ t₀)).toFun (g ((chartAt (H := ℂ) (δ t₀)).symm z)) with hG_def
  -- `G` is `ℝ`-differentiable at `d t₀` (holomorphic `g` in charts).
  have hG_diff_ℝ : DifferentiableAt ℝ G (d t₀) := by
    have hG_diff_ℂ : DifferentiableAt ℂ G (d t₀) := by
      have h1 := hg_mdiff.differentiableWithinAt_writtenInExtChartAt
      rw [ModelWithCorners.range_eq_univ, differentiableWithinAt_univ] at h1
      rw [hG_def, show (chartAt (H := ℂ) (Γ t₀)) = (chartAt (H := ℂ) (g (δ t₀))) from by rw [hgδt₀]]
      convert h1 using 2
    have hFD_ℂ := hG_diff_ℂ.hasFDerivAt
    have hFD_ℝ : HasFDerivAt G ((fderiv ℂ G (d t₀)).restrictScalars ℝ) (d t₀) := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hFD_ℂ ⊢
      simp only [ContinuousLinearMap.coe_restrictScalars']
      exact hFD_ℂ
    exact hFD_ℝ.differentiableAt
  -- Assemble: `chart_Γt₀ ∘ Γ =ᶠ G ∘ d`, then chain rule.
  have hcomp_eq : ((chartAt (H := ℂ) (Γ t₀)).toFun ∘ (g ∘ δ)) =ᶠ[𝓝 t₀] (G ∘ d) := by
    filter_upwards [hδ_source] with t ht
    show (chartAt (H := ℂ) (Γ t₀)) (g (δ t)) =
      (chartAt (H := ℂ) (Γ t₀)) (g ((chartAt (H := ℂ) (δ t₀)).symm ((chartAt (H := ℂ) (δ t₀)) (δ t))))
    rw [(chartAt (H := ℂ) (δ t₀)).left_inv ht]
  have hΓchart_eq : ((chartAt (H := ℂ) (Γ t₀)).toFun ∘ Γ) =ᶠ[𝓝 t₀] (G ∘ d) :=
    (hΓ_eq.fun_comp (chartAt (H := ℂ) (Γ t₀)).toFun).trans hcomp_eq
  rw [hΓchart_eq.differentiableAt_iff]
  exact hG_diff_ℝ.comp t₀ hδ_diff

/-- **§3 sub-piece C — the seam-flattened smooth lift.** Lifting the *reparametrized*
loop `δ ∘ flatEndReparam` (constant near `0,1`) off the branch locus from a fibre
point `e` yields a genuine smooth path with **zero endpoint velocity**:

* `Γ` is constant `= e` near `0` and constant `= Γ 1` near `1` (continuity + local
  injectivity of `f`, using the lift's `projIcc` clamp), so it is chart-differentiable
  with zero velocity at both endpoints;
* on the interior `(0,1)`, `Γ` is chart-differentiable by sub-piece B;
* its endpoint `Γ 1` lies in the same fibre (`f (Γ 1) = δ 0`), the monodromy target.

This is the per-segment building block of the orbit construction: concatenating these
over a monodromy orbit (zero junction velocities ⇒ `IsSmoothPath.concat`) closes the
lift into a smooth loop. The base loop is `δ ∘ flatEndReparam`, a reparametrization of
`δ` (its period vector is unchanged — recorded separately). -/
theorem exists_smoothLift_flatEnd_off_branchLocus
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f)
    {e : X} (he : f e = δ 0) :
    ∃ Γ : ℝ → X,
      Continuous Γ ∧ Γ 0 = e ∧
      (∀ t ∈ Set.Icc (0:ℝ) 1, f (Γ t) = δ (flatEndReparam t)) ∧
      (∀ t ∈ Set.uIcc (0:ℝ) 1, DifferentiableAt ℝ ((chartAt (H := ℂ) (Γ t)).toFun ∘ Γ) t) ∧
      pathSpeed Γ 0 = 0 ∧ pathSpeed Γ 1 = 0 ∧
      f (Γ 1) = δ 0 := by
  classical
  -- The reparametrized base loop `δr = δ ∘ flatEndReparam`, constant near the endpoints.
  set δr : ℝ → Y := δ ∘ flatEndReparam with hδr_def
  have hδr_cont : Continuous δr := hδ.cont.comp differentiable_flatEndReparam.continuous
  have hδr_avoid : ∀ t : ℝ, δr t ∉ branchLocus f := fun t => havoid (flatEndReparam t)
  have hδr0 : δr 0 = δ 0 := by show δ (flatEndReparam 0) = δ 0; rw [flatEndReparam_zero]
  have he' : f e = δr 0 := by rw [hδr0]; exact he
  -- Lift `δr` from `e` (sub-piece A), exposing the endpoint clamps.
  obtain ⟨Γ, hΓ_cont, hΓ_lift, hΓ0, hΓ_clampL, hΓ_clampR⟩ :=
    exists_continuous_lift_off_branchLocus f hf hnonconst δr hδr_cont hδr_avoid he'
  -- `f (Γ 1) = δ 0`.
  have hfΓ1 : f (Γ 1) = δ 0 := by
    rw [hΓ_lift 1 ⟨zero_le_one, le_rfl⟩]; show δ (flatEndReparam 1) = δ 0
    rw [flatEndReparam_one]; exact hδ.closed.symm
  -- `δr` is chart-pullback-differentiable on `[0,1]` (chain rule `δ ∘ flatEndReparam`).
  have hδr_diff : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (δr t)).toFun ∘ δr) t := by
    intro t _
    have hrt : flatEndReparam t ∈ Set.uIcc (0:ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact flatEndReparam_mem_unit t
    have hδr_comp : ((chartAt (H := ℂ) (δr t)).toFun ∘ δr) =
        ((chartAt (H := ℂ) (δ (flatEndReparam t))).toFun ∘ δ) ∘ flatEndReparam := by
      funext s; rfl
    rw [hδr_comp]
    exact (hδ.diff (flatEndReparam t) hrt).comp t (differentiable_flatEndReparam t)
  -- `Γ` is constant `= e` near `0`.
  have hΓ_const0 : Γ =ᶠ[𝓝 (0:ℝ)] (fun _ => e) := by
    have he_crit : e ∉ criticalSet f := fun hmem => (havoid 0) ⟨e, hmem, he⟩
    obtain ⟨U, hUopen, heU, hinj, -⟩ := isLocalHomeoOffCritical f hf hnonconst he_crit
    have hΓU : ∀ᶠ t in 𝓝 (0:ℝ), Γ t ∈ U :=
      hΓ_cont.continuousAt.eventually_mem (by rw [hΓ0]; exact hUopen.mem_nhds heU)
    have hfΓ0 : ∀ᶠ t in 𝓝 (0:ℝ), f (Γ t) = δ 0 := by
      filter_upwards [Iic_mem_nhds (show (0:ℝ) < 1/4 by norm_num)] with t ht
      simp only [Set.mem_Iic] at ht
      rcases le_or_gt t 0 with htle | htpos
      · rw [hΓ_clampL t htle, he]
      · rw [hΓ_lift t ⟨htpos.le, by linarith⟩]
        show δ (flatEndReparam t) = δ 0; rw [flatEndReparam_eqZero_of_le ht]
    filter_upwards [hΓU, hfΓ0] with t htU htf
    exact hinj htU heU (htf.trans he.symm)
  -- `Γ` is constant `= Γ 1` near `1`.
  have hΓ_const1 : Γ =ᶠ[𝓝 (1:ℝ)] (fun _ => Γ 1) := by
    have hΓ1_crit : Γ 1 ∉ criticalSet f := fun hmem => (havoid 0) ⟨Γ 1, hmem, hfΓ1⟩
    obtain ⟨U, hUopen, hΓ1U, hinj, -⟩ := isLocalHomeoOffCritical f hf hnonconst hΓ1_crit
    have hΓU : ∀ᶠ t in 𝓝 (1:ℝ), Γ t ∈ U :=
      hΓ_cont.continuousAt.eventually_mem (hUopen.mem_nhds hΓ1U)
    have hfΓ1' : ∀ᶠ t in 𝓝 (1:ℝ), f (Γ t) = δ 0 := by
      filter_upwards [Ici_mem_nhds (show (3/4:ℝ) < 1 by norm_num)] with t ht
      simp only [Set.mem_Ici] at ht
      rcases le_or_gt 1 t with htge | htlt
      · rw [hΓ_clampR t htge, hfΓ1]
      · rw [hΓ_lift t ⟨by linarith, htlt.le⟩]
        show δ (flatEndReparam t) = δ 0; rw [flatEndReparam_eqOne_of_ge ht]; exact hδ.closed.symm
    filter_upwards [hΓU, hfΓ1'] with t htU htf
    exact hinj htU hΓ1U (htf.trans hfΓ1.symm)
  -- Chart-pullback differentiability on `[0,1]`.
  have hΓ_diff : ∀ t ∈ Set.uIcc (0:ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (Γ t)).toFun ∘ Γ) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    obtain ⟨ht0, ht1⟩ := ht
    rcases eq_or_lt_of_le ht0 with rfl | h0pos
    · have hc : ((chartAt (H := ℂ) (Γ 0)).toFun ∘ Γ) =ᶠ[𝓝 (0:ℝ)]
          (fun _ => (chartAt (H := ℂ) (Γ 0)).toFun e) := hΓ_const0.fun_comp _
      rw [hc.differentiableAt_iff]; exact differentiableAt_const _
    · rcases eq_or_lt_of_le ht1 with rfl | h1lt
      · have hc : ((chartAt (H := ℂ) (Γ 1)).toFun ∘ Γ) =ᶠ[𝓝 (1:ℝ)]
            (fun _ => (chartAt (H := ℂ) (Γ 1)).toFun (Γ 1)) := hΓ_const1.fun_comp _
        rw [hc.differentiableAt_iff]; exact differentiableAt_const _
      · refine differentiableAt_chart_lift_of_notMem_criticalSet f hf hnonconst δr Γ
          hΓ_cont.continuousAt ?_ ?_ ?_
        · filter_upwards [Ioo_mem_nhds h0pos h1lt] with s hs
          exact hΓ_lift s ⟨hs.1.le, hs.2.le⟩
        · exact fun hmem => (hδr_avoid t) ⟨Γ t, hmem, hΓ_lift t ⟨h0pos.le, h1lt.le⟩⟩
        · exact hδr_diff t (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact ⟨h0pos.le, h1lt.le⟩)
  -- Zero endpoint velocities (chart pullback is eventually constant).
  have hps0 : pathSpeed Γ 0 = 0 := by
    have hc : ((chartAt (H := ℂ) (Γ 0)).toFun ∘ Γ) =ᶠ[𝓝 (0:ℝ)]
        (fun _ => (chartAt (H := ℂ) (Γ 0)).toFun e) := hΓ_const0.fun_comp _
    show fderiv ℝ ((chartAt (H := ℂ) (Γ 0)).toFun ∘ Γ) 0 1 = 0
    rw [hc.fderiv_eq]; simp
  have hps1 : pathSpeed Γ 1 = 0 := by
    have hc : ((chartAt (H := ℂ) (Γ 1)).toFun ∘ Γ) =ᶠ[𝓝 (1:ℝ)]
        (fun _ => (chartAt (H := ℂ) (Γ 1)).toFun (Γ 1)) := hΓ_const1.fun_comp _
    show fderiv ℝ ((chartAt (H := ℂ) (Γ 1)).toFun ∘ Γ) 1 1 = 0
    rw [hc.fderiv_eq]; simp
  exact ⟨Γ, hΓ_cont, hΓ0, hΓ_lift, hΓ_diff, hps0, hps1, hfΓ1⟩

/-- **[open] — geometric heart of the preimage-cycle lift.** The monodromy/orbit
construction, stated **purely in elementary line-integral / period-vector terms**
(no ambient-coordinate `ambientPullbackJac`): off the branch locus, `δ` lifts to a
finite ℤ-family of closed smooth loops realizing
* the **projection identity** `∫_δ traceFormTotal(ωⱼ^X) = ∑ᵢ coeffsᵢ • periodVec(loopsᵢ)ⱼ`
  (the per-component pullback, before coordinatization), and
* the **pushforward identity** `∑ᵢ coeffsᵢ • periodVec(f∘loopsᵢ) = sheets • periodVec δ`.

The reduction `exists_preimageCycle_of_off_branchLocus` below turns this into a
`PreimageCycle` via the **proven** coordinate bridge
`ambientPullbackJac_periodVec_apply_eq_lineIntegral_traceFormTotal` — so this lemma
isolates exactly the remaining *geometry*.

What it still needs (all infrastructure is identified; see
`docs/preimage_cycle_lift_plan.md`):
* the seam-flattened smooth lifts `exists_smoothLift_flatEnd_off_branchLocus` (DONE),
  one per fibre point (`fiber_finite_off_branchLocus` ⇒ `Fintype`), assembled into a
  monodromy permutation via lift uniqueness (`IsCoveringMap.eq_liftPath_iff`) and
  concatenated over its orbits (`IsSmoothPath.concat`, junction velocities zero);
* the partition/sheet-reassembly projection formula (`exists_nbhd_cover` +
  `exists_localSheetSystem_traceForm_eq_sum` + `lineIntegral_pullback_section`);
* two **analytic facts currently gated on a Mathlib gap** — the lifts' integrability
  and line-integral reparametrization-invariance `periodVec (δ∘flatEndReparam) =
  periodVec δ` — both reducing to a **change-of-variables for *integrable* (not
  merely continuous) integrands** under a monotone `C¹` reparametrization. -/
theorem exists_preimageLoopFamily (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f) :
    ∃ (m : ℕ) (loops : Fin m → ℝ → X) (coeffs : Fin m → ℤ) (sheets : ℕ),
      (∀ i, IsClosedSmoothLoop (loops i)) ∧
      (fun j => lineIntegral (traceFormTotal f hf (periodBasisForm X j)) δ) =
        ∑ i, coeffs i • periodVec (loops i) ∧
      ∑ i, coeffs i • periodVec (f ∘ loops i) = (sheets : ℤ) • periodVec δ :=
  sorry

/-- **A closed smooth loop off the branch locus lifts to a preimage cycle.** The
coordinate-layer reduction is now **proven**: it takes the elementary geometric
loop family `exists_preimageLoopFamily` and packages it as a `PreimageCycle`, the
only nontrivial step being the projection identity's conversion from the line-integral
form `∫_δ trace(ωⱼ)` to the ambient pullback `(ambientPullbackJac f hf (periodVec δ))ⱼ`
via the proven bridge `ambientPullbackJac_periodVec_apply_eq_lineIntegral_traceFormTotal`
(integrability supplied by `hδ.integrable`). The remaining content is entirely inside
`exists_preimageLoopFamily` (the monodromy/projection geometry). -/
theorem exists_preimageCycle_of_off_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) (havoid : ∀ t : ℝ, δ t ∉ branchLocus f) :
    Nonempty (PreimageCycle f hf δ) := by
  obtain ⟨m, loops, coeffs, sheets, hclosed, hproj, hpush⟩ :=
    exists_preimageLoopFamily f hf hnonconst δ hδ havoid
  refine ⟨⟨m, loops, hclosed, coeffs, sheets, ?_, hpush⟩⟩
  -- Convert the projection identity to the ambient pullback via the proven bridge.
  have hb : ambientPullbackJac (gX := genus X) (gY := genus Y) f hf (periodVec δ) =
      (fun j => lineIntegral (traceFormTotal f hf (periodBasisForm X j)) δ) := by
    funext j
    exact ambientPullbackJac_periodVec_apply_eq_lineIntegral_traceFormTotal f hf δ j hδ.integrable
  rw [hb, hproj]

/-- **[PROVEN]** A `PreimageCycle` depends on `δ` only through `periodVec δ`
(the only places `δ` enters the data are the pullback/pushforward identities,
whose `δ`-dependence is exactly through `periodVec δ`). Transporting along a
period-vector equality reuses the same loops/coeffs. -/
def PreimageCycle.congr_periodVec {f : X → Y} {hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f}
    {δ δ' : ℝ → Y} (h : periodVec δ = periodVec δ') (c : PreimageCycle f hf δ') :
    PreimageCycle f hf δ where
  n := c.n
  loops := c.loops
  loops_smooth := c.loops_smooth
  coeffs := c.coeffs
  sheets := c.sheets
  pullback_eq := by rw [h]; exact c.pullback_eq
  pushforward_eq := by rw [h]; exact c.pushforward_eq

/-- **[PROVEN]** `exists_preimageCycle_of_nonconstant`, assembled: homotope `δ`
off the branch locus, lift it to a preimage cycle, and transport back
along the period-vector equality (`congr_periodVec`). -/
theorem exists_preimageCycle_of_nonconstant (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    Nonempty (PreimageCycle f hf δ) := by
  obtain ⟨δ', hδ', hpv, havoid⟩ := exists_loop_off_branchLocus f hf hnonconst δ hδ
  obtain ⟨c⟩ := exists_preimageCycle_of_off_branchLocus f hf hnonconst δ' hδ' havoid
  exact ⟨PreimageCycle.congr_periodVec hpv.symm c⟩

/-- **Pullback identity — member case.** For a closed smooth loop `δ`
in `Y`, the genuine pullback `ambientPullbackJac (periodVec δ)` lies
in `truePeriodLattice X`. Case-splits on constancy of `f`:

* If `f` is constant, `ambientPullbackJac f hf = 0`
  (`ambientPullbackJac_eq_zero_of_const`), so the image is `0`.
* If `f` is non-constant, extract a preimage cycle witness via
  `exists_preimageCycle_of_nonconstant`, then apply the algebraic reduction
  `ambientPullbackJac_periodVec_mem_truePeriodLattice_of_preimageCycle`. -/
theorem ambientPullbackJac_periodVec_mem_truePeriodLattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (δ : ℝ → Y) (hδ : IsClosedSmoothLoop δ) :
    ambientPullbackJac (gX := genus X) (gY := genus Y) f hf (periodVec δ) ∈
      truePeriodLattice X := by
  by_cases hconst : ∃ y₀ : Y, ∀ x, f x = y₀
  · -- Constant case: ambientPullbackJac = 0.
    rw [ambientPullbackJac_eq_zero_of_const f hf hconst]
    simp
  · -- Non-constant case: extract a preimage cycle and apply the algebraic
    -- reduction.
    obtain ⟨c⟩ := exists_preimageCycle_of_nonconstant f hf hconst δ hδ
    exact ambientPullbackJac_periodVec_mem_truePeriodLattice_of_preimageCycle f hf δ c

/-- `ambientPullbackJac` (the genuine Jacobian pullback `Tᵀ`) preserves the period
lattice. Reduces to `ambientPullbackJac_periodVec_mem_truePeriodLattice` on
closed-loop generators, extended to the ℤ-span by `Submodule.span_induction` and
ℤ-linearity. Discharges `Jacobian.ambientPullbackJac_preserves_lattice`. -/
theorem ambientPullbackJac_preserves_truePeriodLattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (truePeriodLattice Y).toAddSubgroup ≤
      (truePeriodLattice X).toAddSubgroup.comap
        (ambientPullbackJac (gX := genus X) (gY := genus Y) f hf).toAddMonoidHom := by
  show ∀ v ∈ truePeriodLattice Y,
    ambientPullbackJac (gX := genus X) (gY := genus Y) f hf v ∈ truePeriodLattice X
  intro v hv
  refine Submodule.span_induction
    (p := fun v _ => ambientPullbackJac (gX := genus X) (gY := genus Y) f hf v ∈
      truePeriodLattice X) ?_ ?_ ?_ ?_ hv
  · -- Generator case: v = periodVec δ for a closed smooth loop δ in Y.
    rintro _ ⟨δ, hδ, rfl⟩
    exact ambientPullbackJac_periodVec_mem_truePeriodLattice f hf δ hδ
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
