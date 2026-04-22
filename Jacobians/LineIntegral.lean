import Jacobians.HolomorphicForms
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Line integral of a holomorphic 1-form along a smooth path

Defines

  `∫_γ α := ∫ t in 0..1, α(γ t) (γ'(t)) dt`

for `γ : ℝ → X` a path into a compact connected complex 1-manifold and
`α : HolomorphicOneForms X`.

## Base-field workaround

`mfderiv` expects the source and target manifolds to share a base field.
For `γ : ℝ → X` (real source, complex target), we bypass this by
computing `γ'(t)` **via a chart**:

  `γ'(t) ≈ fderiv ℝ ((chartAt ℂ (γ t)).toFun ∘ γ) t 1 : ℂ`

The value of this expression is the "complex speed of `γ` at `t`",
expressed in the local chart around `γ t`. It coincides with the
intrinsic tangent vector modulo the chart identification
`TangentSpace 𝓘(ℂ) (γ t) = ℂ` that Mathlib uses.

Chart-independence of the line integral (the full "intrinsic"
well-definedness) is a TODO(math).

## References

Forster §§10–12; Miranda Ch. 4 §§3–4.
-/

namespace Jacobians

open scoped Manifold ContDiff Bundle
open MeasureTheory

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Complex speed of `γ` at `t`, expressed in the chart around `γ t`. -/
noncomputable def pathSpeed (γ : ℝ → X) (t : ℝ) : ℂ :=
  fderiv ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t 1

/-- Line integral of a holomorphic 1-form `α` along a smooth path `γ`.

`∫_γ α := ∫ t in 0..1, α(γ t)(γ'(t))`, where `γ'(t)` is computed via
`pathSpeed`. -/
noncomputable def lineIntegral (α : HolomorphicOneForms X) (γ : ℝ → X) : ℂ :=
  ∫ t in (0 : ℝ)..1, α.toFun (γ t) (pathSpeed γ t)

/-! ### Phase 1a of the Abel–Jacobi plan: vector line integral -/

/-- Vector line integral of a tuple of holomorphic 1-forms along `γ`.
The building block for the "period map" `Fin (genus X) → ℂ` whose
image (over closed loops at a basepoint) is the period lattice. -/
noncomputable def lineIntegralVec {n : ℕ} (forms : Fin n → HolomorphicOneForms X)
    (γ : ℝ → X) : Fin n → ℂ :=
  fun i => lineIntegral (forms i) γ

@[simp]
theorem lineIntegralVec_apply {n : ℕ} (forms : Fin n → HolomorphicOneForms X)
    (γ : ℝ → X) (i : Fin n) :
    lineIntegralVec forms γ i = lineIntegral (forms i) γ := rfl

/-! ### Phase 1b: linearity of the line integral in the form

Immediate from pointwise addition/scalar action on `ContMDiffSection`
sections and `intervalIntegral` linearity. The algebraic identities
are stated; integrability hypotheses are passed in for `lineIntegral_add`
(a separate technical lemma, "smooth path ⇒ continuous integrand ⇒
integrable on [0,1]", will add a hypothesis-free variant once the
path-regularity infrastructure is built out). -/

/-- `lineIntegral (0 : HOF X) γ = 0`. -/
theorem lineIntegral_zero (γ : ℝ → X) :
    lineIntegral (0 : HolomorphicOneForms X) γ = 0 := by
  unfold lineIntegral
  have h_zero : ∀ t : ℝ,
      (0 : HolomorphicOneForms X).toFun (γ t) (pathSpeed γ t) = 0 := fun _ => rfl
  simp_rw [h_zero]
  exact intervalIntegral.integral_zero

/-- Additivity of `lineIntegral` in the form, under integrability. -/
theorem lineIntegral_add (α β : HolomorphicOneForms X) (γ : ℝ → X)
    (hα : IntervalIntegrable (fun t : ℝ => α.toFun (γ t) (pathSpeed γ t))
      MeasureTheory.volume 0 1)
    (hβ : IntervalIntegrable (fun t : ℝ => β.toFun (γ t) (pathSpeed γ t))
      MeasureTheory.volume 0 1) :
    lineIntegral (α + β) γ = lineIntegral α γ + lineIntegral β γ := by
  unfold lineIntegral
  have h_pw : ∀ t : ℝ,
      (α + β).toFun (γ t) (pathSpeed γ t) =
        α.toFun (γ t) (pathSpeed γ t) + β.toFun (γ t) (pathSpeed γ t) := fun _ => rfl
  simp_rw [h_pw]
  exact intervalIntegral.integral_add hα hβ

/-- Scalar-homogeneity of `lineIntegral` in the form. -/
theorem lineIntegral_smul (c : ℂ) (α : HolomorphicOneForms X) (γ : ℝ → X) :
    lineIntegral (c • α) γ = c * lineIntegral α γ := by
  unfold lineIntegral
  have h_pw : ∀ t : ℝ,
      (c • α).toFun (γ t) (pathSpeed γ t) = c * α.toFun (γ t) (pathSpeed γ t) := by
    intro t
    show (c • α.toFun (γ t)) (pathSpeed γ t) = _
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  simp_rw [h_pw]
  exact intervalIntegral.integral_const_mul c _

/-- Negation: `lineIntegral (-α) γ = -lineIntegral α γ`. -/
theorem lineIntegral_neg (α : HolomorphicOneForms X) (γ : ℝ → X) :
    lineIntegral (-α) γ = -lineIntegral α γ := by
  have h : -α = (-1 : ℂ) • α := by rw [neg_smul, one_smul]
  rw [h, lineIntegral_smul]; ring

/-! ### Phase 1b: path reversal

`reverse γ t := γ (1 - t)`, and the line integral flips sign under
reversal. The pathSpeed identity `pathSpeed (reverse γ) t =
-pathSpeed γ (1 - t)` holds under differentiability of the chart
pullback at `1 - t`. -/

/-- Time-reversal of a path: `reverse γ t := γ (1 - t)`. -/
def reverse (γ : ℝ → X) : ℝ → X := fun t => γ (1 - t)

omit [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] in
@[simp] theorem reverse_apply (γ : ℝ → X) (t : ℝ) :
    reverse γ t = γ (1 - t) := rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [IsManifold 𝓘(ℂ) ω X] in
/-- pathSpeed under reversal: sign flip + reparametrization. Requires
chart-pullback `(chartAt ℂ (γ(1-t))).toFun ∘ γ` to be differentiable
at `1 - t` (which holds for smooth γ at points in the chart source). -/
theorem pathSpeed_reverse (γ : ℝ → X) (t : ℝ)
    (hdiff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (γ (1 - t))).toFun ∘ γ) (1 - t)) :
    pathSpeed (reverse γ) t = -pathSpeed γ (1 - t) := by
  unfold pathSpeed
  -- reverse γ t = γ (1 - t), so chartAt at (reverse γ t) = chartAt at (γ (1 - t)).
  show fderiv ℝ ((chartAt (H := ℂ) (γ (1 - t))).toFun ∘ (reverse γ)) t (1 : ℝ) =
    -fderiv ℝ ((chartAt (H := ℂ) (γ (1 - t))).toFun ∘ γ) (1 - t) (1 : ℝ)
  -- (chartAt).toFun ∘ (reverse γ) = (chartAt).toFun ∘ γ ∘ (1 - ·)
  set ψ : ℝ → ℂ := (chartAt (H := ℂ) (γ (1 - t))).toFun ∘ γ with hψ
  have h_comp : (chartAt (H := ℂ) (γ (1 - t))).toFun ∘ (reverse γ) =
      ψ ∘ (fun s : ℝ => 1 - s) := by
    funext s; simp [reverse, hψ, Function.comp_def]
  rw [h_comp]
  -- Chain rule: fderiv (ψ ∘ (1-·)) t 1 = fderiv ψ (1-t) (fderiv (1-·) t 1).
  have h_sub_diff : DifferentiableAt ℝ (fun s : ℝ => 1 - s) t :=
    (differentiableAt_const _).sub differentiableAt_id
  rw [fderiv_comp t hdiff h_sub_diff]
  -- fderiv (1-·) t applied at 1 = -1 (the derivative of `1 - s` is `-1`).
  have h_fderiv_sub : fderiv ℝ (fun s : ℝ => 1 - s) t (1 : ℝ) = (-1 : ℝ) := by
    rw [fderiv_const_sub]; simp
  show (fderiv ℝ ψ (1 - t)) (fderiv ℝ (fun s : ℝ => 1 - s) t 1) = -fderiv ℝ ψ (1 - t) 1
  rw [h_fderiv_sub]
  rw [show ((fderiv ℝ ψ (1 - t)) (-1 : ℝ) : ℂ) = -fderiv ℝ ψ (1 - t) (1 : ℝ) from by
    rw [show (-1 : ℝ) = -(1 : ℝ) from rfl, (fderiv ℝ ψ (1 - t)).map_neg]]

/-- Line integral reverses sign under path reversal, under
differentiability of the chart pullback on [0, 1]. -/
theorem lineIntegral_reverse (α : HolomorphicOneForms X) (γ : ℝ → X)
    (hdiff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ (1 - t))).toFun ∘ γ) (1 - t)) :
    lineIntegral α (reverse γ) = -lineIntegral α γ := by
  unfold lineIntegral
  -- α.toFun((reverse γ) t)(pathSpeed (reverse γ) t) = -α.toFun(γ(1-t))(pathSpeed γ(1-t)).
  have h_pw : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      α.toFun ((reverse γ) t) (pathSpeed (reverse γ) t) =
        -α.toFun (γ (1 - t)) (pathSpeed γ (1 - t)) := by
    intro t ht
    rw [reverse_apply, pathSpeed_reverse γ t (hdiff t ht)]
    exact (α.toFun (γ (1 - t))).map_neg _
  rw [intervalIntegral.integral_congr h_pw, intervalIntegral.integral_neg]
  -- ∫_0^1 α(γ(1-t))(pathSpeed γ(1-t)) dt = ∫_0^1 α(γ u)(pathSpeed γ u) du
  -- via substitution u = 1 - t.
  congr 1
  have h_sub := intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => α.toFun (γ u) (pathSpeed γ u)) 1 (a := 0) (b := 1)
  simp at h_sub
  exact h_sub

end Jacobians
