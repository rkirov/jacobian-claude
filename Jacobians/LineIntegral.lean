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

end Jacobians
