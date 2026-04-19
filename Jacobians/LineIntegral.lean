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

end Jacobians
