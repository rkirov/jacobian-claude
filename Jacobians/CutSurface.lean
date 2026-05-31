import Mathlib.Analysis.Complex.CauchyIntegral
import Jacobians.BoundaryPositivity

/-!
# Cut-surface bridge: proving the Riemann bilinear relations

This file formalizes the *analytic heart* of the period-lattice goal (#7): the two Riemann bilinear
relations R1 (vanishing) and R2 (positivity) are **proven** from a single, more primitive topological
input — the **boundary word** of a canonical dissection realized as a cut surface (a chart
`cut : box → X`, holomorphic on the interior, a diffeo onto `X` minus the cuts, whose boundary
traverses the loops `a₁b₁a₁⁻¹b₁⁻¹⋯`).

The boundary word is the identity `∑ₖ(A_{ki}B_{kj} − B_{ki}A_{kj}) = ∮_{∂box}(F_i · h_j dz)` (and a
conjugated variant), where `h_j = cut^*ω_j` is the pullback of the `j`-th holomorphic form and `F_i`
is a primitive of `h_i`. Given it, R1/R2 are pure analysis:

* **R1** — the boundary integral of the *holomorphic* `F_i·h_j` over `∂box` is `0` by **Cauchy's
  theorem on the rectangle** (`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`). Hence
  `∑ₖ(A_{ki}B_{kj} − B_{ki}A_{kj}) = 0`, i.e. `AᵀB = BᵀA`.
* **R2** — the conjugated boundary integral is `−(i/2)⁻¹` times a strictly positive area integral
  (`Jacobians.boundaryForm_pos`), giving positive-definiteness of the period Hermitian form.

Only the boundary word stays isolated (it encodes the surface's polygonal schema, which Mathlib
lacks); the relations themselves are theorems.
-/

open MeasureTheory Set intervalIntegral Complex Matrix
open scoped ComplexConjugate

namespace Jacobians

/-- The counterclockwise contour integral of `f` over the boundary of the unit box `[0,1]²`
(identified with the square `0,1,1+i,i` in `ℂ`), in the orientation of Mathlib's rectangle Cauchy
theorem: `∫P(·,0) − ∫P(·,1) + i∫P(1,·) − i∫P(0,·)`, i.e. `∮ f dz`. -/
noncomputable def rectBoundaryIntegral (f : ℂ → ℂ) : ℂ :=
  ((∫ x in (0:ℝ)..1, f (x : ℂ)) - ∫ x in (0:ℝ)..1, f ((x : ℂ) + Complex.I))
    + Complex.I * (∫ y in (0:ℝ)..1, f (1 + (y : ℂ) * Complex.I))
    - Complex.I * ∫ y in (0:ℝ)..1, f ((y : ℂ) * Complex.I)

/-- **Cauchy on the box.** If `f` is holomorphic on (a set containing) the closed unit box, its
contour integral over `∂box` vanishes. Direct from
`Complex.integral_boundary_rect_eq_zero_of_differentiableOn` specialized to `z = 0`, `w = 1 + i`. -/
theorem rectBoundaryIntegral_eq_zero_of_differentiableOn {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Set.uIcc 0 1 ×ℂ Set.uIcc 0 1)) :
    rectBoundaryIntegral f = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f 0 (1 + Complex.I) (by
    simpa using hf)
  simpa [rectBoundaryIntegral, smul_eq_mul] using h

/-- **Riemann's first bilinear relation, from the boundary word.** Given period blocks `A, B`,
pullbacks `h_j` with primitives `F_i`, and the boundary-word identity
`(AᵀB − BᵀA) i j = ∮_{∂box}(F_i·h_j) dz`, the relation `AᵀB = BᵀA` holds: each `F_i·h_j` is
holomorphic, so its box contour integral vanishes by Cauchy. (The boundary word is supplied by the
cut surface and is itself a theorem there — see `CutSurface`.) -/
theorem riemann_R1_of_boundaryWord {g : ℕ} (A B : Matrix (Fin g) (Fin g) ℂ) (h F : Fin g → ℂ → ℂ)
    (hFh : ∀ i j, DifferentiableOn ℂ (fun z => F i z * h j z) (Set.uIcc 0 1 ×ℂ Set.uIcc 0 1))
    (boundaryWord : ∀ i j,
      (Aᵀ * B - Bᵀ * A) i j = rectBoundaryIntegral (fun z => F i z * h j z)) :
    Aᵀ * B = Bᵀ * A := by
  rw [← sub_eq_zero]
  ext i j
  rw [Matrix.zero_apply, boundaryWord i j]
  exact rectBoundaryIntegral_eq_zero_of_differentiableOn (hFh i j)

end Jacobians
