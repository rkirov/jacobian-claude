/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.BoundaryPositivity
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

/-!
# Riemann's second bilinear relation, from the boundary word

This is the box-layer analytic core for **R2** (positive-definiteness of the period Hermitian form),
the companion of `Jacobians.riemann_R1_of_boundaryWord` (the box-layer R1).

Given period blocks `A B : Matrix (Fin g) (Fin g) ℂ`, pullback coefficients `h_j` (`= cut^*ω_j`)
holomorphic on a convex open `U ⊇ [0,1]²` with primitives `F_i` (`F_i' = h_i`), the **boundary word**
identity (the genuinely topological input, supplied by the cut surface)

  `(Aᵀ·B̄ − Bᵀ·Ā)_{ij} = − boundaryForm (h_j) (F_i)`   (`boundaryForm (h) (F) = ∮_{∂box} F̄·h dz`)

together with non-degeneracy of the pullbacks forces the Hermitian form `H = i·(Aᵀ·B̄ − Bᵀ·Ā)` to be
**positive definite**. The proof is pure box-level analysis:

* `boundaryForm` is bilinear (`boundaryForm_combo`), so the quadratic form `vᴴ(Aᵀ·B̄ − Bᵀ·Ā)v`
  collapses to `−boundaryForm (h_v) (F_v)` for the combinations `h_v = ∑ⱼ vⱼ hⱼ`, `F_v = ∑ᵢ vᵢ Fᵢ`;
* `Jacobians.boundaryForm_pos` makes `−(i/2)·boundaryForm (h_v) (F_v)` a strictly positive real
  (Green's theorem: it equals `∬_box ‖h_v‖² > 0`), since `h_v ≠ 0` somewhere in the open box;
* hence `vᴴ H v = i·(−boundaryForm (h_v) (F_v)) = 2·(∬‖h_v‖²) > 0`.

The sign is validated at `g = 1`: the standard torus `ℂ/(ℤ+ℤτ)` gives `vᴴ H v = 2·Im τ > 0`.

No surface topology enters here — only matrix algebra, interval integrals, and the proven Green
positivity bridge. This is a "hard Lean, no missing math" leaf.
-/

open MeasureTheory Set intervalIntegral Complex Matrix
open scoped ComplexConjugate ComplexOrder

namespace Jacobians

variable {g : ℕ}

/-- A single boundary-edge contribution `∫₀¹ F̄(γ t)·h(γ t) dt`, the building block of
`boundaryForm`. -/
noncomputable def edgeBF (γ : ℝ → ℂ) (h F : ℂ → ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, (starRingEnd ℂ) (F (γ t)) * h (γ t)

/-- **`boundaryForm` as a signed sum of four edge contributions.** Unfolds the definition; the four
edges of `∂box` are the images of `t ↦ wCLM (t,0)`, `wCLM (1,·)`, `wCLM (·,1)`, `wCLM (0,·)`. -/
lemma boundaryForm_eq_edges (h F : ℂ → ℂ) :
    boundaryForm h F
      = (edgeBF (fun t => wCLM (t, 0)) h F + Complex.I * edgeBF (fun t => wCLM (1, t)) h F)
        - edgeBF (fun t => wCLM (t, 1)) h F - Complex.I * edgeBF (fun t => wCLM (0, t)) h F := by
  rfl

/-- **Bilinearity of `boundaryForm`** over the combinations `h_v = ∑ⱼ vⱼ·hⱼ`, `F_v = ∑ᵢ vᵢ·Fᵢ`:
`boundaryForm (h_v) (F_v) = ∑ᵢ ∑ⱼ conj(vᵢ)·vⱼ · boundaryForm (hⱼ) (Fᵢ)`. (`boundaryForm` is ℂ-linear
in its first argument and conjugate-linear in its second, via interval-integral linearity.) -/
lemma boundaryForm_combo (v : Fin g → ℂ) (h F : Fin g → ℂ → ℂ)
    (hcont : ∀ i, ContinuousOn (h i) (wCLM '' (Icc 0 1 ×ˢ Icc 0 1)))
    (hcontF : ∀ i, ContinuousOn (F i) (wCLM '' (Icc 0 1 ×ˢ Icc 0 1))) :
    boundaryForm (fun z => ∑ j, v j * h j z) (fun z => ∑ i, v i * F i z)
      = ∑ i, ∑ j, (starRingEnd ℂ) (v i) * v j * boundaryForm (h j) (F i) := by
  sorry

/-- **Riemann's second bilinear relation (positive-definiteness), from the boundary word.**
Given period blocks `A, B`, holomorphic pullbacks `h_j` on a convex open `U ⊇ [0,1]²` with primitives
`F_i`, the per-entry boundary word `(Aᵀ·B̄ − Bᵀ·Ā)_{ij} = −boundaryForm (h_j) (F_i)`, and
non-degeneracy of the pullbacks, the period Hermitian form `i·(Aᵀ·B̄ − Bᵀ·Ā)` is positive definite.

(Hermitian-ness is automatic from the structure of the form; positivity is the Green-positivity
`∬_box ‖h_v‖² > 0`. Sign validated at `g = 1` → `2·Im τ > 0`.) -/
theorem riemann_R2_posDef_of_boundaryWord
    (A B : Matrix (Fin g) (Fin g) ℂ) (h F : Fin g → ℂ → ℂ) (U : Set ℂ)
    (hbox : wCLM '' (Icc 0 1 ×ˢ Icc 0 1) ⊆ U)
    (hh : ∀ i, ∀ z ∈ U, HasDerivAt (h i) (deriv (h i) z) z)
    (hF : ∀ i, ∀ z ∈ U, HasDerivAt (F i) (h i z) z)
    (boundaryWord : ∀ i j,
      (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ)) i j
        = - boundaryForm (h j) (F i))
    (nondeg : ∀ v : Fin g → ℂ, v ≠ 0 →
      ∃ p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1, (∑ j, v j * h j (wCLM p)) ≠ 0) :
    (Complex.I • (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ))).PosDef := by
  sorry

end Jacobians
