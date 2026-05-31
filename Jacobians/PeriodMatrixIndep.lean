import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Analysis.Complex.Order

open Matrix
open scoped ComplexConjugate ComplexOrder

namespace Jacobians

variable {g : ℕ}

/-- **Riemann period independence.** Let `A B : Matrix (Fin g) (Fin g) ℂ` be the `a`-period and
`b`-period blocks (row = loop, column = holomorphic form). If
* (R1, vanishing) `Aᵀ * B = Bᵀ * A`, and
* (R2, positivity) the Hermitian matrix `H = (-I) • (Aᵀ * conj B - Bᵀ * conj A)` is positive
  definite,
then the `2g` period vectors (the rows of `fromRows A B`, indexed by `Fin g ⊕ Fin g`) are
ℝ-linearly independent in `Fin g → ℂ`. -/
theorem linearIndependent_periodRows_of_posDef
    (A B : Matrix (Fin g) (Fin g) ℂ)
    (H : Matrix (Fin g) (Fin g) ℂ)
    (hH : H = (-Complex.I) • (Aᵀ * B.map (starRingEnd ℂ) - Bᵀ * A.map (starRingEnd ℂ)))
    (hR1 : Aᵀ * B = Bᵀ * A)
    (hR2 : H.PosDef) :
    LinearIndependent ℝ (fun k : Fin g ⊕ Fin g => (Matrix.fromRows A B k : Fin g → ℂ)) := by
  classical
  -- Entrywise conjugates of `A` and `B`.
  set cA : Matrix (Fin g) (Fin g) ℂ := A.map (starRingEnd ℂ) with hcA
  set cB : Matrix (Fin g) (Fin g) ℂ := B.map (starRingEnd ℂ) with hcB
  -- The doubled period matrix: first g columns are `M = fromRows A B`, last g columns are `conj M`.
  set N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ := Matrix.fromBlocks A cA B cB with hN
  -- The symplectic form.
  set J : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℂ := Matrix.fromBlocks 0 1 (-1) 0 with hJ
  -- The two antidiagonal blocks of `Nᵀ * J * N`.
  set K : Matrix (Fin g) (Fin g) ℂ := Aᵀ * cB - Bᵀ * cA with hK
  set L : Matrix (Fin g) (Fin g) ℂ := cAᵀ * B - cBᵀ * A with hL
  -- Transpose of N.
  have hNt : Nᵀ = Matrix.fromBlocks Aᵀ Bᵀ cAᵀ cBᵀ := by
    rw [hN, Matrix.fromBlocks_transpose]
  -- Nᵀ * J.
  have hNtJ : Nᵀ * J = Matrix.fromBlocks (-Bᵀ) Aᵀ (-cBᵀ) cAᵀ := by
    rw [hNt, hJ, Matrix.fromBlocks_multiply]
    simp
  -- Nᵀ * J * N is block-antidiagonal: `fromBlocks 0 K L 0`.
  have hNJN : Nᵀ * J * N = Matrix.fromBlocks 0 K L 0 := by
    rw [hNtJ, hN, Matrix.fromBlocks_multiply]
    congr 1
    · -- top-left: -Bᵀ*A + Aᵀ*B = 0 by R1.
      rw [hR1]; simp only [neg_mul]; abel
    · -- top-right = K.
      rw [hK]; simp only [neg_mul, sub_eq_add_neg]; abel
    · -- bottom-left = L.
      rw [hL]; simp only [neg_mul, sub_eq_add_neg]; abel
    · -- bottom-right: -cBᵀ*cA + cAᵀ*cB = conj(Aᵀ*B - Bᵀ*A) = 0.
      have e1 : cAᵀ * cB = (Aᵀ * B).map (starRingEnd ℂ) := by
        rw [hcA, hcB, ← Matrix.transpose_map, ← Matrix.map_mul]
      have e2 : cBᵀ * cA = (Bᵀ * A).map (starRingEnd ℂ) := by
        rw [hcA, hcB, ← Matrix.transpose_map, ← Matrix.map_mul]
      simp only [neg_mul]
      rw [e1, e2, hR1]
      abel
  -- Step 4: K and L have nonzero determinant.
  -- K = I • H.
  have hKIH : K = Complex.I • H := by
    rw [hH, smul_smul]
    rw [show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I, neg_neg]]
    rw [one_smul]
  have hHdet : H.det ≠ 0 := ne_of_gt hR2.det_pos
  have hKdet : K.det ≠ 0 := by
    rw [hKIH, Matrix.det_smul, Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) hHdet
  -- L = -Kᵀ.
  have hLt : Lᵀ = -K := by
    rw [hL, hK, Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose, Matrix.transpose_transpose]
    abel
  have hLeq : L = -Kᵀ := by
    rw [← Matrix.transpose_transpose L, hLt, Matrix.transpose_neg]
  have hLdet : L.det ≠ 0 := by
    rw [hLeq, Matrix.det_neg, Matrix.det_transpose, Fintype.card_fin]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hKdet
  sorry

end Jacobians
