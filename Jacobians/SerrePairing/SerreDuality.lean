import Mathlib.LinearAlgebra.FiniteDimensional.Defs

open Submodule Module

namespace Jacobians.Dolbeault.SerreDuality

/-- **Pigeonhole for subspaces.**  Two subspaces of a finite-dimensional space whose dimensions
sum to strictly more than the ambient dimension meet nontrivially.  The "pure linear algebra"
heart of Forster's §17.9 surjectivity step (`dim Λ + dim Im ι > dim H¹ ⟹ Λ ∩ Im ≠ 0`). -/
theorem subspaces_inf_ne_bot_of_finrank_add_gt
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Λ W : Submodule K V) (h : finrank K Λ + finrank K W > finrank K V) :
    Λ ⊓ W ≠ ⊥ := by
  intro hbot
  have key : finrank K ↥(Λ ⊔ W) + finrank K ↥(Λ ⊓ W) = finrank K Λ + finrank K W :=
    Submodule.finrank_sup_add_finrank_inf_eq Λ W
  rw [hbot, finrank_bot, Nat.add_zero] at key
  have hle : finrank K ↥(Λ ⊔ W) ≤ finrank K V := Submodule.finrank_le _
  omega

/-- **§17.9 surjectivity — abstract finite-dimensional core.**
Mirrors Forster's pigeonhole count.  For each `n`, `V n = H¹(𝒪_{D_n})*` is finite-dimensional with
two subspaces: `Λ n ≅ H⁰(𝒪_{nP})` with `dim ≥ 1 - g + n` (Lemma 17.8 + Riemann–Roch) and
`I n = Im ι_{D_n}` with `dim ≥ n + k₀ - deg D` (Lemmas 17.4/17.6).  Riemann–Roch gives
`dim (V n) = n + g - 1 - deg D` once `n > deg D`.  Then for all sufficiently large `n` the two
subspaces meet nontrivially — Forster's `Λ ∩ Im ι_{D_n} ≠ 0`, the surjectivity witness.

`g` (genus), `d = deg D`, `k₀` (the constant of Lemma 17.4) are arbitrary integers here; the result
is purely the linear-algebra/arithmetic skeleton, so it stays valid for whatever the geometric build
supplies. -/
theorem serre_surjectivity_dim_core
    {K : Type*} [Field K] {V : ℕ → Type*}
    [∀ n, AddCommGroup (V n)] [∀ n, Module K (V n)] [∀ n, FiniteDimensional K (V n)]
    (Λ I : ∀ n, Submodule K (V n)) (g d k₀ : ℤ)
    (hΛ : ∀ n : ℕ, (1 : ℤ) - g + n ≤ (finrank K (Λ n) : ℤ))
    (hI : ∀ n : ℕ, (n : ℤ) + k₀ - d ≤ (finrank K (I n) : ℤ))
    (hV : ∀ n : ℕ, d < n → ((finrank K (V n) : ℤ)) = n + g - 1 - d) :
    ∃ N : ℕ, ∀ n ≥ N, Λ n ⊓ I n ≠ ⊥ := by
  -- `n` must clear both `deg D` (for the RR formula `hV`) and `2g - 2 - k₀` (for the count
  -- to flip).
  set M : ℤ := max d (2 * g - 2 - k₀) with hM
  refine ⟨M.toNat + 1, fun n hn => ?_⟩
  have hself : M ≤ (M.toNat : ℤ) := Int.self_le_toNat M
  have hmd : d ≤ M := le_max_left _ _
  have hme : 2 * g - 2 - k₀ ≤ M := le_max_right _ _
  have hn' : (M.toNat : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
  have hdn : d < (n : ℤ) := by omega
  apply subspaces_inf_ne_bot_of_finrank_add_gt
  have hΛn := hΛ n
  have hIn := hI n
  have hVn := hV n hdn
  have : ((finrank K (V n) : ℤ)) < (finrank K (Λ n) : ℤ) + (finrank K (I n) : ℤ) := by omega
  exact_mod_cast this

/-- **§17.6 injectivity — abstract finite-dimensional core.**  An injective linear map from `V`
into the dual of a finite-dimensional `W` forces `dim V ≤ dim W`.  This is the linear-algebra
content of Forster's `ι_D` *injectivity* step: at `D = 0`, `ι₀ : H⁰(X,Ω) → H¹(X,𝒪)*` injective
gives `genus = dim H⁰(X,Ω) ≤ dim H¹(X,𝒪) = h1Dim 0` — the one-directional inequality.
Counterpart to `serre_surjectivity_dim_core` (which supplies the reverse inequality from
surjectivity). -/
theorem finrank_le_of_injective_to_dual
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (ι : V →ₗ[K] Module.Dual K W) (hι : Function.Injective ι) :
    finrank K V ≤ finrank K W :=
  (LinearMap.finrank_le_finrank_of_injective hι).trans_eq Subspace.dual_finrank_eq

end Jacobians.Dolbeault.SerreDuality
