/-
  The abstract Schwartz / Riesz–Schauder finiteness lemma (Forster *Lectures on Riemann Surfaces*
  Lemma 14.8) — the functional-analysis core of the `H¹(X, 𝒪_D)` finiteness theorem (14.9).

  Standalone (Banach-space functional analysis; no manifold / Čech dependency). Mathlib has the
  spectral Fredholm alternative (`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`) and Riesz's
  lemma but NOT this packaged "compact perturbation of a surjection has finite-codimensional image".
-/
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.FredholmAlternative
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Jacobians.SchwartzFiniteness

open Metric Filter Topology Finset

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Successive-approximation surjectivity.** If a continuous linear map `g : E →L[ℂ] G` between
Banach spaces admits, for every target `y`, an *approximate* preimage `x` within distance
`(1/2)‖y‖` and with norm `≤ C‖y‖`, then `g` is (exactly) surjective. This is the iterative second
half of the Banach open mapping theorem (`ContinuousLinearMap.exists_preimage_norm_le`), abstracted
so it can be applied to a small perturbation of a surjection. -/
theorem surjective_of_approx {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (g : E →L[ℂ] G) {C : ℝ}
    (h : ∀ y : G, ∃ x : E, dist (g x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) :
    Function.Surjective g := by
  choose f hdist hnorm using h
  intro y
  set r : G → G := fun y => y - g (f y) with hr
  have hrle : ∀ z, ‖r z‖ ≤ 1 / 2 * ‖z‖ := by
    intro z
    show ‖z - g (f z)‖ ≤ 1 / 2 * ‖z‖
    rw [← dist_eq_norm, dist_comm]
    exact hdist z
  have hrnle : ∀ n : ℕ, ‖r^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n IH =>
      rw [Function.iterate_succ']
      calc ‖r (r^[n] y)‖ ≤ 1 / 2 * ‖r^[n] y‖ := hrle _
        _ ≤ 1 / 2 * ((1 / 2) ^ n * ‖y‖) := by gcongr
        _ = (1 / 2) ^ (n + 1) * ‖y‖ := by ring
  set u : ℕ → E := fun n => f (r^[n] y) with hu
  have hunorm : ∀ n, ‖u n‖ ≤ (|C| * ‖y‖) * (1 / 2) ^ n := by
    intro n
    calc ‖u n‖ ≤ C * ‖r^[n] y‖ := hnorm _
      _ ≤ |C| * ‖r^[n] y‖ := mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
      _ ≤ |C| * ((1 / 2) ^ n * ‖y‖) := by gcongr; exact hrnle n
      _ = (|C| * ‖y‖) * (1 / 2) ^ n := by ring
  have hcauchy : CauchySeq (fun n => ∑ k ∈ range (n + 1), u k) :=
    NormedAddCommGroup.cauchy_series_of_le_geometric' (by norm_num : (1:ℝ)/2 < 1) hunorm
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨x, ?_⟩
  have hgu : ∀ k, g (u k) = r^[k] y - r^[k + 1] y := by
    intro k
    show g (f (r^[k] y)) = r^[k] y - r^[k + 1] y
    rw [Function.iterate_succ']
    show g (f (r^[k] y)) = r^[k] y - (r^[k] y - g (f (r^[k] y)))
    abel
  have hpartial : ∀ n, g (∑ k ∈ range (n + 1), u k) = y - r^[n + 1] y := by
    intro n
    rw [map_sum, Finset.sum_congr rfl (fun k _ => hgu k)]
    rw [Finset.sum_range_sub' (fun k => r^[k] y) (n + 1)]
    simp
  have hlim1 : Tendsto (fun n => g (∑ k ∈ range (n + 1), u k)) atTop (𝓝 (g x)) :=
    (g.continuous.tendsto x).comp hx
  have hr0 : Tendsto (fun n => r^[n + 1] y) atTop (𝓝 0) := by
    have htend : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1) * ‖y‖) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num : (1:ℝ)/2 < 1)).comp (tendsto_add_atTop_nat 1)
      simpa using this.mul_const ‖y‖
    exact squeeze_zero_norm (fun n => hrnle (n + 1)) htend
  have hlim2 : Tendsto (fun n => y - r^[n + 1] y) atTop (𝓝 (y - 0)) :=
    tendsto_const_nhds.sub hr0
  rw [sub_zero] at hlim2
  apply tendsto_nhds_unique hlim1
  simpa only [hpartial] using hlim2

/-- **Schwartz finiteness (Forster 14.8).** A compact perturbation of a surjection between Banach
spaces has finite-codimensional image: if `A : E →L[ℂ] F` is surjective and `K : E →L[ℂ] F` is a
compact operator, then `F ⧸ range (A + K)` is finite-dimensional. (`K = 0` ⟹ codim 0; `A = id` ⟹
Riesz–Schauder for `1 + K`.) This is the functional-analysis core of Forster 14.9. -/
theorem finiteDimensional_quotient_range_add_compact
    (A : E →L[ℂ] F) (hA : Function.Surjective A)
    (K : E →L[ℂ] F) (hK : IsCompactOperator K) :
    FiniteDimensional ℂ (F ⧸ LinearMap.range (A + K).toLinearMap) := by
  sorry

end Jacobians.SchwartzFiniteness
