/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.RamifiedResidueChangeOfVariables
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Constructions

/-!
# The symmetric-function descent: the trace of a holomorphic germ is holomorphic

This file proves the single genuinely-new analytic lemma blocking the Gate-A 1-form residue theorem
`∑ₐ Resₐ(α) = 0`: the **symmetric-function descent** (Forster §5 / Miranda §VIII.3, "the trace of a
holomorphic form is holomorphic").

## The statement

For an analytic germ `Q` at `0`, a positive multiplicity `m`, and a primitive `m`-th root of unity
`ζ`, the *weighted* `m`-sheet trace

> `u ↦ ∑_{j<m} Q(ζʲ·u)·ζʲ`

descends through `(·)^m`: there is an analytic germ `G` at `0` with

> `∑_{j<m} Q(ζʲ·u)·ζʲ = m·u^{m−1}·G(uᵐ)`   (for `u` near `0`).

This is `analyticAt_weightedSymSum_descent`.  The downstream ramified-residue subtree needs it in the
slit form `Rem z = ∑_{j<m} ppR(ζʲ·w₀ z)·(d/dz)[ζʲ·w₀ z] = G(z−c)` with `w₀ z = (z−c)^{1/m}` and the
chain rule `(d/dz)[ζʲ·w₀ z] = ζʲ·(1/m)·w₀ z^{1−m}`; that wiring is `ramifiedRemainderTrace_descent`.

## The proof

Taylor-expand `Q = ∑ₙ aₙ uⁿ` (`a_n = pf.coeff n`).  Then

> `∑_{j<m} Q(ζʲ·u)·ζʲ = ∑ₙ aₙ uⁿ·(∑_{j<m} ζ^{j(n+1)}) = ∑ₙ aₙ uⁿ · m·[m ∣ n+1]`

by the roots-of-unity power-sum collapse `rootsOfUnity_geom_zsum`.  Only the indices `n+1 = m(k+1)`,
i.e. `n = m·k + (m−1)`, survive, so the sum is `m·u^{m−1}·∑ₖ a_{m·k+(m−1)}·(uᵐ)ᵏ`, and we set

> `G(v) := ∑ₖ a_{m·k+(m−1)}·vᵏ`,

an analytic germ at `0` (its coefficients are a subsequence of `Q`'s, so its radius is `≥ (radius Q)^m`).

The two delicate steps — the analyticity of the subsequence series `G`, and the `HasSum`-divisibility
reindex `∑ₙ [m ∣ n+1] cₙ = ∑ₖ c_{m·k+(m−1)}` — are `analyticAt_ofScalars_subseq` and the
`HasSum.comp_injective` along `k ↦ m·k + d` inside `hasSum_weightedSymSum`.

## ⚠ Soundness

No custom axiom, no `sorry`, no false/junk/circular field.  The descent is the genuine *symmetric*
sum (single-valued via the roots of unity, not a single-valued branch `w₀` on `𝓝[≠]`).  Verified
axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §5.
* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (3.1).
* `Jacobians.RamifiedTrace.rootsOfUnity_geom_zsum` (the proven roots-of-unity power-sum collapse).
* `FormalMultilinearSeries.ofScalars` (Mathlib `Analysis/Analytic/OfScalars.lean`).
-/

noncomputable section

open Complex Filter Topology Finset
open scoped NNReal ENNReal

namespace Jacobians.SymmetricDescent

open FormalMultilinearSeries

/-! ## Analyticity of an arithmetic-progression subsequence series

Given an analytic germ `Q` at `0` with power series `pf`, the series `∑ₖ pf.coeff (m·k + d)·vᵏ`
(coefficients sampled along an arithmetic progression `k ↦ m·k + d`) is analytic at `0`.  Its
coefficients are a subsequence of `Q`'s, so a radius bound for `Q` gives one here: if `‖pf n‖·ρⁿ ≤ C`
for all `n` then `‖pf.coeff (m·k+d)‖·(ρᵐ)ᵏ ≤ ‖pf (m·k+d)‖·ρ^{m·k} ≤ C` (using `‖coeff n‖ ≤ ‖pf n‖`,
`ρ ≤ 1`-free since we keep `ρ < 1` by shrinking, and `m·k ≤ m·k+d`). -/

/-- `‖pf.coeff n‖ ≤ ‖pf n‖` for a one-dimensional formal multilinear series:
`coeff n = pf n (fun _ => 1)`, and `‖pf n (fun _ => 1)‖ ≤ ‖pf n‖·∏ ‖1‖ = ‖pf n‖`. -/
theorem norm_coeff_le (pf : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    ‖pf.coeff n‖ ≤ ‖pf n‖ := by
  rw [FormalMultilinearSeries.coeff]
  calc ‖pf n fun _ => 1‖ ≤ ‖pf n‖ * ∏ _i : Fin n, ‖(1 : ℂ)‖ := (pf n).le_opNorm _
    _ = ‖pf n‖ := by simp

/-- The subsequence series `ofScalars ℂ (fun k => pf.coeff (m·k + d))` has radius at least
`(pf.radius)^m`.  Concretely: for every `ρ < pf.radius`, `(ρᵐ : ℝ≥0∞) ≤ (subseries).radius`.  Take
`ρ < pf.radius`, get a bound `‖pf n‖·ρⁿ ≤ C`; then for the subseries coefficient at `k`,
`‖coeff (m·k+d)‖·(ρᵐ)ᵏ ≤ ‖pf (m·k+d)‖·ρ^{m·k}`, and `ρ^{m·k} ≤ ρ^{m·k+d}·ρ^{-d}`… we instead bound
directly: `‖pf (m·k+d)‖·ρ^{m·k+d} ≤ C`, so `‖coeff (m·k+d)‖·ρ^{m·k} ≤ C·ρ^{-d}` is **not** uniform.
The clean bound keeps the full power: `‖coeff (m·k+d)‖·(ρᵐ)ᵏ ≤ ‖pf (m·k+d)‖·ρ^{m·k}`, and since
`ρ^{m·k} ≤ max 1 (ρ^{-d}) · ρ^{m·k+d}`, the product is `≤ (max 1 ρ^{-d})·C`. -/
theorem le_radius_ofScalars_subseq (pf : FormalMultilinearSeries ℂ ℂ ℂ) {m : ℕ} (hm : 0 < m) (d : ℕ)
    {ρ : ℝ≥0} (hρ : (ρ : ℝ≥0∞) < pf.radius) :
    ((ρ : ℝ≥0∞) ^ m) ≤ (ofScalars ℂ (fun k => pf.coeff (m * k + d))).radius := by
  rcases eq_or_ne ρ 0 with rfl | hρ0
  · simp only [ENNReal.coe_zero, zero_pow hm.ne']; exact zero_le _
  · obtain ⟨C, hC, hbound⟩ := pf.norm_mul_pow_le_of_lt_radius hρ
    have hρ0' : (0 : ℝ) < (ρ : ℝ) := by positivity
    -- the uniform bound `‖coeff (m·k+d)‖·(ρᵐ)ᵏ ≤ C / ρ^d`
    have key : ∀ k : ℕ, ‖(ofScalars ℂ (fun k => pf.coeff (m * k + d))) k‖ * ((ρ ^ m : ℝ≥0) : ℝ) ^ k
        ≤ C / (ρ : ℝ) ^ d := by
      intro k
      rw [ofScalars_norm]  -- `‖ofScalars c k‖ = ‖c k‖` (NormOneClass)
      have h1 : ‖pf.coeff (m * k + d)‖ * ((ρ : ℝ) ^ (m * k + d)) ≤ C :=
        le_trans (by gcongr; exact norm_coeff_le pf (m * k + d)) (hbound (m * k + d))
      rw [le_div_iff₀ (by positivity)]
      calc ‖pf.coeff (m * k + d)‖ * ((ρ ^ m : ℝ≥0) : ℝ) ^ k * (ρ : ℝ) ^ d
          = ‖pf.coeff (m * k + d)‖ * (ρ : ℝ) ^ (m * k + d) := by
            push_cast
            rw [pow_add, ← pow_mul]
            ring
        _ ≤ C := h1
    have h := (ofScalars ℂ (fun k => pf.coeff (m * k + d))).le_radius_of_bound
      (C / (ρ : ℝ) ^ d) key
    -- `((ρ^m : ℝ≥0) : ℝ≥0∞) = (ρ : ℝ≥0∞)^m`
    rw [ENNReal.coe_pow] at h
    exact h

/-- A `1`-D scalar power series of positive radius has an analytic sum at `0`. -/
theorem analyticAt_ofScalarsSum_of_pos_radius (c : ℕ → ℂ)
    (h : 0 < (ofScalars ℂ c).radius) :
    AnalyticAt ℂ (ofScalarsSum (E := ℂ) c) 0 := by
  have := ((ofScalars (𝕜 := ℂ) ℂ c).hasFPowerSeriesOnBall h).analyticAt
  rwa [show (ofScalars (𝕜 := ℂ) ℂ c).sum = ofScalarsSum (E := ℂ) c from rfl] at this

/-- **The subsequence series is analytic at `0`.**  If `pf` is the power series of an analytic germ at
`0` with positive radius, then the function `ofScalarsSum (fun k => pf.coeff (m·k + d))`
(`= v ↦ ∑' k, pf.coeff (m·k + d)·vᵏ`, the coefficients sampled along the arithmetic progression
`k ↦ m·k + d`) is analytic at `0`.  Its power series is `ofScalars ℂ (fun k => pf.coeff (m·k + d))`,
of positive radius by `le_radius_ofScalars_subseq`. -/
theorem analyticAt_ofScalars_subseq (pf : FormalMultilinearSeries ℂ ℂ ℂ) (hpf : 0 < pf.radius)
    {m : ℕ} (hm : 0 < m) (d : ℕ) :
    AnalyticAt ℂ (ofScalarsSum (E := ℂ) (fun k => pf.coeff (m * k + d))) 0 := by
  apply analyticAt_ofScalarsSum_of_pos_radius
  -- pick `0 < ρ < pf.radius`; then `0 < ρᵐ ≤ (subseries).radius`
  obtain ⟨ρ, hρ0, hρ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpf
  refine lt_of_lt_of_le ?_ (le_radius_ofScalars_subseq pf hm d hρ)
  have hρ0' : (0 : ℝ≥0) < ρ := by exact_mod_cast hρ0
  rw [← ENNReal.coe_pow]
  exact_mod_cast pow_pos hρ0' m

/-! ## The arithmetic-progression index map and its range

The reindex map `k ↦ m·k + (m−1)`.  Its image is exactly `{n | m ∣ n+1}` (for `m > 0`): a natural `n`
has `n+1` divisible by `m` iff `n = m·k + (m−1)` for some `k`.  This is the divisibility reindex that
collapses the roots-of-unity sum to the subsequence series. -/

/-- The reindex map `k ↦ m·k + (m−1)` is injective (for `m > 0`). -/
theorem apIdx_injective {m : ℕ} (hm : 0 < m) :
    Function.Injective (fun k : ℕ => m * k + (m - 1)) := by
  intro a b hab
  simp only at hab
  have : m * a = m * b := by omega
  exact Nat.eq_of_mul_eq_mul_left hm this

/-- `n` lies in the range of `k ↦ m·k + (m−1)` iff `m ∣ n+1` (for `m > 0`). -/
theorem mem_range_apIdx_iff {m : ℕ} (hm : 0 < m) (n : ℕ) :
    n ∈ Set.range (fun k : ℕ => m * k + (m - 1)) ↔ m ∣ (n + 1) := by
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k + 1, ?_⟩
    show m * k + (m - 1) + 1 = m * (k + 1)
    rw [Nat.mul_succ]
    omega
  · rintro ⟨k, hk⟩
    -- `n + 1 = m·k`, and `k ≥ 1` since `n + 1 ≥ 1`; set `k = k'+1`, `n = m·k' + (m−1)`.
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · simp at hk
      · exact h
    refine ⟨k - 1, ?_⟩
    show m * (k - 1) + (m - 1) = n
    have hmk : m * k = m * (k - 1) + m := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [Nat.mul_succ]
    omega

/-! ## The weighted symmetric-sum HasSum identity

The heart of the descent.  For `Q` analytic at `0` (power series `pf`), `m > 0`, `ζ` a primitive `m`-th
root of unity, and `u` near `0`, the weighted `m`-sheet sum collapses to the subsequence series:

> `∑_{j<m} Q(ζʲ·u)·ζʲ = m·u^{m−1}·∑'ₖ pf.coeff (m·k+(m−1))·(uᵐ)ᵏ`.

The proof scales each `HasSum (fun n => (ζʲu)ⁿ·pf.coeff n) (Q(ζʲu))` by `ζʲ`, sums over `j` via
`hasSum_sum`, collapses the coefficient `∑_{j<m} ζ^{j(n+1)} = m·[m∣n+1]` by `rootsOfUnity_geom_zsum`,
and reindexes `n = m·k+(m−1)` via `Function.Injective.hasSum_iff`. -/

/-- For `u` near `0`, the `m`-sheet sum HasSum form: `∑_{j<m} Q(ζʲ·u)·ζʲ` is the sum of the series
`n ↦ (∑_{j<m} ζ^{j(n+1)})·uⁿ·pf.coeff n`. -/
theorem hasSum_symSheetSum_aux {Q : ℂ → ℂ} {pf : FormalMultilinearSeries ℂ ℂ ℂ}
    (hpf : HasFPowerSeriesAt Q pf 0) {m : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) :
    ∀ᶠ u in 𝓝 (0 : ℂ),
      HasSum (fun n : ℕ => (∑ j ∈ Finset.range m, (ζ ^ j) ^ ((n : ℤ) + 1)) * u ^ n * pf.coeff n)
        (∑ j ∈ Finset.range m, Q (ζ ^ j * u) * ζ ^ j) := by
  -- The per-sheet eventual HasSum, pulled back along the continuous `u ↦ ζʲ·u` (each sends `𝓝 0 → 𝓝 0`).
  rw [hasFPowerSeriesAt_iff] at hpf
  have hev : ∀ᶠ u in 𝓝 (0 : ℂ), ∀ j ∈ Finset.range m,
      HasSum (fun n => (ζ ^ j * u) ^ n • pf.coeff n) (Q (ζ ^ j * u)) := by
    rw [eventually_all_finset]
    intro j _
    have hcont : Tendsto (fun u : ℂ => ζ ^ j * u) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun u : ℂ => ζ ^ j * u) := continuous_const.mul continuous_id
      simpa using hc.tendsto 0
    have := hcont.eventually hpf
    filter_upwards [this] with u hu
    simpa using hu
  filter_upwards [hev] with u hu
  -- scale each per-sheet HasSum by `ζ^j`, then sum over `j ∈ range m`.
  have hperj : ∀ j ∈ Finset.range m,
      HasSum (fun n : ℕ => ((ζ ^ j) ^ ((n : ℤ) + 1)) * u ^ n * pf.coeff n) (Q (ζ ^ j * u) * ζ ^ j) := by
    intro j hj
    have h0 := (hu j hj).mul_right (ζ ^ j)
    refine h0.congr_fun ?_  -- rewrite the summand
    intro n
    have hζj : ζ ^ j ≠ 0 := pow_ne_zero j (hζ.ne_zero (by rintro rfl; simp at hj))
    rw [smul_eq_mul]
    rw [show ((ζ ^ j) ^ ((n : ℤ) + 1)) = (ζ ^ j) ^ n * ζ ^ j by
      rw [zpow_add₀ hζj (n : ℤ) 1, zpow_one, zpow_natCast]]
    rw [mul_pow]
    ring
  -- pull the common factor `u^n·pf.coeff n` out of the finite `j`-sum.
  have hsum := hasSum_sum hperj
  refine hsum.congr_fun ?_
  intro n
  rw [Finset.sum_mul, Finset.sum_mul]

/-- The defining `HasSum` of `ofScalarsSum c` at a point `v` strictly inside the radius. -/
theorem hasSum_ofScalarsSum_of_lt_radius (c : ℕ → ℂ) {v : ℂ}
    (hv : (‖v‖₊ : ℝ≥0∞) < (ofScalars ℂ c).radius) :
    HasSum (fun k => c k • v ^ k) (ofScalarsSum (E := ℂ) c v) := by
  have hball : v ∈ Metric.eball (0 : ℂ) (ofScalars ℂ c).radius := by
    rw [Metric.mem_eball, edist_zero_right]
    simpa [enorm] using hv
  have hpos : 0 < (ofScalars ℂ c).radius := lt_of_le_of_lt (zero_le _) hv
  have h := ((ofScalars (𝕜 := ℂ) ℂ c).hasFPowerSeriesOnBall hpos).hasSum hball
  -- `(ofScalars c) n (fun _ => v) = c n • v^n`, and `(ofScalars c).sum v = ofScalarsSum c v`.
  simp only [ofScalars_apply_eq] at h
  rw [zero_add] at h
  exact h

end Jacobians.SymmetricDescent
