/-
  Dolbeault ladder — **Forster 13.2**: `∂̄`-solvability on an *open* disk.

  This is the single missing analytic engine for the Čech finiteness node (see
  `docs/cech_refinement_attack_plan.md`).  The repo already has:

    * `DbarDisk.dbar_solvable_of_compactSupport` (Forster 13.1, Cauchy transform), and
    * `DbarDiskCohomology.dbar_solvable_ball` — solving `∂̄u = g` on a ball, but only for a
      **globally** smooth datum `g`.

  Forster 13.2 removes the global-smoothness requirement: it solves `∂̄u = g` on an open disk for a
  datum `g` smooth on the *open disk only*.  This is exactly what the genuine disk-acyclicity
  `H¹(disk, 𝒪) = 0` (Forster 13.4 — required by Leray's theorem 12.8) needs: there the datum is the
  glued `∂̄(smooth split)`, smooth on the union's chart-image ball but not globally, leaving no room
  for a cutoff bump.

  **Proof (Forster p.106, exhaustion).**  Exhaust `ball c R` by `ball c ρₙ`, `ρₙ ↑ R`.  Cutoffs `χₙ`
  (`= 1` on `closedBall c ρₙ`, supported in `ball c ρₙ₊₁ ⋐ ball c R`) make `χₙ·g` globally smooth with
  compact support, so 13.1 gives `fₙ` with `∂̄fₙ = χₙ·g = g` on `ball c ρₙ`.  Inductively correct
  `f̃ₙ` by a holomorphic polynomial `Pₙ` (Taylor partial sum of the holomorphic `fₙ₊₁ − f̃ₙ`) so that
  `‖f̃ₙ₊₁ − f̃ₙ‖ ≤ 2⁻ⁿ` on `closedBall c ρₙ`; the limit `u` converges locally uniformly, is smooth, and
  the holomorphic corrections preserve `∂̄u = g`.

  Mathlib ingredients (all confirmed present): `DifferentiableOn.hasFPowerSeriesOnBall`,
  `HasFPowerSeriesOnBall.tendstoUniformlyOn'` (partial sums = polynomials → `f` uniformly on
  subdisks), `TendstoLocallyUniformlyOn.differentiableOn` (locally-uniform limit of holomorphic is
  holomorphic), `ContDiffBump`.
-/
import Jacobians.Dolbeault.DbarDiskCohomology

open Complex Metric Filter Topology
open scoped NNReal ENNReal

namespace Jacobians.Dolbeault
namespace DbarOpenDisk

/-! ### Keystone lemmas (proven) -/

/-- Power-series partial sums (centred at `c`) are entire — they are polynomials. -/
theorem diff_partialSum (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) (c : ℂ) :
    Differentiable ℂ (fun y => p.partialSum n (y - c)) := by
  unfold FormalMultilinearSeries.partialSum
  apply Differentiable.fun_sum
  intro k _
  have hcmm : ContDiff ℂ (⊤ : ℕ∞) (p k) := (p k).contDiff
  exact (hcmm.differentiable (by norm_num)).comp (by fun_prop)

/-- **Runge/Taylor approximation on a closed subdisk.**  A function holomorphic on `ball c R'` is,
on any closed subdisk `closedBall c r` (`r < R'`), uniformly approximated to within `ε` by an *entire*
function (a Taylor partial sum). -/
theorem exists_holo_approx (φ : ℂ → ℂ) (c : ℂ) (R' : ℝ)
    (hφ : DifferentiableOn ℂ φ (ball c R')) (r : ℝ) (hr0 : 0 ≤ r) (hrR : r < R')
    (ε : ℝ) (hε : 0 < ε) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧ ∀ z ∈ closedBall c r, ‖φ z - P z‖ ≤ ε := by
  obtain ⟨s, hrs, hsR⟩ := exists_between hrR
  have hs0 : 0 < s := hr0.trans_lt hrs
  set R₀ : ℝ≥0 := s.toNNReal with hR₀
  have hR₀pos : 0 < R₀ := Real.toNNReal_pos.mpr hs0
  have hR₀coe : (R₀ : ℝ) = s := Real.coe_toNNReal s hs0.le
  have hsub : closedBall c (R₀ : ℝ) ⊆ ball c R' := by
    rw [hR₀coe]; exact closedBall_subset_ball hsR
  have hball := (hφ.mono hsub).hasFPowerSeriesOnBall hR₀pos
  set r' : ℝ≥0 := ((r + s) / 2).toNNReal with hr'
  have hr'coe : (r' : ℝ) = (r + s) / 2 := Real.coe_toNNReal _ (by positivity)
  have hr'lt : (r' : ℝ≥0∞) < (R₀ : ℝ≥0∞) := by
    rw [ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hr'coe, hR₀coe]; linarith
  have htu := hball.tendstoUniformlyOn' hr'lt
  rw [Metric.tendstoUniformlyOn_iff] at htu
  obtain ⟨N, hN⟩ := (htu ε hε).exists
  refine ⟨fun y => (cauchyPowerSeries φ c R₀).partialSum N (y - c), diff_partialSum _ _ _, ?_⟩
  intro z hz
  have hzin : z ∈ ball c (r' : ℝ) := by
    rw [mem_ball, hr'coe]; rw [mem_closedBall] at hz; linarith
  have := hN z hzin
  rw [dist_eq_norm] at this
  exact this.le

/-- **Cutoff × open-disk-smooth datum is globally smooth.**  If `g` is smooth on the open set `U`,
`ψ` is globally smooth, and `tsupport ψ ⊆ U`, then `ψ·g` is globally smooth (it is `ψ·g` on `U` and
`0` off `tsupport ψ`). -/
theorem contDiff_cutoff_mul {g ψ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g U) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsupp : tsupport ψ ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hψ.contDiffAt.mul (hg.contDiffAt (hU.mem_nhds hx))
  · have hxs : x ∉ tsupport ψ := fun h => hx (hsupp h)
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hxs] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]

/-- `∂̄` is subtractive at a point where both functions are real-differentiable. -/
theorem dbar_sub {f h : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z) :
    DbarDisk.dbar (fun x => f x - h x) z = DbarDisk.dbar f z - DbarDisk.dbar h z := by
  unfold DbarDisk.dbar
  rw [fderiv_fun_sub hf hh]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-! ### Exhaustion radii and the per-ball solve -/

/-- The exhaustion radii `ρₙ = R(1 − 2⁻⁽ⁿ⁺¹⁾) ↑ R`. -/
noncomputable def rho (R : ℝ) (n : ℕ) : ℝ := R * (1 - (1 / 2) ^ (n + 1))

/-- The exhaustion radii are positive, strictly increasing, bounded by `R`, and tend to `R`. -/
theorem rho_props {R : ℝ} (hR : 0 < R) :
    (∀ n, 0 < rho R n) ∧ StrictMono (rho R) ∧ (∀ n, rho R n < R) ∧
      Tendsto (rho R) atTop (nhds R) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    have h1 : (1 / 2 : ℝ) ^ (n + 1) < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    have : (0 : ℝ) < 1 - (1 / 2) ^ (n + 1) := by linarith
    rw [rho]; positivity
  · intro a b hab
    have : (1 / 2 : ℝ) ^ (b + 1) < (1 / 2) ^ (a + 1) :=
      pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by omega)
    simp only [rho]; nlinarith
  · intro n
    have h1 : (0 : ℝ) < (1 / 2) ^ (n + 1) := by positivity
    simp only [rho]; nlinarith
  · have h1 : Tendsto (fun n => (1 / 2 : ℝ) ^ (n + 1)) atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (tendsto_add_atTop_nat 1)
    have h2 := (tendsto_const_nhds (x := R)).mul ((tendsto_const_nhds (x := (1 : ℝ))).sub h1)
    have hrw : rho R = fun n => R * (1 - (1 / 2) ^ (n + 1)) := rfl
    rw [hrw]; simpa using h2

/-- **The per-ball solve.** With the open-disk datum `g`, solve `∂̄u = g` on `ball c a` for radii
`0 < a < b < R`: cut off `g` by a bump (`= 1` on `closedBall c a`, supported in `closedBall c b ⊆
ball c R`) so `χ·g` is globally smooth with compact support, then apply Forster 13.1. -/
theorem solve_on_ball (c : ℂ) {R : ℝ} {g : ℂ → ℂ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (ball c R))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hbR : b < R) :
    ∃ u : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) u ∧ ∀ z ∈ ball c a, DbarDisk.dbar u z = g z := by
  set χ : ContDiffBump c := { rIn := a, rOut := b, rIn_pos := ha, rIn_lt_rOut := hab } with hχ
  set χℂ : ℂ → ℂ := fun z => ((χ z : ℝ) : ℂ) with hχℂ
  obtain ⟨hχℂ_smooth, hχℂ_supp⟩ := DbarLocal.contDiff_hasCompactSupport_ofReal_contDiffBump χ
  have htsupp : tsupport χℂ ⊆ ball c R := by
    have h1 : tsupport χℂ ⊆ tsupport (fun z => (χ z : ℝ)) := by
      apply closure_mono; intro z hz
      simp only [Function.mem_support, hχℂ, ne_eq] at hz ⊢
      intro h0; exact hz (by rw [h0]; rfl)
    exact (χ.tsupport_eq ▸ h1).trans (closedBall_subset_ball hbR)
  have hG_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun z => χℂ z * g z) :=
    contDiff_cutoff_mul isOpen_ball hg hχℂ_smooth htsupp
  have hG_supp : HasCompactSupport (fun z => χℂ z * g z) := hχℂ_supp.mul_right
  obtain ⟨u, hu_smooth, hu_dbar⟩ := DbarDisk.dbar_solvable_of_compactSupport hG_smooth hG_supp
  refine ⟨u, hu_smooth, fun z hz => ?_⟩
  rw [hu_dbar z]
  show ((χ z : ℝ) : ℂ) * g z = g z
  rw [χ.one_of_mem_closedBall (ball_subset_closedBall hz)]
  simp only [Complex.ofReal_one, one_mul]

/-! ### Forster 13.2 — the main theorem -/

/-- **Forster 13.2 — `∂̄`-solvability on an open disk.**  For `g` smooth on the *open* ball
`ball c R`, there is `u` smooth on `ball c R` with `∂̄u = g` there.  Unlike
`DbarDiskCohomology.dbar_solvable_ball`, the datum need not be globally smooth — this is the version
required by genuine disk-acyclicity (Forster 13.4 / Leray 12.8). -/
theorem dbar_solvable_open_disk (c : ℂ) {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (ball c R)) :
    ∃ u : ℂ → ℂ, ContDiffOn ℝ (⊤ : ℕ∞) u (ball c R) ∧
      ∀ z ∈ ball c R, DbarDisk.dbar u z = g z := by
  sorry

end DbarOpenDisk
end Jacobians.Dolbeault
