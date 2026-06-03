/-
  The residue atom (Forster §17.1–17.2 building block).

  `resAt f c` is the residue of `f : ℂ → ℂ` at `c`, defined by the contour integral
  `(2πi)⁻¹ ∮_{|z-c|=r} f` in the limit `r → 0⁺`.  This is the upstream-most genuinely-new object the
  Čech-residue route to Serre duality (`docs/hodge_bridge_research.md` PHASE 0) rests on: every local
  residue `Res_a(ω)` of a meromorphic 1-form is, in a chart, `resAt (coeff of ω) (chart a)`.

  Mathlib has **no** residue / general Laurent-coefficient API (only `meromorphicTrailingCoeffAt`, the
  *leading* coefficient), so we build it on Mathlib's circle-integral + Cauchy–Goursat toolkit.

  This module is pure one-variable complex analysis — no manifold — and so is reusable verbatim in
  every chart.  The `limUnder (𝓝[>] 0)` shape mirrors the repo's `MeromorphicFunction.holoRepr`.

  Lemmas proved here (all sorry-free):
    * `resAt_eq_of_eventuallyEq_circleIntegral` — the workhorse: if the contour integral is eventually
      constant `= K` as `r → 0⁺`, then `resAt f c = (2πi)⁻¹ • K`.
    * `resAt_const_mul_sub_inv` / `resAt_sub_inv` — `Res_c (a/(z-c)) = a` (Forster 17.6's `dz/z` witness).
    * `resAt_eq_zero_of_differentiableOn_ball` — `Res_c(f) = 0` for `f` holomorphic near `c` (the
      holomorphic-difference property that makes `Res` well-defined on Mittag–Leffler cochains).
-/
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Metric Filter Topology
open scoped Real

namespace Jacobians.Dolbeault

/-- The **residue** of `f : ℂ → ℂ` at `c`: `(2πi)⁻¹ ∮_{|z-c|=r} f` in the limit `r → 0⁺`.
For `f` with an isolated singularity at `c` the contour integral is independent of small `r`
(annulus Cauchy–Goursat), so this picks out that common value = the Laurent coefficient `c₋₁`. -/
noncomputable def resAt (f : ℂ → ℂ) (c : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun r => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, r), f z)

/-- **Workhorse.** If the contour integral `∮_{|z-c|=r} f` is eventually constant `= K` as `r → 0⁺`,
then `resAt f c = (2πi)⁻¹ • K`.  Every residue computation below funnels through this. -/
theorem resAt_eq_of_eventuallyEq_circleIntegral {f : ℂ → ℂ} {c K : ℂ}
    (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), (∮ z in C(c, r), f z) = K) :
    resAt f c = (2 * π * I : ℂ)⁻¹ • K := by
  apply Filter.Tendsto.limUnder_eq
  refine (tendsto_const_nhds (x := (2 * π * I : ℂ)⁻¹ • K)).congr' ?_
  filter_upwards [h] with r hr
  rw [hr]

/-- If the contour integral is constant `= K` on a punctured right-neighbourhood `Ioo 0 ρ` of `0`,
the eventual-constancy hypothesis of the workhorse holds. -/
theorem eventuallyEq_circleIntegral_of_forall {f : ℂ → ℂ} {c K : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ∀ r ∈ Set.Ioo (0 : ℝ) ρ, (∮ z in C(c, r), f z) = K) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), (∮ z in C(c, r), f z) = K := by
  have hmem : Set.Ioo (0 : ℝ) ρ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hρ
  filter_upwards [hmem] with r hr using h r hr

/-- **Forster 17.6's witness, general coefficient.**  `Res_c (a·(z-c)⁻¹) = a`. -/
theorem resAt_const_mul_sub_inv (a c : ℂ) :
    resAt (fun z => a * (z - c)⁻¹) c = a := by
  have hcint : ∀ r ∈ Set.Ioo (0 : ℝ) 1,
      (∮ z in C(c, r), a * (z - c)⁻¹) = a * (2 * π * I) := by
    intro r hr
    rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_inv_of_mem_ball
      (mem_ball_self hr.1)]
  rw [resAt_eq_of_eventuallyEq_circleIntegral
    (eventuallyEq_circleIntegral_of_forall (by norm_num) hcint)]
  rw [smul_eq_mul, ← mul_assoc, mul_comm _ a, mul_assoc, inv_mul_cancel₀, mul_one]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-- `Res_c ((z-c)⁻¹) = 1`. -/
theorem resAt_sub_inv (c : ℂ) : resAt (fun z => (z - c)⁻¹) c = 1 := by
  have := resAt_const_mul_sub_inv 1 c
  simpa using this

/-- **Holomorphic-difference property.**  If `f` is complex-differentiable on a ball `ball c ρ`
(`ρ > 0`), its residue at `c` is `0`.  This is what makes `Res` well-defined on Mittag–Leffler
cochains: the differences `ωᵢ - ωⱼ` are holomorphic, hence contribute no residue. -/
theorem resAt_eq_zero_of_differentiableOn_ball {f : ℂ → ℂ} {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ∀ z ∈ ball c ρ, DifferentiableAt ℂ f z) :
    resAt f c = 0 := by
  have hcint : ∀ r ∈ Set.Ioo (0 : ℝ) ρ, (∮ z in C(c, r), f z) = 0 := by
    intro r hr
    refine circleIntegral_eq_zero_of_differentiable_on_off_countable hr.1.le Set.countable_empty
      ?_ (fun z hz => hf z ?_)
    · -- continuity on the closed ball of radius r ⊆ ball c ρ
      intro z hz
      exact (hf z (lt_of_le_of_lt (mem_closedBall.mp hz) hr.2)).continuousAt.continuousWithinAt
    · exact lt_of_lt_of_le (mem_ball.mp hz.1) hr.2.le
  rw [resAt_eq_of_eventuallyEq_circleIntegral
    (eventuallyEq_circleIntegral_of_forall hρ hcint), smul_zero]

end Jacobians.Dolbeault
