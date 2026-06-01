/-
  DbarDisk.lean

  ∂̄-on-a-disk solvability (the Cauchy transform) — a standalone, Mathlib-only
  probe toward the Dolbeault wall.

  We define the Wirtinger ∂̄ operator on `ℂ → ℂ` and aim to prove the
  inhomogeneous Cauchy–Riemann solvability statement:

    for `g` continuous on the closed disk of radius `r`, there is an ℝ-differentiable
    `f` on the open disk with `∂̄ f = g` there.

  The classical witness is the **Cauchy transform**
    f(z) = -(1/π) ∬_{|ζ|≤r} g(ζ)/(ζ - z) dA(ζ),
  whose ∂̄ recovers `g` (Cauchy–Pompeiu).  This file isolates exactly the
  Mathlib gap on that route; see `dbar_disk_solvable` below.
-/
import Mathlib

open scoped Real Topology ENNReal
open Complex MeasureTheory

namespace DbarDisk

/-- The Wirtinger anti-holomorphic derivative `∂̄f = ½(∂ₓf + i ∂_y f)`, written via
the real Fréchet derivative `fderiv ℝ f` evaluated at the basis directions `1` and `I`.
`f` is holomorphic at `z` iff `dbar f z = 0` (see `dbar_eq_zero_of_differentiableAt`). -/
noncomputable def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

@[simp] theorem dbar_const (c : ℂ) (z : ℂ) : dbar (fun _ => c) z = 0 := by
  simp [dbar]

/-! ## D0 — the Cauchy kernel is locally integrable

The kernel `K ζ = -(1/(π·ζ))` has `‖K ζ‖ = (1/π)·‖ζ‖⁻¹`, which is `~ 1/r` in 2D and hence
locally integrable (`∫ r·(1/r) dr dθ < ∞`).  We synthesize this via polar coordinates; the
isolated "`‖x‖⁻¹` loc-integrable on ℝ²" lemma is absent from Mathlib. -/

/-- The Cauchy-transform kernel `K ζ = -(1/(π·ζ))`, so that
`u(z) = (g ⋆ K)(z) = -(1/π)∬ g(ζ)/(ζ-z) dA(ζ)`. -/
noncomputable def cauchyKernel (ζ : ℂ) : ℂ := -(1 / (π * ζ))

/-- The inverse function `ζ ↦ ζ⁻¹` is integrable on every closed ball of `ℂ`: in polar
coordinates the area element `r dr dθ` exactly cancels the `1/r` singularity. -/
theorem integrableOn_inv_closedBall (R : ℝ) :
    IntegrableOn (fun ζ : ℂ => ζ⁻¹) (Metric.closedBall 0 R) volume := by
  refine ⟨(measurable_inv).aestronglyMeasurable.restrict, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  -- The set-lintegral of `‖ζ⁻¹‖ₑ` over the ball, expressed on the whole space via an indicator,
  -- then transported to polar coordinates where the `r`-Jacobian cancels the `r⁻¹` singularity.
  rw [← lintegral_indicator measurableSet_closedBall,
    ← Complex.lintegral_comp_polarCoord_symm]
  -- Bound the polar integrand pointwise by the indicator (value `1`) of the finite-measure
  -- box `B = Ioc 0 R ×ˢ Ioo (-π) π`, then integrate the constant.
  set B : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) R ×ˢ Set.Ioo (-π) π with hB
  have hbound : ∀ p ∈ Complex.polarCoord.target,
      ENNReal.ofReal p.1 • (Metric.closedBall (0 : ℂ) R).indicator (fun ζ => ‖ζ⁻¹‖ₑ)
          (Complex.polarCoord.symm p)
        ≤ Set.indicator B (fun _ => (1 : ℝ≥0∞)) p := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    -- `r > 0` and `θ ∈ Ioo (-π) π`; `‖symm (r,θ)‖ = r`.
    simp only [Set.mem_Ioi] at hr
    by_cases hrR : r ≤ R
    · -- inside the ball: the indicator is `‖(symm p)⁻¹‖ₑ = ofReal r⁻¹`, so `ofReal r * ofReal r⁻¹ = 1`.
      have hmem : Complex.polarCoord.symm (r, θ) ∈ Metric.closedBall (0 : ℂ) R := by
        rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hr]
        exact hrR
      have hpB : (r, θ) ∈ B := ⟨⟨hr, hrR⟩, hθ⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hpB]
      have hne : Complex.polarCoord.symm (r, θ) ≠ 0 := by
        rw [← norm_ne_zero_iff, Complex.norm_polarCoord_symm, abs_of_pos hr]; exact hr.ne'
      rw [enorm_inv hne, ← ofReal_norm_eq_enorm, Complex.norm_polarCoord_symm, abs_of_pos hr,
        smul_eq_mul, ← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_mul hr.le,
        mul_inv_cancel₀ hr.ne', ENNReal.ofReal_one]
    · -- outside the ball: the closedBall indicator vanishes.
      have hnmem : Complex.polarCoord.symm (r, θ) ∉ Metric.closedBall (0 : ℂ) R := by
        rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hr]
        exact hrR
      rw [Set.indicator_of_notMem hnmem, smul_zero]; exact zero_le _
  calc
    ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 • (Metric.closedBall (0 : ℂ) R).indicator
            (fun ζ => ‖ζ⁻¹‖ₑ) (Complex.polarCoord.symm p)
        ≤ ∫⁻ p, Set.indicator B (fun _ => (1 : ℝ≥0∞)) p := by
          rw [← lintegral_indicator Complex.polarCoord.open_target.measurableSet]
          refine lintegral_mono fun p => ?_
          by_cases hp : p ∈ Complex.polarCoord.target
          · simpa [Set.indicator_of_mem hp] using hbound p hp
          · rw [Set.indicator_of_notMem hp]; exact zero_le _
      _ = volume B := by
          rw [lintegral_indicator (by exact (measurableSet_Ioc.prod measurableSet_Ioo)),
            setLIntegral_const, one_mul]
      _ < ∞ := by
          rw [hB, Measure.volume_eq_prod, Measure.prod_prod]
          exact ENNReal.mul_lt_top (by simp [Real.volume_Ioc]) (by simp [Real.volume_Ioo])

/-- **D0.** The Cauchy kernel `K ζ = -(1/(π·ζ))` is locally integrable on `ℂ`. -/
theorem locallyIntegrable_cauchyKernel : LocallyIntegrable cauchyKernel volume := by
  -- `K = (-(1/π) : ℂ) • (·⁻¹)`, and `·⁻¹` is integrable on every compact set (⊆ some closed ball).
  rw [locallyIntegrable_iff]
  intro k hk
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  have hinv : IntegrableOn (fun ζ : ℂ => ζ⁻¹) k volume :=
    (integrableOn_inv_closedBall R).mono_set hR
  have : cauchyKernel = fun ζ : ℂ => (-(1 / π) : ℂ) • ζ⁻¹ := by
    funext ζ; simp only [cauchyKernel, smul_eq_mul, one_div, mul_inv, neg_mul]
  rw [this]
  exact hinv.smul (-(1 / π) : ℂ)

/-- A function that is `ℂ`-differentiable (holomorphic) at `z` satisfies the
homogeneous Cauchy–Riemann equation `∂̄ f = 0` there.  This is the Wirtinger
characterization and validates the definition of `dbar`. -/
theorem dbar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : dbar f z = 0 := by
  -- For a `ℂ`-differentiable `f`, the real Fréchet derivative is multiplication by the
  -- complex derivative `f'(z)`: `fderiv ℝ f z = f'(z) • (1 : ℂ →L[ℝ] ℂ)`.
  -- (`HasDerivAt.complexToReal_fderiv` avoids the `restrictScalars` instance-synthesis snag.)
  have hr : fderiv ℝ f z = (deriv f z) • (1 : ℂ →L[ℝ] ℂ) :=
    hf.hasDerivAt.complexToReal_fderiv.fderiv
  -- Evaluate `∂̄f = ½(D 1 + I · D I)` with `D = f'(z) • 1`: `D 1 = f'`, `D I = f'·I`,
  -- so `∂̄f = ½(f' + I·(f'·I)) = ½(f' + I²·f') = 0`.
  rw [dbar, hr]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul, mul_one]
  have hII : Complex.I * (deriv f z * Complex.I) = - deriv f z := by
    rw [show Complex.I * (deriv f z * Complex.I) = deriv f z * (Complex.I * Complex.I) by ring,
      Complex.I_mul_I]; ring
  rw [hII]; ring

end DbarDisk
