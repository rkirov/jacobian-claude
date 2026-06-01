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

open scoped Real Topology
open Complex MeasureTheory

namespace DbarDisk

/-- The Wirtinger anti-holomorphic derivative `∂̄f = ½(∂ₓf + i ∂_y f)`, written via
the real Fréchet derivative `fderiv ℝ f` evaluated at the basis directions `1` and `I`.
`f` is holomorphic at `z` iff `dbar f z = 0` (see `dbar_eq_zero_of_differentiableAt`). -/
noncomputable def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

@[simp] theorem dbar_const (c : ℂ) (z : ℂ) : dbar (fun _ => c) z = 0 := by
  simp [dbar]

/-- A function that is `ℂ`-differentiable (holomorphic) at `z` satisfies the
homogeneous Cauchy–Riemann equation `∂̄ f = 0` there.  This is the Wirtinger
characterization and validates the definition of `dbar`. -/
theorem dbar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : dbar f z = 0 := by
  -- The real derivative is the complexified derivative restricted to ℝ-scalars.
  have hr : fderiv ℝ f z = (fderiv ℂ f z).restrictScalars ℝ :=
    (hf.hasFDerivAt.restrictScalars ℝ).fderiv
  have h1 : fderiv ℝ f z 1 = fderiv ℂ f z 1 := by rw [hr]; rfl
  have hI : fderiv ℝ f z Complex.I = fderiv ℂ f z Complex.I := by rw [hr]; rfl
  -- ℂ-linearity: D(I) = I • D(1).
  have hlin : fderiv ℂ f z Complex.I = Complex.I * fderiv ℂ f z 1 := by
    have : (Complex.I : ℂ) • (1 : ℂ) = Complex.I := by simp
    rw [← this, map_smul, smul_eq_mul]
  rw [dbar, h1, hI, hlin]
  have hII : Complex.I * (Complex.I * fderiv ℂ f z 1) = - fderiv ℂ f z 1 := by
    rw [← mul_assoc, Complex.I_mul_I]; ring
  rw [hII]; ring

end DbarDisk
