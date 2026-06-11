/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Abel engine C-2 (planar layer): the Forster 20.3 integration atoms on `ℂ`

The planar heart of Forster's Lemma 20.5 identity `∫_c ω = (1/2πi)∬(df/f)∧ω`.  This file
provides the Wirtinger `∂`-calculus (`del`, conjugate partner of the repo's `DbarDisk.dbar`)
and the two integration atoms the identity rests on:

  1. `integral_logDeriv_cross_eq_zero` — `∫_ℂ (∂W/W·∂̄G − ∂̄W/W·∂G) dA = 0` for smooth
     nonvanishing `W` and `G ∈ C_c^∞(ℂ)`: this is `∬ d(G·dW/W) = 0` in Wirtinger coordinates
     (compact-support Stokes `∫∂̄φ = ∫∂φ = 0`, `PlanarCompactSupportStokes`) plus the mixed
     Wirtinger commutation `∂̄∂W = ∂∂̄W` (`dbar_del_eq_del_dbar`, symmetry of the second
     Fréchet derivative);
  2. `integral_dbar_mul_inv_sub` — `∫_ℂ ∂̄G·((z−α)⁻¹ − (z−β)⁻¹) dA = π·(G β − G α)`
     (two applications of Cauchy–Pompeiu, `DbarDisk.cauchyPompeiu_area`).

These are exactly the "planar Stokes + residue" ingredients of Forster's proof of 20.3
(p. 160): the first kills the `dW/W` part of `df/f`, the second evaluates the two poles.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.3 (p. 160);
plan `docs/walls_bc_plan_2026-06-10.md`, phase C-2 (E2).
-/
import Jacobians.Dolbeault.AnnulusResidueIntegral

noncomputable section

-- ℂ-as-ℝ-module diamond discipline (as in `DbarOpenDisk`/`AnnulusResidueIntegral`).
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Complex Metric MeasureTheory Filter Set DbarDisk
open scoped Real Topology ContDiff

namespace Jacobians.AbelPlanar

/-! ### The Wirtinger holomorphic derivative `∂`

`DbarDisk.dbar` is the repo's `∂̄ = ½(∂ₓ + i∂_y)`; here we add its conjugate partner
`del = ∂ = ½(∂ₓ − i∂_y)` and the calculus the 20.3 Stokes argument needs. -/

/-- The Wirtinger holomorphic derivative `∂f = ½(∂ₓf − i·∂_yf)`, via the real Fréchet
derivative at the basis directions `1, I` (conjugate partner of `DbarDisk.dbar`). -/
def del (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I)

/-- `∂` only depends on the germ. -/
theorem del_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : del f z = del g z := by
  unfold del
  rw [h.fderiv_eq]

/-- **`∂` of a holomorphic function is its complex derivative** (the Wirtinger split of the
Cauchy–Riemann equations; companion of `dbar_eq_zero_of_differentiableAt`). -/
theorem del_eq_deriv_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : del f z = deriv f z := by
  have hr : fderiv ℝ f z = (deriv f z) • (1 : ℂ →L[ℝ] ℂ) :=
    hf.hasDerivAt.complexToReal_fderiv.fderiv
  rw [del, hr]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul,
    mul_one]
  have hII : Complex.I * (deriv f z * Complex.I) = - deriv f z := by
    rw [show Complex.I * (deriv f z * Complex.I) = deriv f z * (Complex.I * Complex.I) by ring,
      Complex.I_mul_I]; ring
  rw [hII]; ring

/-- **Wirtinger–Leibniz product rule for `∂`.** -/
theorem del_fun_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    del (fun w => f w * g w) z = f z * del g z + g z * del f z := by
  have h : HasFDerivAt (fun w => f w * g w) (f z • fderiv ℝ g z + g z • fderiv ℝ f z) z :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  unfold del
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `∂̄` of a pointwise inverse: `∂̄(f⁻¹) = −f⁻²·∂̄f` at points where `f ≠ 0`. -/
theorem dbar_fun_inv {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (h0 : f z ≠ 0) :
    dbar (fun w => (f w)⁻¹) z = -((f z) ^ 2)⁻¹ * dbar f z := by
  have hinv : HasDerivAt Inv.inv (-((f z) ^ 2)⁻¹) (f z) := hasDerivAt_inv h0
  have hcomp : HasFDerivAt (fun w => (f w)⁻¹)
      (((-((f z) ^ 2)⁻¹) • (1 : ℂ →L[ℝ] ℂ)).comp (fderiv ℝ f z)) z :=
    (hinv.complexToReal_fderiv).comp z hf.hasFDerivAt
  unfold dbar
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  ring

/-- `∂` of a pointwise inverse: `∂(f⁻¹) = −f⁻²·∂f` at points where `f ≠ 0`. -/
theorem del_fun_inv {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (h0 : f z ≠ 0) :
    del (fun w => (f w)⁻¹) z = -((f z) ^ 2)⁻¹ * del f z := by
  have hinv : HasDerivAt Inv.inv (-((f z) ^ 2)⁻¹) (f z) := hasDerivAt_inv h0
  have hcomp : HasFDerivAt (fun w => (f w)⁻¹)
      (((-((f z) ^ 2)⁻¹) • (1 : ℂ →L[ℝ] ℂ)).comp (fderiv ℝ f z)) z :=
    (hinv.complexToReal_fderiv).comp z hf.hasFDerivAt
  unfold del
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  ring

/-! ### Smoothness of the Wirtinger reads -/

/-- The directional Fréchet read `z ↦ (fderiv ℝ f z) v` of a `C^∞` function is `C^∞`. -/
theorem contDiff_fderiv_apply {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ f z v) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp h1

/-- `∂̄f` is `C^∞` for `C^∞` `f`. -/
theorem contDiff_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (dbar f) := by
  have h1 := contDiff_fderiv_apply hf 1
  have hI := contDiff_fderiv_apply hf Complex.I
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

/-- `∂f` is `C^∞` for `C^∞` `f`. -/
theorem contDiff_del {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (del f) := by
  have h1 := contDiff_fderiv_apply hf 1
  have hI := contDiff_fderiv_apply hf Complex.I
  exact contDiff_const.mul (h1.sub (contDiff_const.mul hI))

/-- `∂f` inherits compact support from `f` (companion of `hasCompactSupport_dbar`). -/
theorem hasCompactSupport_del {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (del f) := by
  apply HasCompactSupport.intro (hf.fderiv ℝ).isCompact
  intro z hz
  have : fderiv ℝ f z = 0 := image_eq_zero_of_notMem_tsupport hz
  simp [del, this]

/-! ### The mixed Wirtinger derivatives commute -/

/-- **`∂̄∂f = ∂∂̄f`** for `C^∞` `f` (symmetry of the second Fréchet derivative read in the
Wirtinger frame). -/
theorem dbar_del_eq_del_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    dbar (del f) z = del (dbar f) z := by
  -- the second derivative and its symmetry
  have hsymm : IsSymmSndFDerivAt ℝ f z := by
    have h2 : ContDiffAt ℝ 2 f z := hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    refine h2.isSymmSndFDerivAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
  have hf1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hD2 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf1.differentiable (by simp)).differentiableAt).hasFDerivAt
  set D2 : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := fderiv ℝ (fderiv ℝ f) z with hD2def
  -- Fréchet derivatives of the directional reads
  have hread : ∀ v : ℂ, HasFDerivAt (fun w => fderiv ℝ f w v)
      ((ContinuousLinearMap.apply ℝ ℂ v).comp D2) z :=
    fun v => (ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp z hD2
  -- Fréchet derivatives of `∂f` and `∂̄f`
  have hdel : HasFDerivAt (del f)
      ((2 : ℂ)⁻¹ • (((ContinuousLinearMap.apply ℝ ℂ 1).comp D2)
        - Complex.I • ((ContinuousLinearMap.apply ℝ ℂ Complex.I).comp D2))) z := by
    have h := ((hread 1).sub ((hread Complex.I).const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
    simpa [smul_smul, ContinuousLinearMap.smul_comp] using h
  have hdbar : HasFDerivAt (dbar f)
      ((2 : ℂ)⁻¹ • (((ContinuousLinearMap.apply ℝ ℂ 1).comp D2)
        + Complex.I • ((ContinuousLinearMap.apply ℝ ℂ Complex.I).comp D2))) z := by
    have h := ((hread 1).add ((hread Complex.I).const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
    simpa [smul_smul, ContinuousLinearMap.smul_comp] using h
  -- evaluate both sides in the `{1, I}` frame and use the symmetry `D2 u v = D2 v u`
  show (2 : ℂ)⁻¹ * (fderiv ℝ (del f) z 1 + Complex.I * fderiv ℝ (del f) z Complex.I)
      = (2 : ℂ)⁻¹ * (fderiv ℝ (dbar f) z 1 - Complex.I * fderiv ℝ (dbar f) z Complex.I)
  rw [hdel.fderiv, hdbar.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  have hsym1I : D2 1 Complex.I = D2 Complex.I 1 := hsymm.eq 1 Complex.I
  rw [hsym1I]
  ring

/-! ### Integration atom 1: the cross-term Stokes identity -/

/-- `∫_ℂ ∂φ = 0` for `C¹` compactly-supported `φ` (named-`del` form of
`Jacobians.Dolbeault.integral_del_eq_zero`). -/
theorem integral_del_eq_zero {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) : ∫ z, del φ z = 0 :=
  Jacobians.Dolbeault.integral_del_eq_zero φ hφ hsupp

/-- `∫_ℂ ∂̄φ = 0` for `C¹` compactly-supported `φ` (re-export of the
`PlanarCompactSupportStokes` atom in the `dbar` spelling). -/
theorem integral_dbar_eq_zero {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) : ∫ z, dbar φ z = 0 :=
  Jacobians.Dolbeault.integral_dbar_eq_zero φ hφ hsupp

/-- **The 20.3 cross-term Stokes identity**: for smooth nonvanishing `W` and `G ∈ C_c^∞(ℂ)`,

  `∫_ℂ (∂W/W·∂̄G − ∂̄W/W·∂G) dA = 0`.

This is `∬_ℂ d(G·dW/W) = 0` read in Wirtinger coordinates: expand `∫∂̄(G·∂W/W) = 0` and
`∫∂(G·∂̄W/W) = 0` (compact-support Stokes) and cancel the mixed second Wirtinger derivatives
of `W` (`dbar_del_eq_del_dbar`). -/
theorem integral_logDeriv_cross_eq_zero {W G : ℂ → ℂ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hW0 : ∀ z, W z ≠ 0)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGsupp : HasCompactSupport G) :
    ∫ z, (del W z / W z * dbar G z - dbar W z / W z * del G z) = 0 := by
  have hWd : Differentiable ℝ W := hW.differentiable (by simp)
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hdelW : ContDiff ℝ (⊤ : ℕ∞) (del W) := contDiff_del hW
  have hdbarW : ContDiff ℝ (⊤ : ℕ∞) (dbar W) := contDiff_dbar hW
  have hinvW : ContDiff ℝ (⊤ : ℕ∞) (fun z => (W z)⁻¹) :=
    contDiff_iff_contDiffAt.mpr fun z => (contDiffAt_inv ℝ (hW0 z)).comp z hW.contDiffAt
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun z => del W z / W z) := by
    simp only [div_eq_mul_inv]
    exact hdelW.mul hinvW
  have hU : ContDiff ℝ (⊤ : ℕ∞) (fun z => dbar W z / W z) := by
    simp only [div_eq_mul_inv]
    exact hdbarW.mul hinvW
  -- the two compactly-supported products
  set A : ℂ → ℂ := fun z => G z * (del W z / W z) with hAdef
  set B : ℂ → ℂ := fun z => G z * (dbar W z / W z) with hBdef
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := hG.mul hP
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hG.mul hU
  have hAsupp : HasCompactSupport A := hGsupp.mul_right
  have hBsupp : HasCompactSupport B := hGsupp.mul_right
  -- the two Stokes identities
  have h1 : ∫ z, dbar A z = 0 := integral_dbar_eq_zero (hA.of_le (by simp)) hAsupp
  have h2 : ∫ z, del B z = 0 := integral_del_eq_zero (hB.of_le (by simp)) hBsupp
  -- pointwise: `∂̄A − ∂B = ∂W/W·∂̄G − ∂̄W/W·∂G` (the `G·(∂̄(∂W/W) − ∂(∂̄W/W))` term cancels)
  have hpt : ∀ z, del W z / W z * dbar G z - dbar W z / W z * del G z
      = dbar A z - del B z := by
    intro z
    have hexpA : dbar A z = G z * dbar (fun w => del W w / W w) z
        + (del W z / W z) * dbar G z := by
      rw [hAdef]
      exact dbar_fun_mul hGd.differentiableAt (hP.differentiable (by simp)).differentiableAt
    have hexpB : del B z = G z * del (fun w => dbar W w / W w) z
        + (dbar W z / W z) * del G z := by
      rw [hBdef]
      exact del_fun_mul hGd.differentiableAt (hU.differentiable (by simp)).differentiableAt
    -- the mixed-derivative cancellation: `∂̄(∂W·W⁻¹) = ∂(∂̄W·W⁻¹)`
    have hmixed : dbar (fun w => del W w / W w) z = del (fun w => dbar W w / W w) z := by
      have hdelWd : DifferentiableAt ℝ (del W) z :=
        (hdelW.differentiable (by simp)).differentiableAt
      have hdbarWd : DifferentiableAt ℝ (dbar W) z :=
        (hdbarW.differentiable (by simp)).differentiableAt
      have hinvWd : DifferentiableAt ℝ (fun w => (W w)⁻¹) z :=
        (hinvW.differentiable (by simp)).differentiableAt
      have e1 : dbar (fun w => del W w / W w) z
          = del W z * dbar (fun w => (W w)⁻¹) z + (W z)⁻¹ * dbar (del W) z := by
        have h := dbar_fun_mul hdelWd hinvWd
        simpa only [div_eq_mul_inv] using h
      have e2 : del (fun w => dbar W w / W w) z
          = dbar W z * del (fun w => (W w)⁻¹) z + (W z)⁻¹ * del (dbar W) z := by
        have h := del_fun_mul hdbarWd hinvWd
        simpa only [div_eq_mul_inv] using h
      rw [e1, e2, dbar_fun_inv hWd.differentiableAt (hW0 z),
        del_fun_inv hWd.differentiableAt (hW0 z), dbar_del_eq_del_dbar hW z]
      ring
    rw [hexpA, hexpB, hmixed]
    ring
  -- assemble
  have hint1 : Integrable (fun z => dbar A z) volume :=
    (contDiff_dbar hA).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_dbar hAsupp)
  have hint2 : Integrable (fun z => del B z) volume :=
    (contDiff_del hB).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_del hBsupp)
  calc ∫ z, (del W z / W z * dbar G z - dbar W z / W z * del G z)
      = ∫ z, (dbar A z - del B z) := by
        exact integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫ z, dbar A z) - ∫ z, del B z := integral_sub hint1 hint2
    _ = 0 := by rw [h1, h2, sub_self]

/-! ### Integration atom 2: the two-pole Cauchy–Pompeiu pairing -/

/-- The pole pairing integrand `∂̄G·(z − a)⁻¹` is integrable for `G ∈ C_c^∞` (transport of
`DbarDisk.integrable_dbar_mul_cauchyKernel`). -/
theorem integrable_dbar_mul_inv {G : ℂ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGsupp : HasCompactSupport G) (a : ℂ) :
    Integrable (fun z => dbar G z * (z - a)⁻¹) volume := by
  have h := (integrable_dbar_mul_cauchyKernel hG hGsupp a).const_mul (-(π : ℂ))
  refine h.congr (Eventually.of_forall fun z => ?_)
  show -(π : ℂ) * (dbar G z * cauchyKernel (a - z)) = dbar G z * (z - a)⁻¹
  have hker : cauchyKernel (a - z) = 1 / ((π : ℂ) * (a - z)) := rfl
  rcases eq_or_ne z a with rfl | hz
  · rw [hker, sub_self]
    simp
  · have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have haz : a - z ≠ 0 := sub_ne_zero.mpr (fun h' => hz h'.symm)
    rw [hker]
    field_simp [sub_ne_zero.mpr hz]
    ring

/-- **The two-pole Cauchy–Pompeiu pairing** (the residue half of Forster 20.3):

  `∫_ℂ ∂̄G·((z−α)⁻¹ − (z−β)⁻¹) dA = π·(G β − G α)`   for `G ∈ C_c^∞(ℂ)`. -/
theorem integral_dbar_mul_inv_sub {G : ℂ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGsupp : HasCompactSupport G) (α β : ℂ) :
    ∫ z, dbar G z * ((z - α)⁻¹ - (z - β)⁻¹) = (π : ℂ) * (G β - G α) := by
  have hα := integrable_dbar_mul_inv hG hGsupp α
  have hβ := integrable_dbar_mul_inv hG hGsupp β
  have hsplit : ∫ z, dbar G z * ((z - α)⁻¹ - (z - β)⁻¹)
      = (∫ z, dbar G z * (z - α)⁻¹) - ∫ z, dbar G z * (z - β)⁻¹ := by
    rw [← integral_sub hα hβ]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  have hpomp : ∀ w : ℂ, ∫ z, dbar G z * (z - w)⁻¹ = -π * G w := by
    intro w
    have h := cauchyPompeiu_area hG hGsupp w
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun z =>
      (div_eq_mul_inv (dbar G z) (z - w)).symm)
  rw [hsplit, hpomp α, hpomp β]
  ring

end Jacobians.AbelPlanar
