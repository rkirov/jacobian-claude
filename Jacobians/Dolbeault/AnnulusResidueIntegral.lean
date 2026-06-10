/-
  The annulus residue integral (Forster (10.21), planar form; Route-H atom 2).

  For a cutoff `χ` that is `≡ 1` near `c` and compactly supported inside a punctured-holomorphy
  ball of a meromorphic `m`, the Forster (10.21) identity computes the area integral of
  `∂̄(χ·m)` — a smooth, annulus-supported integrand (no singular integrals anywhere) — as a
  *residue*:

    `∫_ℂ ∂̄(χ·m) = −π · Res_c m`            (`integral_dbar_cutoff_mul_eq_resAt`)

  with the repo conventions `DbarDisk.dbar = ½(∂ₓ + i∂_y)` and `resAt = (2πi)⁻¹∮` (so for
  `m = (·−c)⁻¹` the integral is exactly `−π`; see the sanity anchor at the bottom).
  Forster's `2πi·Res` shape differs by his use of the 2-form `dz̄∧dz = 2i·dA`:
  `(−π)·dA`-normalisation `= (2πi)/(2i)·(−1)`… i.e. this is the same identity.

  Proof layout (all complete, no sorries):
  * §1 extends `DbarDisk` with the Wirtinger calculus (`dbar_fun_mul` Leibniz, congruence,
    sums) — pointwise statements at points of real differentiability.
  * §2 computes `∂̄` of a *radial* cutoff `η(|w−c|²)`: `∂̄χ = η'(|z−c|²)·(z−c)` (the ½ in `∂̄`
    cancels the 2 from the squared modulus — polynomial-clean, no `‖·‖`-calculus).
  * §3 builds an explicit `C¹` radial profile from `Real.smoothTransition`.
  * §4 the single-term computation `∫ ∂̄(χ·(·−c)^{−k}) = −π·δ_{k,1}` in polar coordinates:
    angular integral `∮ e^{i(1−k)θ}dθ = 2π·δ_{k,1}` (FTC), radial integral `∫ rη'(r²)dr = −½`.
  * §5 cutoff independence: for two admissible cutoffs the difference `(χ₁−χ₂)·m` is `C¹` with
    compact support, so its `∂̄`-integral vanishes by the proven Forster (10.20) atom
    (`integral_dbar_eq_zero`, `PlanarCompactSupportStokes`).
  * §6 the principal-part split `m = negTail + G` (`exists_principalPart_meromorphicAt`) with a
    junk-repaired holomorphic complement `G`; the `G`-term again dies by (10.20).
  * §7 `resAt` of the same data (`resAt m c = Σ b_k δ_{k,1}`), and the assembled theorem.

  References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §10 (Lemma 10.20 and the
  computation (10.21)); Miranda §VIII.3 uses the same bump-times-principal-part integrand.
-/
import Mathlib
import Jacobians.DbarDisk
import Jacobians.Dolbeault.PlanarCompactSupportStokes
import Jacobians.Dolbeault.Residue
import Jacobians.Dolbeault.FormTracePrincipalPart

open Complex Metric MeasureTheory Filter Set Topology
open scoped Real

/-! ### §1 — Wirtinger calculus for `DbarDisk.dbar`

`dbar f z = ½(D1 + i·DI)` with `D = fderiv ℝ f z` is a fixed linear read-off of the real
Fréchet derivative, so it inherits congruence/linearity/Leibniz from `fderiv ℝ` pointwise. -/

namespace DbarDisk

/-- `∂̄` only depends on the germ: functions agreeing near `z` have equal `∂̄` at `z`. -/
theorem dbar_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dbar f z = dbar g z := by
  unfold dbar
  rw [h.fderiv_eq]

/-- Additivity of `∂̄` at a common point of real differentiability. -/
theorem dbar_fun_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w + g w) z = dbar f z + dbar g z := by
  unfold dbar
  rw [fderiv_fun_add hf hg]
  simp only [ContinuousLinearMap.add_apply]
  ring

/-- Subtraction rule for `∂̄` at a common point of real differentiability. -/
theorem dbar_fun_sub {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w - g w) z = dbar f z - dbar g z := by
  unfold dbar
  rw [fderiv_fun_sub hf hg]
  simp only [ContinuousLinearMap.sub_apply]
  ring

/-- Finite sums commute with `∂̄` at a common point of real differentiability. -/
theorem dbar_fun_sum {ι : Type*} {s : Finset ι} {f : ι → ℂ → ℂ} {z : ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) z) :
    dbar (fun w => ∑ i ∈ s, f i w) z = ∑ i ∈ s, dbar (f i) z := by
  unfold dbar
  rw [fderiv_fun_sum hf]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]

/-- **Wirtinger–Leibniz product rule**: `∂̄(f·g) = f·∂̄g + g·∂̄f` at a common point of real
differentiability (`∂̄` is a derivation, like each directional `fderiv ℝ`). -/
theorem dbar_fun_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    dbar (fun w => f w * g w) z = f z * dbar g z + g z * dbar f z := by
  have h : HasFDerivAt (fun w => f w * g w) (f z • fderiv ℝ g z + g z • fderiv ℝ f z) z :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  unfold dbar
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Constants scale through `∂̄` at points of real differentiability. -/
theorem dbar_fun_const_mul (a : ℂ) {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) :
    dbar (fun w => a * f w) z = a * dbar f z := by
  rw [dbar_fun_mul (differentiableAt_const a) hf, dbar_const]
  ring

/-- `∂̄` of a `C¹` function is continuous at points of `C¹`-ness (local statement: only
`ContDiffAt ℝ 1` is assumed, which yields a neighbourhood on which `fderiv ℝ` is continuous). -/
theorem continuousAt_dbar_of_contDiffAt {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ 1 f z) :
    ContinuousAt (dbar f) z := by
  obtain ⟨u, hu_mem, hu⟩ := hf.contDiffOn le_rfl (by simp)
  obtain ⟨v, hvu, hv_open, hzv⟩ := _root_.mem_nhds_iff.mp hu_mem
  have h1 : ContinuousAt (fderiv ℝ f) z :=
    (((hu.mono hvu).continuousOn_fderiv_of_isOpen hv_open le_rfl).continuousAt
      (hv_open.mem_nhds hzv))
  exact continuousAt_const.mul ((h1.clm_apply continuousAt_const).add
    (continuousAt_const.mul (h1.clm_apply continuousAt_const)))

end DbarDisk

namespace Jacobians.Dolbeault

/-! ### §2 — `∂̄` of a radial profile of the squared modulus

For `χ(w) = η(normSq (w − c))` with `η : ℝ → ℝ` of class `C¹`,

  `∂̄χ(z) = η'(normSq (z−c)) · (z − c)`:

the `½` in `∂̄ = ½(∂ₓ + i∂_y)` exactly cancels the `2` from differentiating the squared
modulus, and `(∂ₓ + i∂_y)(x² + y²)/2 = x + iy`.  Using `normSq` (a polynomial in `re`/`im`)
avoids the `‖·‖`-at-zero pathology: the formula holds at **every** `z`, including `z = c`. -/

/-- The shifted squared modulus `w ↦ normSq (w − c)` is real-differentiable, with derivative
`v ↦ 2((z−c).re·v.re + (z−c).im·v.im)` (assembled from `reCLM`/`imCLM`). -/
theorem hasFDerivAt_normSq_sub (c z : ℂ) :
    HasFDerivAt (fun w : ℂ => Complex.normSq (w - c))
      ((z - c).re • (Complex.reCLM : ℂ →L[ℝ] ℝ) + (z - c).re • (Complex.reCLM : ℂ →L[ℝ] ℝ)
        + ((z - c).im • (Complex.imCLM : ℂ →L[ℝ] ℝ)
          + (z - c).im • (Complex.imCLM : ℂ →L[ℝ] ℝ))) z := by
  have hre : HasFDerivAt (fun w : ℂ => (w - c).re) (Complex.reCLM : ℂ →L[ℝ] ℝ) z := by
    have h := (Complex.reCLM.hasFDerivAt (x := z - c)).comp z (hasFDerivAt_sub_const c)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  have him : HasFDerivAt (fun w : ℂ => (w - c).im) (Complex.imCLM : ℂ →L[ℝ] ℝ) z := by
    have h := (Complex.imCLM.hasFDerivAt (x := z - c)).comp z (hasFDerivAt_sub_const c)
    rw [ContinuousLinearMap.comp_id] at h
    exact h
  refine HasFDerivAt.congr_of_eventuallyEq ((hre.mul hre).add (him.mul him)) ?_
  exact Filter.Eventually.of_forall fun w => by
    simp [Complex.normSq_apply]

/-- **`∂̄` of a complexified radial profile**: `∂̄(η ∘ normSq(·−c))(z) = η'(normSq(z−c))·(z−c)`.
Valid at every `z` (no puncture needed): `normSq` is polynomial. -/
theorem dbar_comp_normSq {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (c z : ℂ) :
    DbarDisk.dbar (fun w => (η (Complex.normSq (w - c)) : ℂ)) z
      = Complex.ofReal (deriv η (Complex.normSq (z - c))) * (z - c) := by
  have hη' : HasDerivAt η (deriv η (Complex.normSq (z - c))) (Complex.normSq (z - c)) :=
    ((hη.differentiable one_ne_zero) _).hasDerivAt
  have hcomp := hη'.comp_hasFDerivAt z (hasFDerivAt_normSq_sub c z)
  have hC : HasFDerivAt (fun w : ℂ => (η (Complex.normSq (w - c)) : ℂ))
      (Complex.ofRealCLM.comp (deriv η (Complex.normSq (z - c)) •
        ((z - c).re • (Complex.reCLM : ℂ →L[ℝ] ℝ) + (z - c).re • (Complex.reCLM : ℂ →L[ℝ] ℝ)
          + ((z - c).im • (Complex.imCLM : ℂ →L[ℝ] ℝ)
            + (z - c).im • (Complex.imCLM : ℂ →L[ℝ] ℝ))))) z :=
    Complex.ofRealCLM.hasFDerivAt.comp z hcomp
  rw [DbarDisk.dbar, hC.fderiv]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  linear_combination (Complex.ofReal (deriv η (Complex.normSq (z - c))))
    * (Complex.re_add_im (z - c))

/-- The radial profile is real-differentiable at every point (needed as a `DifferentiableAt ℝ`
input to the Leibniz rule). -/
theorem differentiableAt_comp_normSq {η : ℝ → ℝ} (hη : ContDiff ℝ 1 η) (c z : ℂ) :
    DifferentiableAt ℝ (fun w => (η (Complex.normSq (w - c)) : ℂ)) z := by
  have hη' : HasDerivAt η (deriv η (Complex.normSq (z - c))) (Complex.normSq (z - c)) :=
    ((hη.differentiable one_ne_zero) _).hasDerivAt
  exact (Complex.ofRealCLM.hasFDerivAt.comp z
    (hη'.comp_hasFDerivAt z (hasFDerivAt_normSq_sub c z))).differentiableAt

/-! ### §3 — an explicit `C¹` radial profile from `Real.smoothTransition` -/

/-- A `C¹` (indeed smooth) profile `η` with `η ≡ 1` on `(-∞, s₀]` and `η ≡ 0` on `[s₁, ∞)`.
Composed with `normSq(·−c)` this is the explicit radial cutoff used for the (10.21)
computation. -/
theorem exists_cutoff_profile {s₀ s₁ : ℝ} (h : s₀ < s₁) :
    ∃ η : ℝ → ℝ, ContDiff ℝ 1 η ∧ (∀ s ≤ s₀, η s = 1) ∧ (∀ s, s₁ ≤ s → η s = 0) := by
  refine ⟨fun s => Real.smoothTransition ((s₁ - s) / (s₁ - s₀)), ?_, ?_, ?_⟩
  · exact (Real.smoothTransition.contDiff (n := 1)).comp
      ((contDiff_const.sub contDiff_id).div_const _)
  · intro s hs
    exact Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).mpr (by linarith))
  · intro s hs
    exact Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

/-- The derivative of a profile that is constant `1` on `(-∞, s₀]` vanishes on the open ray
`(-∞, s₀)` (local constancy). -/
theorem deriv_profile_eq_zero_left {η : ℝ → ℝ} {s₀ : ℝ} (h1 : ∀ s ≤ s₀, η s = 1)
    {s : ℝ} (hs : s < s₀) : deriv η s = 0 := by
  have hev : η =ᶠ[𝓝 s] fun _ => 1 := by
    filter_upwards [Iio_mem_nhds hs] with t ht
    exact h1 t (le_of_lt ht)
  rw [hev.deriv_eq, deriv_const]

/-- The derivative of a profile that is constant `0` on `[s₁, ∞)` vanishes on the open ray
`(s₁, ∞)` (local constancy). -/
theorem deriv_profile_eq_zero_right {η : ℝ → ℝ} {s₁ : ℝ} (h0 : ∀ s, s₁ ≤ s → η s = 0)
    {s : ℝ} (hs : s₁ < s) : deriv η s = 0 := by
  have hev : η =ᶠ[𝓝 s] fun _ => 0 := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact h0 t (le_of_lt ht)
  rw [hev.deriv_eq, deriv_const]

/-! ### §4 — `resAt` of negative powers and of finite principal parts

Extensions of the `Residue.lean` API: residues of `(z−c)^{−k}` (`= δ_{k,1}`), closure of
`HoloPunctured` under sums, and `resAt` of a finite sum. -/

/-- `(w − c)^n` is holomorphic off `c`. -/
theorem differentiableAt_zpow_sub (c : ℂ) (n : ℤ) {z : ℂ} (hz : z ≠ c) :
    DifferentiableAt ℂ (fun w => (w - c) ^ n) z :=
  ((differentiableAt_zpow (m := n)).mpr (Or.inl (sub_ne_zero_of_ne hz))).comp z
    (differentiableAt_id.sub_const c)

/-- Scaled negative powers of `(· − c)` have isolated singularities at `c`. -/
theorem holoPunctured_const_mul_zpow (a c : ℂ) (n : ℤ) :
    HoloPunctured (fun z => a * (z - c) ^ n) c :=
  ⟨1, one_pos, fun _ hz =>
    (differentiableAt_zpow_sub c n (Set.mem_singleton_iff.not.mp hz.2)).const_mul a⟩

/-- `HoloPunctured` is closed under pointwise addition (intersect the two punctured balls). -/
theorem HoloPunctured.add {f g : ℂ → ℂ} {c : ℂ} (hf : HoloPunctured f c)
    (hg : HoloPunctured g c) : HoloPunctured (fun z => f z + g z) c := by
  obtain ⟨ρf, hρf, hf'⟩ := hf
  obtain ⟨ρg, hρg, hg'⟩ := hg
  refine ⟨min ρf ρg, lt_min hρf hρg, fun z hz => ?_⟩
  exact (hf' z ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_left _ _)), hz.2⟩).add
    (hg' z ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_right _ _)), hz.2⟩)

/-- `HoloPunctured` is closed under finite sums. -/
theorem holoPunctured_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ}
    (hf : ∀ i ∈ s, HoloPunctured (f i) c) :
    HoloPunctured (fun z => ∑ i ∈ s, f i z) c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, one_pos, fun z _ => ?_⟩
    simp only [Finset.sum_empty]
    exact differentiableAt_const (0 : ℂ)
  | insert a s ha ih =>
    have h := (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine h.imp fun ρ hρ => ⟨hρ.1, fun z hz => ?_⟩
    have := hρ.2 z hz
    simpa [Finset.sum_insert ha] using this

/-- **`resAt` of a finite sum** of functions with isolated singularities. -/
theorem resAt_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ}
    (hf : ∀ i ∈ s, HoloPunctured (f i) c) :
    resAt (fun z => ∑ i ∈ s, f i z) c = ∑ i ∈ s, resAt (f i) c := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact resAt_eq_zero_of_differentiableOn_ball one_pos fun z _ => differentiableAt_const 0
  | insert a s ha ih =>
    have hsum : HoloPunctured (fun z => ∑ i ∈ s, f i z) c :=
      holoPunctured_finset_sum s f fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hone : HoloPunctured (f a) c := hf a (Finset.mem_insert_self a s)
    have hadd := resAt_add hone hsum
    have hfun : (fun z => ∑ i ∈ insert a s, f i z)
        = fun z => f a z + ∑ i ∈ s, f i z := by
      funext z
      exact Finset.sum_insert ha
    rw [hfun, Finset.sum_insert ha, ← ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    exact hadd

/-- **`Res_c((·−c)^{−k}) = 0` for `k ≠ 1`** (all small contour integrals vanish:
`circleIntegral.integral_sub_zpow_of_ne`). -/
theorem resAt_zpow_neg_of_ne {c : ℂ} {k : ℕ} (hk : k ≠ 1) :
    resAt (fun z => (z - c) ^ (-(k : ℤ))) c = 0 := by
  have hn : (-(k : ℤ)) ≠ -1 := by
    intro h
    exact hk (by exact_mod_cast neg_inj.mp h)
  have h : ∀ᶠ r in 𝓝[>] (0 : ℝ), (∮ z in C(c, r), (z - c) ^ (-(k : ℤ))) = 0 :=
    Filter.Eventually.of_forall fun r => circleIntegral.integral_sub_zpow_of_ne hn c c r
  rw [resAt_eq_of_eventuallyEq_circleIntegral h, smul_zero]

/-- **`Res_c((·−c)^{−1}) = 1`** (the `zpow` phrasing of `resAt_sub_inv`). -/
theorem resAt_zpow_neg_one (c : ℂ) :
    resAt (fun z => (z - c) ^ (-(1 : ℕ) : ℤ)) c = 1 := by
  have hfun : (fun z : ℂ => (z - c) ^ (-(1 : ℕ) : ℤ)) = fun z => (z - c)⁻¹ := by
    funext z
    norm_num
  rw [hfun, resAt_sub_inv]

/-- **`resAt` of a single principal-part term**: `Res_c(b·(·−c)^{−k}) = b·δ_{k,1}`. -/
theorem resAt_const_mul_zpow_neg (b c : ℂ) (k : ℕ) :
    resAt (fun z => b * (z - c) ^ (-(k : ℤ))) c = b * (if k = 1 then 1 else 0) := by
  have hsmul : (fun z => b * (z - c) ^ (-(k : ℤ)))
      = b • fun z : ℂ => (z - c) ^ (-(k : ℤ)) := rfl
  rw [hsmul, resAt_smul b ⟨1, one_pos, fun _ hz =>
    differentiableAt_zpow_sub c _ (Set.mem_singleton_iff.not.mp hz.2)⟩]
  by_cases hk : k = 1
  · subst hk
    rw [resAt_zpow_neg_one, if_pos rfl, smul_eq_mul]
  · rw [resAt_zpow_neg_of_ne hk, if_neg hk]
    simp

end Jacobians.Dolbeault
