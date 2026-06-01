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

/-- The Cauchy-transform kernel `K ζ = 1/(π·ζ)`, so that the convolution
`u(z) = (g ⋆ K)(z) = (1/π)∬ g(ζ)/(z-ζ) dA(ζ)` satisfies `∂̄u = g` (Cauchy–Pompeiu, with this
sign convention; see `cauchyPompeiu` / `dbar_cauchyTransform`). -/
noncomputable def cauchyKernel (ζ : ℂ) : ℂ := 1 / (π * ζ)

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
  have : cauchyKernel = fun ζ : ℂ => ((1 / π) : ℂ) • ζ⁻¹ := by
    funext ζ; simp only [cauchyKernel, smul_eq_mul, one_div, mul_inv]
  rw [this]
  exact hinv.smul ((1 / π) : ℂ)

/-! ## D1 — regularity of the Cauchy transform, derivative onto the smooth factor

For `g ∈ C^∞_c`, the Cauchy transform `u = g ⋆ K` (with the kernel `K`) is `C^∞`, and its
Fréchet derivative is the convolution of `fderiv g` against `K`.  The derivative transfers to
the *smooth* factor `g`, so the rough kernel `K` is never differentiated; we need only
`LocallyIntegrable K` (D0).  We use `L = ContinuousLinearMap.mul ℝ ℂ` (complex multiplication
as an `ℝ`-bilinear map), so `(g ⋆[L] K) x = ∫ t, g t * K (x - t)`. -/

open scoped Convolution in
/-- The Cauchy transform of `g`: `u = g ⋆ K` with `K` the Cauchy kernel, computed against
complex multiplication.  Pointwise `u(x) = ∫ g(t)·K(x−t) dt = -(1/π)∬ g(ζ)/(x−ζ) dA(ζ)`. -/
noncomputable def cauchyTransform (g : ℂ → ℂ) : ℂ → ℂ :=
  g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] cauchyKernel

open scoped Convolution in
/-- **D1 (regularity).** For `g ∈ C^∞_c`, the Cauchy transform `u = g ⋆ K` is `C^∞`. -/
theorem contDiff_cauchyTransform {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g) : ContDiff ℝ (⊤ : ℕ∞) (cauchyTransform g) :=
  hgsupp.contDiff_convolution_left _ hg locallyIntegrable_cauchyKernel

open scoped Convolution in
/-- **D1 (derivative).** For `g ∈ C^∞_c`, the Fréchet derivative of `u = g ⋆ K` is
`(fderiv ℝ g) ⋆ K` (with the precomposed bilinear map), evaluated at each point. -/
theorem hasFDerivAt_cauchyTransform {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g) (x : ℂ) :
    HasFDerivAt (cauchyTransform g)
      (((fderiv ℝ g) ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompL ℂ, volume] cauchyKernel) x) x :=
  hgsupp.hasFDerivAt_convolution_left _ (hg.of_le (by exact_mod_cast le_top))
    locallyIntegrable_cauchyKernel x

open scoped Convolution in
/-- **D3 bridge.** `∂̄` commutes through the Cauchy transform onto the *smooth* factor:
`∂̄(g ⋆ K) = (∂̄g) ⋆ K`.  Combined with D1's derivative formula and the fact that the
evaluation maps `T ↦ T 1`, `T ↦ T I` (and hence `dbar`) commute with the Bochner integral. -/
theorem dbar_cauchyTransform {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g) (z : ℂ) :
    dbar (cauchyTransform g) z = (dbar g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] cauchyKernel) z := by
  set L := ContinuousLinearMap.mul ℝ ℂ
  -- The CLM-valued convolution integrand (D1's derivative) is integrable: `fderiv g` is
  -- continuous with compact support, `K` is locally integrable.
  have hfd_supp : HasCompactSupport (fderiv ℝ g) := hgsupp.fderiv ℝ
  have hfd_cont : Continuous (fderiv ℝ g) :=
    (hg.continuous_fderiv (by norm_num))
  have hint : Integrable
      (fun t => (L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) volume :=
    hfd_supp.convolutionExists_left (L.precompL ℂ) hfd_cont locallyIntegrable_cauchyKernel z
  -- Integrability of the two scalar integrands (evaluations of the CLM integrand at `1`, `I`).
  have hi1 : Integrable
      (fun t => ((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) (1 : ℂ)) volume :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).integrable_comp hint
  have hiI : Integrable
      (fun t => ((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) Complex.I) volume :=
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).integrable_comp hint
  -- Pull `dbar` (an evaluation-at-`1`/`I` combination) through the convolution integral.
  rw [dbar, (hasFDerivAt_cauchyTransform hg hgsupp z).fderiv, convolution_def,
    ContinuousLinearMap.integral_apply hint, ContinuousLinearMap.integral_apply hint,
    convolution_def]
  -- Merge the two scalar integrals into one (linearity), then compare integrands pointwise.
  have hmul : (Complex.I * ∫ t, ((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) Complex.I)
      = ∫ t, Complex.I * ((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) Complex.I :=
    (integral_const_mul _ _).symm
  rw [hmul, ← integral_add hi1 (hiI.const_mul Complex.I)]
  have hhalf : (2⁻¹ : ℂ) * ∫ t, (((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) 1
        + Complex.I * ((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) Complex.I)
      = ∫ t, (2⁻¹ : ℂ) * (((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) 1
        + Complex.I * ((L.precompL ℂ) (fderiv ℝ g t) (cauchyKernel (z - t))) Complex.I) :=
    (integral_const_mul _ _).symm
  rw [hhalf]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.precompL_apply, L, ContinuousLinearMap.mul_apply', dbar]
  ring

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

/-! ## D2 — the fundamental-solution identity (Cauchy–Pompeiu)

The genuine content: for `g ∈ C^∞_c`, `(∂̄g) ⋆ K = g`, i.e. `∫ t, (∂̄g)(t)·K(z−t) dt = g(z)`.
With `K ζ = 1/(πζ)` this is the Cauchy–Pompeiu formula with NO boundary term (compact support
kills it).  Proof = the complex Green / divergence theorem applied to `ζ ↦ g(ζ)/(ζ−z)` on the
annulus `ε ≤ |ζ−z| ≤ R`: the outer boundary vanishes by support, the inner circle tends to
`2πi·g(z)` as `ε→0` (the residue brick), and the area integral converges by D0. -/

/-- `dbar g` is continuous when `g` is `C^∞` (it is a fixed continuous-linear combination of the
first Fréchet derivative, which is itself continuous). -/
theorem continuous_dbar {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) : Continuous (dbar g) := by
  have hfd : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  unfold dbar
  fun_prop

/-- `dbar g` has compact support when `g` does (`dbar` is built from `fderiv g`, whose support
is contained in `tsupport g`). -/
theorem hasCompactSupport_dbar {g : ℂ → ℂ}
    (hgsupp : HasCompactSupport g) : HasCompactSupport (dbar g) := by
  apply HasCompactSupport.intro (hgsupp.fderiv ℝ).isCompact
  intro z hz
  have : fderiv ℝ g z = 0 := image_eq_zero_of_notMem_tsupport hz
  simp [dbar, this]

open scoped Convolution in
/-- Integrability of the area integrand `ζ ↦ (∂̄g)(ζ)·K(z−ζ)`: `∂̄g` is continuous with compact
support and `K(z−·)` is locally integrable (a reflection/translation of the kernel `K`). -/
theorem integrable_dbar_mul_cauchyKernel {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgsupp : HasCompactSupport g) (z : ℂ) :
    Integrable (fun ζ => dbar g ζ * cauchyKernel (z - ζ)) volume := by
  have h := (hasCompactSupport_dbar hgsupp).convolutionExists_left (ContinuousLinearMap.mul ℝ ℂ)
    (continuous_dbar hg) locallyIntegrable_cauchyKernel z
  simpa only [ContinuousLinearMap.mul_apply'] using h

/-- Evaluate the ℝ-linear map `fderiv ℝ g w` at a complex direction `a + b·I` in the `{1, I}`
basis: `(fderiv ℝ g w)(a + b·I) = a·(fderiv … 1) + b·(fderiv … I)` for real `a, b`. -/
theorem fderiv_apply_basis (g : ℂ → ℂ) (w : ℂ) (a b : ℝ) :
    (fderiv ℝ g w) (a + b * I) = (a : ℂ) * (fderiv ℝ g w) 1 + (b : ℂ) * (fderiv ℝ g w) I := by
  have h1 : ((a : ℂ) + b * I) = a • (1 : ℂ) + b • (I : ℂ) := by
    simp only [Complex.real_smul]; ring
  rw [h1, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

/-- **Polar–Wirtinger identity** (purely algebraic, from ℝ-linearity of `fderiv ℝ g`).
With `c = cos θ + sin θ·I = e^{iθ}`, the anti-radial Wirtinger derivative decomposes into the
radial (`fderiv … c`) and angular (`fderiv … (I·c)`) directional derivatives:
`e^{−iθ}·(2·∂̄g w) = (fderiv ℝ g w) c + I·(fderiv ℝ g w) (I·c)`. -/
theorem dbar_polar_identity (g : ℂ → ℂ) (w : ℂ) (θ : ℝ) :
    (Real.cos θ - Real.sin θ * I) * ((2 : ℂ) * dbar g w)
      = (fderiv ℝ g w) (Real.cos θ + Real.sin θ * I)
        + I * (fderiv ℝ g w) (I * (Real.cos θ + Real.sin θ * I)) := by
  set A := (fderiv ℝ g w) 1 with hA
  set B := (fderiv ℝ g w) I with hB
  -- The radial direction `c = cos θ + sin θ·I`.
  have hbasis : (fderiv ℝ g w) (Real.cos θ + Real.sin θ * I)
      = (Real.cos θ : ℂ) * A + (Real.sin θ : ℂ) * B := fderiv_apply_basis g w _ _
  -- The angular direction `I·c = -sin θ + cos θ·I`.
  have hIc : I * (Real.cos θ + Real.sin θ * I) = ((-Real.sin θ : ℝ) : ℂ) + (Real.cos θ : ℝ) * I := by
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hbasisI : (fderiv ℝ g w) (I * (Real.cos θ + Real.sin θ * I))
      = (-Real.sin θ : ℂ) * A + (Real.cos θ : ℂ) * B := by
    rw [hIc, fderiv_apply_basis g w _ _]; push_cast; ring
  rw [hbasis, hbasisI, dbar, ← hA, ← hB]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **D2 core — the Cauchy–Pompeiu area-integral identity.**  For `g ∈ C^∞_c`,
`∬_ℂ (∂̄g)(ζ)/(ζ−z) dA(ζ) = −π·g(z)`.

This is THE genuine mathematical content of the ∂̄-disk atom and the single remaining gap.

PLANNED PROOF — polar coordinates (NOT Green's theorem; this route avoids the unscaffolded
annulus-divergence theorem entirely):
1. Translate `ζ ↦ z + w` (`integral_add_left_eq_self`): `∫ (∂̄g)(ζ)/(ζ−z) = ∫ (∂̄g)(z+w)/w`.
2. Polar change of variables (`Complex.integral_comp_polarCoord_symm`): the Jacobian factor `r`
   cancels `1/w` (`r/(r e^{iθ}) = e^{−iθ}`), giving
   `∫_{(r,θ)∈(0,∞)×(−π,π)} e^{−iθ}·(∂̄g)(z + r e^{iθ}) dr dθ`.
3. The polar-Wirtinger identity `dbar_polar_identity` (PROVEN below): rewrites the integrand as
   `½(∂_r G + (i/r)∂_θ G)`, where `G(r,θ)=g(z+r e^{iθ})`.
4. The `∂_r` term integrates over `r∈(0,∞)` to `−g(z)` (1D FTC for compact support,
   `HasCompactSupport.integral_Ioi_deriv_eq`), then over `θ∈(−π,π)` to `−2π·g(z)`.
   The `∂_θ` term integrates over `θ` to `0` by periodicity (Fubini-swapped, the `1/r` weight is
   `θ`-independent).  Net `½·(−2π·g(z)) = −π·g(z)`.

REMAINING GAP: the Fubini/FTC assembly (step 4) wiring the proven polar-Wirtinger identity (step 3)
through the change-of-variables of steps 1–2.  ~120–200 LoC.  See the probe report. -/
theorem cauchyPompeiu_area {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (z : ℂ) : ∫ ζ, dbar g ζ / (ζ - z) = -π * g z := by
  sorry

open scoped Convolution in
/-- **D2 (Cauchy–Pompeiu).** For `g ∈ C^∞_c`, `(∂̄g) ⋆ K = g`.  Reduces by elementary algebra to
the area-integral identity `cauchyPompeiu_area`. -/
theorem cauchyPompeiu {g : ℂ → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g)
    (z : ℂ) : (dbar g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] cauchyKernel) z = g z := by
  -- Unfold the convolution and rewrite the kernel: `(∂̄g ⋆ K) z = ∫ (∂̄g ζ)·K(z−ζ)`.
  rw [convolution_def]
  simp only [ContinuousLinearMap.mul_apply', cauchyKernel]
  -- `K(z−ζ) = 1/(π(z−ζ)) = -(1/π)·(1/(ζ−z))`, so the integral is `-(1/π)·∫ (∂̄g ζ)/(ζ−z)`.
  have hker : ∀ ζ, dbar g ζ * (1 / (↑π * (z - ζ))) = (-(1 / ↑π)) * (dbar g ζ / (ζ - z)) := by
    intro ζ
    rcases eq_or_ne (ζ - z) 0 with h | h
    · have hzζ : z - ζ = 0 := by linear_combination -h
      simp [h, hzζ]
    · have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hzζ : z - ζ ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp h).symm
      field_simp
      ring
  have hfun : (fun ζ => dbar g ζ * (1 / (↑π * (z - ζ))))
      = (fun ζ => (-(1 / ↑π)) * (dbar g ζ / (ζ - z))) := funext hker
  rw [hfun]
  have hcm : ∫ ζ, (-(1 / ↑π)) * (dbar g ζ / (ζ - z))
      = (-(1 / ↑π)) * ∫ ζ, dbar g ζ / (ζ - z) := integral_const_mul _ _
  rw [hcm, cauchyPompeiu_area hg hgsupp z]
  field_simp

/-! ## D3 — assemble: the ∂̄-solvability atom -/

/-- **Main theorem (∂̄-on-a-disk solvability atom).** For `g ∈ C^∞_c(ℂ)`, the Cauchy transform
`u = g ⋆ K` is a `C^∞` solution of the inhomogeneous Cauchy–Riemann equation `∂̄u = g`
everywhere.  Combines D1 (regularity), the D3 bridge `∂̄(g⋆K) = (∂̄g)⋆K`, and D2 (Cauchy–Pompeiu
`(∂̄g)⋆K = g`). -/
theorem dbar_solvable_of_compactSupport {g : ℂ → ℂ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgsupp : HasCompactSupport g) :
    ∃ u : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) u ∧ ∀ z, dbar u z = g z := by
  refine ⟨cauchyTransform g, contDiff_cauchyTransform hg hgsupp, fun z => ?_⟩
  rw [dbar_cauchyTransform hg hgsupp z, cauchyPompeiu hg hgsupp z]

end DbarDisk
