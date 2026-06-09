/-
  Forster §17.4 — the canonical meromorphic 1-form `ω₀ = df` and its canonical divisor `K = div ω₀`,
  instantiating `CanonicalForm17Data X` (which makes the already-proven §17.4 isomorphism
  `omega17Equiv : L(D+K) ≃ₗ[ℂ] Ω_D` of `CanonicalFormIso` unconditional).

  ## The construction (Forster GTM 81, §17.4: `ω = df`)

  Fix the nonconstant meromorphic function `f` of `exists_nonconstant_meromorphic`
  (`Jacobians.Dolbeault.SerreOmega0`).  Its **differential**

      `df.toFun x := mfderiv 𝓘(ℂ) 𝓘(ℂ) f x`

  is a section of the cotangent bundle (`TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ`); it is the genuine intrinsic
  differential (the *junk-value* defect — `mfderiv` is `0` where `f` is not `MDifferentiableAt`, i.e.
  at poles — is invisible to the germ object `MeromorphicOneForm`, which only cares that `formCoeff`
  is `MeromorphicAt`).

  The keystone identity (`mfderiv_apply_symmL_eq_deriv`) is, in the chart at `x`,

      `mfderiv f y (symmL y 1) = (f ∘ chart⁻¹)' (chart y)`        (`y` regular, in chart source)

  so the chart coefficient `formCoeff (df) x` agrees, on a punctured neighbourhood of `chart x x`,
  with `(f ∘ chart⁻¹)'`, which is `MeromorphicAt` (`MeromorphicAt.deriv`).  Hence `df` is a genuine
  `MeromorphicOneForm`.

  Sanity check (Forster): `f(z) = z` ⟹ `df = dz`, `K = 0`.

  Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.4; Mathlib `mfderiv`,
  `MeromorphicAt.deriv`, `TangentBundle.symmL_trivializationAt`, `mdifferentiableAt_iff_of_mem_source`.
-/
import Jacobians.Dolbeault.CanonicalFormIso
import Jacobians.Dolbeault.SerreOmega0

open scoped Manifold ContDiff Topology Bundle
open Module

namespace Jacobians.Dolbeault

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 1: the two intrinsic-differential bridges

`mfderiv f` paired with the spanning tangent vector `symmL 1` of the canonical trivialization reads,
in the chart at `x`, as the chart-pullback derivative `(f ∘ chart⁻¹)'`.  The two lemmas below carry
this (and the analytic ⇒ `MDifferentiableAt` converse) — they are pure Mathlib manifold-calculus,
independent of the meromorphic structure. -/

/-- **The intrinsic-differential / chart-derivative bridge.**  For `y` in the chart source at `x`
where `f` is `MDifferentiableAt`, the covector `mfderiv f y` paired with the spanning tangent vector
`symmL ℂ y 1` equals the ordinary derivative of the chart pullback `f ∘ chart⁻¹` at `chart y`.

This is the chain rule `mfderiv f ∘ mfderiv chart⁻¹ = mfderiv (f ∘ chart⁻¹)`, with
`symmL ℂ y = mfderiv chart⁻¹ (chart y)` (`TangentBundle.symmL_trivializationAt`) and
`mfderiv (f ∘ chart⁻¹) = fderiv` on the model space (`mfderiv_eq_fderiv`). -/
theorem mfderiv_apply_symmL_eq_deriv (f : X → ℂ) {x y : X} (hy : y ∈ (chartAt ℂ x).source)
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) f y
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ y 1)
      = deriv (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) y) := by
  have hytarget : (extChartAt 𝓘(ℂ) x) y ∈ (extChartAt 𝓘(ℂ) x).target :=
    (extChartAt 𝓘(ℂ) x).map_source (by rwa [extChartAt_source])
  have hyback : (extChartAt 𝓘(ℂ) x).symm ((extChartAt 𝓘(ℂ) x) y) = y :=
    (extChartAt 𝓘(ℂ) x).left_inv (by rwa [extChartAt_source])
  have hsymm_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x y) := by
    have h1 := mdifferentiableWithinAt_extChartAt_symm (I := 𝓘(ℂ)) (x := x) hytarget
    rwa [ModelWithCorners.range_eq_univ, mdifferentiableWithinAt_univ] at h1
  have hf_mf' : HasMFDerivAt 𝓘(ℂ) 𝓘(ℂ) f ((extChartAt 𝓘(ℂ) x).symm ((extChartAt 𝓘(ℂ) x) y))
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) f y) := by rw [hyback]; exact hf.hasMFDerivAt
  have hcomp := hf_mf'.comp (extChartAt 𝓘(ℂ) x y) hsymm_diff.hasMFDerivAt
  have hcomp_app := DFunLike.congr_fun hcomp.mfderiv (1 : ℂ)
  have hsymmL : (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ y =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (extChartAt 𝓘(ℂ) x).symm (extChartAt 𝓘(ℂ) x y) := by
    rw [TangentBundle.symmL_trivializationAt hy, ModelWithCorners.range_eq_univ, mfderivWithin_univ]
  rw [hsymmL]
  rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv,
     show (f ∘ (chartAt ℂ x).symm) = (f ∘ (extChartAt 𝓘(ℂ) x).symm) from rfl,
     show ((chartAt ℂ x) y) = ((extChartAt 𝓘(ℂ) x) y) from rfl]
  exact hcomp_app.symm

/-- **Chart-pullback differentiability ⇒ `MDifferentiableAt f`.**  If `f ∘ chart⁻¹` is
`DifferentiableAt` at a chart-target point `z`, then `f` is `MDifferentiableAt` at `chart⁻¹ z`.
(For the codomain `ℂ` the extended chart is the identity, so the manifold-differentiability
criterion `mdifferentiableAt_iff_of_mem_source` is just chart-pullback differentiability.) -/
theorem mdifferentiableAt_of_differentiableAt_comp (f : X → ℂ) {x : X} {z : ℂ}
    (hz : z ∈ (chartAt ℂ x).target)
    (hdiff : DifferentiableAt ℂ (f ∘ (chartAt ℂ x).symm) z) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f ((chartAt ℂ x).symm z) := by
  have hztarget : z ∈ (extChartAt 𝓘(ℂ) x).target := by
    rw [extChartAt_target, ModelWithCorners.range_eq_univ]; simpa using hz
  have hys : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := by
    rw [← extChartAt_source 𝓘(ℂ) x]; exact (extChartAt 𝓘(ℂ) x).map_target hztarget
  have hfy : f ((chartAt ℂ x).symm z) ∈ (chartAt ℂ (f ((chartAt ℂ x).symm z))).source :=
    mem_chart_source ℂ _
  rw [mdifferentiableAt_iff_of_mem_source hys hfy, ModelWithCorners.range_eq_univ,
    differentiableWithinAt_univ]
  have hzeq : (chartAt ℂ x) ((chartAt ℂ x).symm z) = z := (chartAt ℂ x).right_inv hz
  have hcont : ContinuousAt f ((chartAt ℂ x).symm z) := by
    have h1 : ContinuousAt (f ∘ (chartAt ℂ x).symm) z := hdiff.continuousAt
    have h2 : ContinuousAt (chartAt ℂ x) ((chartAt ℂ x).symm z) := (chartAt ℂ x).continuousAt hys
    have h3 : ContinuousAt ((f ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) ((chartAt ℂ x).symm z) :=
      h1.comp_of_eq h2 hzeq
    refine h3.congr ?_
    filter_upwards [(chartAt ℂ x).open_source.mem_nhds hys] with w hw
    simp only [Function.comp_apply, (chartAt ℂ x).left_inv hw]
  refine ⟨hcont, ?_⟩
  have heq : (extChartAt 𝓘(ℂ) (f ((chartAt ℂ x).symm z))) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm
       = (f ∘ (chartAt ℂ x).symm) := by ext w; rfl
  rw [heq, show (extChartAt 𝓘(ℂ) x) ((chartAt ℂ x).symm z) = z from hzeq]
  exact hdiff

/-! ## Part 2: the differential `df` as a meromorphic 1-form

`df.toFun x := mfderiv 𝓘(ℂ) 𝓘(ℂ) f x` (junk-`0` at poles).  Its chart coefficient agrees on a
punctured neighbourhood with `(f ∘ chart⁻¹)'` (`MeromorphicAt.deriv`), so `df` is a genuine
`MeromorphicOneForm`. -/

/-- The underlying cotangent-bundle section of the differential `df`: `x ↦ mfderiv f x`. -/
noncomputable def differentialSection (f : MeromorphicFunction X) : ∀ x, FormFiber X x :=
  fun x => mfderiv 𝓘(ℂ) 𝓘(ℂ) f.toFun x

/-- `formCoeff (df) x` agrees with the chart-pullback derivative `(f ∘ chart⁻¹)'` on a punctured
neighbourhood of `chart x x` (precisely where `f ∘ chart⁻¹` is analytic, hence `f` is
`MDifferentiableAt`). -/
theorem formCoeff_differentialSection_eventuallyEq (f : MeromorphicFunction X) (x : X) :
    (fun z => deriv (f.toFun ∘ (chartAt ℂ x).symm) z) =ᶠ[𝓝[≠] ((chartAt ℂ x) x)]
      formCoeff (differentialSection f) x := by
  have hmero : MeromorphicAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) ((chartAt ℂ x) x) :=
    f.meromorphic x
  have htarget : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) x) :=
    (chartAt ℂ x).open_target.mem_nhds ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  filter_upwards [hmero.eventually_analyticAt, nhdsWithin_le_nhds htarget] with z hz_an hz_target
  have hdiff : DifferentiableAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) z := hz_an.differentiableAt
  have hmdiff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f.toFun ((chartAt ℂ x).symm z) :=
    mdifferentiableAt_of_differentiableAt_comp f.toFun hz_target hdiff
  have hysrc : (chartAt ℂ x).symm z ∈ (chartAt ℂ x).source := by
    rw [← extChartAt_source 𝓘(ℂ) x]
    apply (extChartAt 𝓘(ℂ) x).map_target
    rw [extChartAt_target, ModelWithCorners.range_eq_univ]; simpa using hz_target
  have hzeq : (chartAt ℂ x) ((chartAt ℂ x).symm z) = z := (chartAt ℂ x).right_inv hz_target
  show deriv (f.toFun ∘ (chartAt ℂ x).symm) z = _
  rw [show formCoeff (differentialSection f) x z
        = mfderiv 𝓘(ℂ) 𝓘(ℂ) f.toFun ((chartAt ℂ x).symm z)
            ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ ((chartAt ℂ x).symm z) 1)
        from rfl]
  rw [mfderiv_apply_symmL_eq_deriv f.toFun hysrc hmdiff, hzeq]

/-- `df` is a **meromorphic 1-form**: its chart coefficient is `MeromorphicAt` because it germ-agrees
with `(f ∘ chart⁻¹)'`, the derivative of a meromorphic function (`MeromorphicAt.deriv`). -/
theorem isMeromorphicOneForm_differentialSection (f : MeromorphicFunction X) :
    IsMeromorphicOneForm (differentialSection f) := by
  intro x
  have hderiv : MeromorphicAt (deriv (f.toFun ∘ (chartAt ℂ x).symm)) ((chartAt ℂ x) x) :=
    (f.meromorphic x).deriv
  exact hderiv.congr (formCoeff_differentialSection_eventuallyEq f x)

/-- The **canonical meromorphic 1-form `ω₀ = df`** of a meromorphic function `f`. -/
noncomputable def differentialForm (f : MeromorphicFunction X) : MeromorphicOneForm X :=
  ⟨differentialSection f, isMeromorphicOneForm_differentialSection f⟩

@[simp] theorem differentialForm_toFun (f : MeromorphicFunction X) (x : X) :
    (differentialForm f).toFun x = mfderiv 𝓘(ℂ) 𝓘(ℂ) f.toFun x := rfl

/-- `formOrderW (df)` at `x` is the meromorphic order of the chart-pullback derivative
`(f ∘ chart⁻¹)'` (via the germ-agreement of `formCoeff (df)` with it). -/
theorem formOrderW_differentialForm (f : MeromorphicFunction X) (x : X) :
    (differentialForm f).formOrderW x
      = meromorphicOrderAt (deriv (f.toFun ∘ (chartAt ℂ x).symm)) ((chartAt ℂ x) x) := by
  rw [MeromorphicOneForm.formOrderW]
  exact (meromorphicOrderAt_congr (formCoeff_differentialSection_eventuallyEq f x)).symm

/-! ## Part 3: `df ≠ 0` for a nonconstant `f` (the soundness-critical field)

If `f` is nonconstant (`¬ IsGermConstant`), then `df ≠ 0` (`∃ x, formOrderW (df) x ≠ ⊤`).  The
contrapositive `df = 0 ⟹ IsGermConstant f` goes through the **no-pole reduction**: if
`deriv (f ∘ chart⁻¹)` vanishes on a punctured neighbourhood at every point, then `f` has no pole
(`deriv_eventually_zero_meromorphicOrderAt_nonneg`: a pole of order `n < 0` forces `deriv` to have a
pole of order `n − 1 < 0 ≠ ⊤`), so `f ∈ L(0)`, and then the repo's Liouville
`germ_eq_const_of_mem_linearSystem_zero` makes `f` germ-constant. -/

/-- **No pole from a vanishing-derivative germ.**  If `g` is meromorphic at `z₀` and its derivative
vanishes on a punctured neighbourhood of `z₀`, then `g` has *no pole* at `z₀`
(`meromorphicOrderAt g z₀ ≥ 0`).  Proof: were `meromorphicOrderAt g z₀ = n < 0`, the Laurent form
`g =ᶠ (·−z₀)ⁿ • G` (`G` analytic, `G z₀ ≠ 0`) makes `deriv g =ᶠ (n·(·−z₀)ⁿ⁻¹)·G + (·−z₀)ⁿ·G'`, whose
order is exactly `n − 1` (the first term dominates, as `n ≠ 0`, `G z₀ ≠ 0`); but `deriv g =ᶠ 0` forces
order `⊤ ≠ n − 1`.  Pure planar complex analysis (mirrors Mathlib's `MeromorphicAt.deriv`). -/
theorem deriv_eventually_zero_meromorphicOrderAt_nonneg {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : MeromorphicAt g z₀) (hdz : ∀ᶠ z in 𝓝[≠] z₀, deriv g z = 0) :
    0 ≤ meromorphicOrderAt g z₀ := by
  by_contra hlt
  push Not at hlt
  have hne_top : meromorphicOrderAt g z₀ ≠ ⊤ := hlt.ne_top
  lift meromorphicOrderAt g z₀ to ℤ using hne_top with n hn
  have hn_neg : n < 0 := by exact_mod_cast hlt
  obtain ⟨G, hG_an, hG_ne, hG_eq⟩ := (meromorphicOrderAt_eq_int_iff hg).1 hn.symm
  have hderiv_eq1 : deriv g =ᶠ[𝓝[≠] z₀] deriv (fun z => (z - z₀) ^ n • G z) :=
    Filter.EventuallyEq.nhdsNE_deriv hG_eq
  -- the explicit derivative of `(·−z₀)ⁿ • G` (mirror of the computation in `MeromorphicAt.deriv`)
  have hderiv_eq2 : deriv (fun z => (z - z₀) ^ n • G z)
      =ᶠ[𝓝[≠] z₀] fun z => (n * (z - z₀) ^ (n - 1)) • G z + (z - z₀) ^ n • deriv G z := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hG_an.eventually_analyticAt,
      eventually_nhdsWithin_of_forall fun _ a => a] with z h₁ h₂
    rw [deriv_fun_smul (DifferentiableAt.zpow (by fun_prop) (by simp_all [sub_ne_zero_of_ne h₂]))
      (by fun_prop), add_comm, deriv_comp_sub_const (f := (· ^ n))]
    aesop
  have hsum_eq : (fun z => (n * (z - z₀) ^ (n - 1)) • G z + (z - z₀) ^ n • deriv G z)
      =ᶠ[𝓝[≠] z₀] (0 : ℂ → ℂ) := (hderiv_eq2.symm.trans hderiv_eq1.symm).trans hdz
  have hord_sum_top : meromorphicOrderAt
      (fun z => (n * (z - z₀) ^ (n - 1)) • G z + (z - z₀) ^ n • deriv G z) z₀ = ⊤ := by
    rw [meromorphicOrderAt_congr hsum_eq, meromorphicOrderAt_eq_top_iff]
    exact eventually_nhdsWithin_of_forall (fun _ _ => rfl)
  have hcoeff_mero : MeromorphicAt (fun z => (n : ℂ) * (z - z₀) ^ (n - 1)) z₀ := by
    apply MeromorphicAt.mul (MeromorphicAt.const _ _)
    exact (MeromorphicAt.id z₀ |>.sub (MeromorphicAt.const z₀ z₀)).zpow _
  have hterm2_mero : MeromorphicAt (fun z => (z - z₀) ^ n • deriv G z) z₀ := by
    apply MeromorphicAt.smul _ hG_an.meromorphicAt.deriv
    exact (MeromorphicAt.id z₀ |>.sub (MeromorphicAt.const z₀ z₀)).zpow _
  -- the first term has order exactly `n − 1`
  have hord1 : meromorphicOrderAt (fun z => (↑n * (z - z₀) ^ (n - 1)) • G z) z₀
      = ((n - 1 : ℤ) : WithTop ℤ) := by
    rw [show (fun z => (↑n * (z - z₀) ^ (n - 1)) • G z)
          = (fun z => (n : ℂ) * (z - z₀) ^ (n - 1)) • G from rfl,
        meromorphicOrderAt_smul hcoeff_mero hG_an.meromorphicAt,
        hG_an.meromorphicOrderAt_eq, (hG_an.analyticOrderAt_eq_zero).mpr hG_ne]
    have hcoeff_ord : meromorphicOrderAt (fun z => (n : ℂ) * (z - z₀) ^ (n - 1)) z₀
        = ((n - 1 : ℤ) : WithTop ℤ) := by
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn_neg.ne
      rw [meromorphicOrderAt_eq_int_iff hcoeff_mero]
      exact ⟨fun _ => (n : ℂ), analyticAt_const, hn0,
        by filter_upwards [] with z; rw [smul_eq_mul, mul_comm]⟩
    rw [hcoeff_ord]; simp
  -- the second term has order ≥ n
  have hord2_ge : (n : WithTop ℤ) ≤ meromorphicOrderAt (fun z => (z - z₀) ^ n • deriv G z) z₀ := by
    have hm : MeromorphicAt (fun z => (z - z₀) ^ n) z₀ :=
      (MeromorphicAt.id z₀ |>.sub (MeromorphicAt.const z₀ z₀)).zpow _
    rw [show (fun z => (z - z₀) ^ n • deriv G z) = (fun z => (z - z₀) ^ n) • deriv G from rfl,
        meromorphicOrderAt_smul hm hG_an.meromorphicAt.deriv]
    have hzpow_ord : meromorphicOrderAt (fun z => (z - z₀) ^ n) z₀ = (n : WithTop ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff hm]
      exact ⟨fun _ => 1, analyticAt_const, one_ne_zero, by filter_upwards [] with z; simp⟩
    rw [hzpow_ord]
    calc (n : WithTop ℤ) = (n : WithTop ℤ) + 0 := by rw [add_zero]
      _ ≤ (n : WithTop ℤ) + meromorphicOrderAt (deriv G) z₀ := by
            gcongr; exact hG_an.deriv.meromorphicOrderAt_nonneg
  have hlt12 : meromorphicOrderAt (fun z => (↑n * (z - z₀) ^ (n - 1)) • G z) z₀
      < meromorphicOrderAt (fun z => (z - z₀) ^ n • deriv G z) z₀ := by
    rw [hord1]
    exact lt_of_lt_of_le (by exact_mod_cast (by omega : (n - 1 : ℤ) < n)) hord2_ge
  have hsum_ord : meromorphicOrderAt
      (fun z => (n * (z - z₀) ^ (n - 1)) • G z + (z - z₀) ^ n • deriv G z) z₀
      = ((n - 1 : ℤ) : WithTop ℤ) := by
    rw [show (fun z => (↑n * (z - z₀) ^ (n - 1)) • G z + (z - z₀) ^ n • deriv G z)
          = (fun z => (↑n * (z - z₀) ^ (n - 1)) • G z) + (fun z => (z - z₀) ^ n • deriv G z) from rfl,
        meromorphicOrderAt_add_eq_left_of_lt hterm2_mero hlt12, hord1]
  rw [hsum_ord] at hord_sum_top
  exact WithTop.coe_ne_top hord_sum_top

/-- **`df ≠ 0` for a nonconstant `f`** (Forster §17.4's nontriviality of `ω₀ = df`).  If `f` is not
germ-constant then `df`'s germ is nonzero somewhere.  Contrapositive: if `formOrderW (df) = ⊤`
everywhere, then `deriv (f ∘ chart⁻¹)` vanishes on a punctured neighbourhood at every point, so `f`
has no pole anywhere (`deriv_eventually_zero_meromorphicOrderAt_nonneg`), i.e. `f ∈ L(0)`; then `f`
is germ-constant by the repo Liouville `germ_eq_const_of_mem_linearSystem_zero`. -/
theorem differentialForm_ne_zero {f : MeromorphicFunction X} (hf : ¬ IsGermConstant f) :
    ∃ x, (differentialForm f).formOrderW x ≠ ⊤ := by
  by_contra hcon
  push Not at hcon
  apply hf
  have hf0 : f ∈ linearSystem (X := X) 0 := by
    intro x
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    show (0 : WithTop ℤ) ≤ MeromorphicFunction.orderW f x
    rw [MeromorphicFunction.orderW]
    have htop := hcon x
    rw [formOrderW_differentialForm, meromorphicOrderAt_eq_top_iff] at htop
    exact deriv_eventually_zero_meromorphicOrderAt_nonneg (f.meromorphic x) htop
  exact germ_eq_const_of_mem_linearSystem_zero f hf0

end Jacobians.Dolbeault
