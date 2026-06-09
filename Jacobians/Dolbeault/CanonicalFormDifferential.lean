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

end Jacobians.Dolbeault
