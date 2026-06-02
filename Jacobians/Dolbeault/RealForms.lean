/-
  Dolbeault ladder — smooth ℂ-valued 1-forms over the real-manifold structure (the INTRINSIC route).

  On top of `RealManifold` (the real-`C^∞` structure of the complex manifold), this is the intrinsic
  real cotangent valued in `ℂ`: smooth sections of `TangentSpace 𝓘(ℝ,ℂ) →L[ℝ] ℂ`. This is the
  textbook-standard container for the Dolbeault complex `A¹ = A^{1,0} ⊕ A^{0,1}` (`∂̄u` lands in the
  `(0,1)` part) — no chart-local cocycle bespoke machinery.

  Mathlib's hom-of-bundles machinery is generic over the scalar field, so the only obstructions are
  the same ℂ-as-ℝ-module diamond as in `RealManifold` (handled with the same
  `set_option backward.isDefEq.respectTransparency false`, as Mathlib's own `Complex/RealDeriv.lean`),
  plus the single instance the hom-bundle needs but doesn't auto-derive for the *sub*-field ℝ:
  `ContinuousSMul ℝ (Trivial X ℂ)` (the trivial fiber `Trivial X ℂ x` is defeq `ℂ`).
-/
import Jacobians.Dolbeault.RealManifold
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions

open scoped Manifold ContDiff Bundle

set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Real-smooth `ℂ`-valued functions** `A⁰` on `X` — the source of `∂̄`: real-`C^∞` maps `X → ℂ`
(over the real model, i.e. NOT holomorphic). A real vector space. -/
abbrev SmoothCFunctions (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  ContMDiffMap (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) X ℂ (⊤ : ℕ∞)

noncomputable example : AddCommGroup (SmoothCFunctions X) := inferInstance

/-- The trivial `ℂ`-bundle is a continuous `ℝ`-module — the one instance Mathlib's hom-of-bundles
machinery needs but does not auto-derive for the sub-field `ℝ` (`Trivial X ℂ x` is defeq `ℂ`, and the
ℂ-`ℝ`-module diamond is resolved by the file `set_option`). -/
instance trivial_continuousSMul_real (x : X) : ContinuousSMul ℝ (Bundle.Trivial X ℂ x) :=
  inferInstanceAs (ContinuousSMul ℝ ℂ)

/-- **Smooth `ℂ`-valued 1-forms** on `X`: smooth sections of the real cotangent valued in `ℂ`
(real-linear maps `TangentSpace 𝓘(ℝ,ℂ) x → ℂ`). The intrinsic container for the Dolbeault complex
`A¹ = A^{1,0} ⊕ A^{0,1}`. A real (`Module ℝ`) vector space. -/
abbrev SmoothCOneForms (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  ContMDiffSection (𝓘(ℝ, ℂ)) (ℂ →L[ℝ] ℂ) (⊤ : ℕ∞)
    (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x)

-- The intrinsic 1-form space is a genuine real vector space (validates the representation).
noncomputable example : AddCommGroup (SmoothCOneForms X) := inferInstance
noncomputable example : Module ℝ (SmoothCOneForms X) := inferInstance

/-- The **de Rham differential** `d : A⁰ → A¹` — the real differential `du = mfderiv u` of a smooth
`ℂ`-valued function, a smooth `ℂ`-valued 1-form. (`∂̄u` is its `(0,1)`-part; `∂u` the `(1,0)`-part.)
The section-smoothness is the standard "the differential of a `C^∞` function is a `C^∞` 1-form"
(`mfderiv_const` in tangent coordinates, bridged to the trivial-bundle codomain `ℂ`). -/
noncomputable def differential (u : SmoothCFunctions X) : SmoothCOneForms X where
  toFun := fun x => mfderiv (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ)) u x
  contMDiff_toFun := by
    intro x₀
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    have h := (u.contMDiff x₀).mfderiv_const (m := (⊤ : ℕ∞)) (by simp)
    convert h using 3 with x
    simp only [inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      Bundle.Trivial.continuousLinearMapAt_trivialization,
      Bundle.Trivial.fiberBundle_trivializationAt',
      TangentBundle.continuousLinearMapAt_trivializationAt, ContinuousLinearMap.id_comp, mfld_simps]

/-- Multiplication by `i` as a real-linear endomorphism of `ℂ` (`= J`, the complex structure on the
real tangent space `T_x ≅ ℂ`). -/
noncomputable def mulI : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ) Complex.I

/-- The **`(0,1)`-projection** on real-linear forms `ℂ →L[ℝ] ℂ`: `P(α) = ½(α + i·α(i·−))`, the
conjugate-`ℂ`-linear (Cauchy–Riemann) part. A fixed continuous-linear fiber endomorphism; applied
fiberwise to `du` it carves `∂̄u` out of the de Rham differential. -/
noncomputable def proj01 : (ℂ →L[ℝ] ℂ) →L[ℝ] (ℂ →L[ℝ] ℂ) :=
  (2 : ℝ)⁻¹ • (ContinuousLinearMap.id ℝ (ℂ →L[ℝ] ℂ) +
    (ContinuousLinearMap.compL ℝ ℂ ℂ ℂ mulI).comp ((ContinuousLinearMap.compL ℝ ℂ ℂ ℂ).flip mulI))

/-- The **Dolbeault `∂̄` operator** `A⁰ → A^{0,1} ⊆ A¹`: the `(0,1)`-part of the de Rham differential,
`∂̄u = proj01 ∘ du`. A smooth `ℂ`-valued 1-form. Section-smoothness is `clm_bundle_apply` (apply the
constant fiber endomorphism `proj01` to the smooth section `du`). -/
noncomputable def dbar (u : SmoothCFunctions X) : SmoothCOneForms X where
  toFun := fun x => proj01 ((differential u).toFun x)
  contMDiff_toFun := by
    intro x₀
    rw [contMDiffAt_hom_bundle]
    refine ⟨contMDiffAt_id, ?_⟩
    simp only [ContinuousLinearMap.inCoordinates,
      Bundle.Trivial.continuousLinearMapAt_trivialization,
      Bundle.Trivial.fiberBundle_trivializationAt', ContinuousLinearMap.id_comp]
    -- After trivialising the (trivial) `ℂ`-codomain the obligation reads
    --   `x ↦ (proj01 (du x)).comp (symmL_tan x)`  is `C^∞`,   `du := differential u`,
    --   `symmL_tan x := (trivializationAt ℂ (TangentSpace 𝓘(ℝ,ℂ)) x₀).symmL ℝ x : ℂ →L T_x`.
    -- Expand `proj01 (du x) = ½ (du x + mulI ∘ du x ∘ mulI)` and distribute `.comp (symmL_tan x)`:
    --   ½ ( A x  +  mulI ∘ ((A x) ∘ Jcoord x) ),
    --     A x      := (du x) ∘ symmL_tan x          -- exactly `differential`'s reduced smoothness,
    --     Jcoord x := (clmAt_tan x) ∘ mulI ∘ (symmL_tan x)
    --               = `inCoordinates` of the *constant* `mulI` in the tangent bundle,
    -- using the eventual identity `symmL_tan x ∘ clmAt_tan x =ᶠ id` (`x ∈ baseSet` near `x₀`).
    -- `A` is `C^∞`; the combination is then `C^∞` by `clm_comp`/`const_smul` AS SOON AS `Jcoord` is.
    -- `Jcoord` is the complex structure `J = (·*i)` on the real tangent bundle read in coordinates;
    -- it is `C^∞` because the tangent `coordChange` is (`ContMDiffVectorBundle (TangentSpace …)`,
    -- `contMDiffOn_coordChangeL`) and `Jcoord` conjugates the fixed `mulI` by it. Mathlib exposes no
    -- `J`-as-smooth-section API for a complex manifold's real tangent bundle, so this last bundle-
    -- coordinate step is the sole open obligation — the only genuinely complex-geometric input to ∂̄.
    sorry

end Jacobians.Dolbeault
