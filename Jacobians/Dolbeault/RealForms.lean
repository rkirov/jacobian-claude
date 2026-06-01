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

end Jacobians.Dolbeault
