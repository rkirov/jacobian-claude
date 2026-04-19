import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Jacobians.Genus

/-!
# Holomorphic 1-forms on a complex manifold

Uses Mathlib's `ContMDiffSection` and the `Bundle.ContinuousLinearMap`
hom-of-bundles construction to define holomorphic 1-forms as **analytic
sections of the cotangent bundle**.

The cotangent bundle at a point `x : X` is
`TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ`, built via Mathlib's hom-of-bundles
machinery (`Bundle.ContinuousLinearMap.fiberBundle`, `vectorBundle`,
and `vectorPrebundle.isContMDiff`).

This is the **honest** definition (compare to a placeholder that sets
`HolomorphicOneForms X := Fin (genus X) → ℂ`).

## Dimension theorem (sorry)

On a compact connected complex 1-manifold, `HolomorphicOneForms X` is
a finite-dim ℂ-vector space of dimension `genus X`. This is a classical
result (Riemann–Roch) and is recorded here as a sorry with TODO(math).

## References

Forster §§9–10; Miranda Ch. 4 §1.
-/

namespace Jacobians

open scoped Manifold ContDiff Bundle

/-- The ℂ-vector space of global analytic sections of the cotangent bundle
of a compact connected complex 1-manifold.

Mathematically: global holomorphic 1-forms on `X`. The cotangent bundle
is built as `Bundle.ContinuousLinearMap (RingHom.id ℂ) (TangentSpace,
Bundle.Trivial X ℂ)` — the fiberwise continuous linear maps from
tangent to trivial-ℂ-bundle. -/
def HolomorphicOneForms (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
    (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)

section Instances

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

noncomputable instance : AddCommGroup (HolomorphicOneForms X) :=
  inferInstanceAs (AddCommGroup
    (ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)))

noncomputable instance : Module ℂ (HolomorphicOneForms X) :=
  inferInstanceAs (Module ℂ
    (ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)))

end Instances

section Curve

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **TODO(math)**: on a compact connected complex 1-manifold, the space
of global holomorphic 1-forms is finite-dimensional. (Cartan–Serre
applied to the sheaf `Ω¹_X`.) -/
noncomputable instance : FiniteDimensional ℂ (HolomorphicOneForms X) := sorry

/-- **TODO(math)**: dimension of holomorphic 1-forms = genus.
Riemann–Roch / Dolbeault on a compact connected complex 1-manifold. -/
theorem finrank_HolomorphicOneForms_eq_genus :
    Module.finrank ℂ (HolomorphicOneForms X) = genus X := sorry

end Curve

/-! ### Pullback of forms along a holomorphic map. -/

section Functoriality

variable {X Y Z : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z] [Nonempty Z]
    [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

/-- Pullback of a holomorphic 1-form along a holomorphic map of complex
manifolds.

The pointwise formula is `(pullbackForm g α)(x) = α(g x) ∘ mfderiv g x`.
Expressed as a ℂ-linear map on sections — marked `sorry` because the
full construction (pointwise + smoothness + linearity) needs three
sub-sorries which net out worse than a single opaque sorry here. -/
noncomputable def pullbackForm (g : X → Y) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    HolomorphicOneForms Y →ₗ[ℂ] HolomorphicOneForms X := sorry

/-- **TODO(math)**: `pullbackForm id = id`. -/
theorem pullbackForm_id : pullbackForm (id : X → X) contMDiff_id =
    LinearMap.id (R := ℂ) (M := HolomorphicOneForms X) := sorry

/-- **TODO(math)**: contravariance of pullback. -/
theorem pullbackForm_comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f)) :
    pullbackForm (g ∘ f) hgf =
      (pullbackForm f hf).comp (pullbackForm g hg) := sorry

end Functoriality

/-! ### Pushforward of forms under a proper holomorphic map between curves. -/

section PushforwardCurve

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **TODO(math)**: pushforward of holomorphic 1-forms under a
holomorphic map of compact Riemann surfaces. -/
noncomputable def pushforwardForm (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForms X →ₗ[ℂ] HolomorphicOneForms Y := sorry

/-- **TODO(math)**: the headline identity `f_* ∘ f^* = deg(f) • id`. -/
theorem pushforwardForm_pullbackForm_eq (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (d : ℕ) (P : HolomorphicOneForms Y) :
    pushforwardForm f hf (pullbackForm f hf P) = (d : ℂ) • P := sorry

end PushforwardCurve

end Jacobians
