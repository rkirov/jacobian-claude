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

Pointwise: `(pullbackForm g α)(x) = α(g x) ∘ mfderiv g x`. -/
noncomputable def pullbackForm (g : X → Y) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    HolomorphicOneForms Y →ₗ[ℂ] HolomorphicOneForms X where
  toFun α :=
    { toFun := fun x : X =>
        (α.toFun (g x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g x)
      contMDiff_toFun := sorry /- TODO(math): chain rule on bundle sections -/ }
  map_add' α₁ α₂ := by
    apply ContMDiffSection.ext
    intro x
    show ((α₁ + α₂).toFun (g x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g x) =
      ((α₁.toFun (g x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g x)) +
        ((α₂.toFun (g x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g x))
    rfl
  map_smul' c α := by
    apply ContMDiffSection.ext
    intro x
    show ((c • α).toFun (g x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g x) =
      c • (α.toFun (g x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g x)
    rfl

/-- `pullbackForm id = id`. Follows from `mfderiv id = id` and
`ContinuousLinearMap.comp_id`. -/
theorem pullbackForm_id : pullbackForm (id : X → X) contMDiff_id =
    LinearMap.id (R := ℂ) (M := HolomorphicOneForms X) := by
  ext α
  apply ContMDiffSection.ext
  intro x
  show (α.toFun x).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) (id : X → X) x) = α.toFun x
  rw [mfderiv_id]
  exact ContinuousLinearMap.comp_id _

/-- Contravariance of pullback: `(g ∘ f)^* = f^* ∘ g^*`. Follows from
the chain rule `mfderiv_comp` + associativity of composition. -/
theorem pullbackForm_comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f)) :
    pullbackForm (g ∘ f) hgf =
      (pullbackForm f hf).comp (pullbackForm g hg) := by
  ext α
  apply ContMDiffSection.ext
  intro x
  show (α.toFun ((g ∘ f) x)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) (g ∘ f) x) =
    ((α.toFun (g (f x))).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g (f x))).comp
      (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x)
  rw [mfderiv_comp x (hg.mdifferentiableAt (by decide))
    (hf.mdifferentiableAt (by decide))]
  exact (ContinuousLinearMap.comp_assoc _ _ _).symm

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

/-! ### Ambient-space bridge

Connects the forms side (`HolomorphicOneForms X`, `pullbackForm`,
`pushforwardForm`) to the Jacobian-quotient ambient `(Fin (genus X) → ℂ)`
via a basis isomorphism and dualization. This is the glue layer between
`HolomorphicForms` and `ZLatticeQuotient` (where the quotient descent
lives).

|Ambient side                            |Forms side                        |
|----------------------------------------|----------------------------------|
|`Φ : (Fin gX → ℂ) →L[ℝ] (Fin gY → ℂ)`    |dual of `pullbackForm f hf`       |
|`Ψ : (Fin gY → ℂ) →L[ℝ] (Fin gX → ℂ)`    |dual of `pushforwardForm f hf`    |
|`Φ (Ψ y) = d • y`                       |`pushforwardForm_pullbackForm_eq` |
-/

section AmbientBridge

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- A linear isomorphism `(Fin (genus X) → ℂ) ≃ₗ[ℂ] HolomorphicOneForms X`
from a choice of basis, via `Module.finBasisOfFinrankEq` + the sorried
dimension equality `finrank_HolomorphicOneForms_eq_genus`. -/
noncomputable def ambientIso (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    (Fin (genus X) → ℂ) ≃ₗ[ℂ] HolomorphicOneForms X :=
  (Module.finBasisOfFinrankEq ℂ (HolomorphicOneForms X)
    (finrank_HolomorphicOneForms_eq_genus X)).equivFun.symm

/-- **TODO(math)**: the ambient ℝ-linear map `Φ` induced by the pushforward
of forms along `f : X → Y`. Concretely `(ambientIso Y).symm ∘
pushforwardForm f hf ∘ ambientIso X`, restricted to ℝ-linear. Left
sorry pending pushforwardForm content + continuous-linearity tracking. -/
noncomputable def ambientPhi {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin gX → ℂ) →L[ℝ] (Fin gY → ℂ) := sorry

/-- **TODO(math)**: the ambient ℝ-linear map `Ψ` induced by the pullback
of forms along `f : X → Y`. -/
noncomputable def ambientPsi {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin gY → ℂ) →L[ℝ] (Fin gX → ℂ) := sorry

/-- **TODO(math)**: the ambient degree identity, dualized from
`pushforwardForm_pullbackForm_eq`. -/
theorem ambientPhi_ambientPsi_eq {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (d : ℕ)
    (y : Fin gY → ℂ) :
    ambientPhi (gX := gX) (gY := gY) f hf (ambientPsi f hf y) = (d : ℕ) • y := sorry

/-- **TODO(math)**: `ambientPhi id = id` (dualizes `pullbackForm_id`). -/
theorem ambientPhi_id {g : ℕ} (x : Fin g → ℂ) :
    ambientPhi (X := X) (Y := X) (gX := g) (gY := g) id contMDiff_id x = x := sorry

/-- **TODO(math)**: covariant composition: `ambientPhi (g ∘ f) =
ambientPhi g ∘ ambientPhi f`. -/
theorem ambientPhi_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    {gX gY gZ : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f))
    (x : Fin gX → ℂ) :
    ambientPhi (gX := gX) (gY := gZ) (g ∘ f) hgf x =
      ambientPhi (gX := gY) (gY := gZ) g hg
        (ambientPhi (gX := gX) (gY := gY) f hf x) := sorry

/-- **TODO(math)**: `ambientPsi id = id`. -/
theorem ambientPsi_id {g : ℕ} (y : Fin g → ℂ) :
    ambientPsi (X := X) (Y := X) (gX := g) (gY := g) id contMDiff_id y = y := sorry

/-- **TODO(math)**: contravariant composition: `ambientPsi (g ∘ f) =
ambientPsi f ∘ ambientPsi g`. -/
theorem ambientPsi_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    {gX gY gZ : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f))
    (z : Fin gZ → ℂ) :
    ambientPsi (gX := gX) (gY := gZ) (g ∘ f) hgf z =
      ambientPsi (gX := gX) (gY := gY) f hf
        (ambientPsi (gX := gY) (gY := gZ) g hg z) := sorry

end AmbientBridge

end Jacobians
