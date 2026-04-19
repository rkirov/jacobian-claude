import Mathlib.Geometry.Manifold.Complex
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Holomorphic 1-forms on a complex manifold

**Skeleton** — defines the type `HolomorphicOneForms X` of global
holomorphic 1-forms on a complex manifold and declares its structural
instances as sorries. Actual construction (as sections of the
holomorphic cotangent bundle, or via alternating multilinear maps + a
holomorphy condition) is future work.

The definition here is signature-compatible with the eventual real
definition: `HolomorphicOneForms X` is a `ℂ`-vector space, and on a
compact connected complex manifold of complex dimension 1 it is
finite-dimensional of dimension equal to the genus.

## Goals of this file

* Expose an API surface other files can depend on (`HolomorphicOneForms X`,
  its ℂ-module structure, its finite-dimensionality on curves).
* Declare the two key maps: pullback `f^*` along a holomorphic `f : X → Y`
  and pushforward `f_*` when `f` is a proper holomorphic map between
  equidimensional connected complex manifolds.
* Leave the construction and proofs as sorry; this file establishes the
  interface.

## References

Forster §§9–10 (holomorphic 1-forms and their cohomology);
Miranda Ch. 4 §1 (regular forms on Riemann surfaces).

## TODO(math)

The real construction: `H⁰(X, Ω¹)` as the global sections of the sheaf
of holomorphic 1-forms. For a compact Riemann surface of genus `g`, this
is a `ℂ`-vector space of dimension `g` (half the rank of `H₁(X, ℝ)`,
equivalently the holomorphic half of the Hodge decomposition).
-/

namespace Jacobians

open scoped Manifold ContDiff

/-- The `ℂ`-vector space of global holomorphic 1-forms on a complex manifold.
**TODO(math)**: replace the `sorry` with a real construction — sections
of the holomorphic cotangent bundle, or alternating `ℂ`-linear maps on
the tangent space varying holomorphically. -/
def HolomorphicOneForms (X : Type*) [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Type := sorry

section Instances

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) ω X]

/-- **TODO(math)**: `AddCommGroup (HolomorphicOneForms X)` — pointwise
addition of 1-forms. -/
noncomputable instance : AddCommGroup (HolomorphicOneForms X) := sorry

/-- **TODO(math)**: ℂ-module structure via pointwise scalar multiplication. -/
noncomputable instance : Module ℂ (HolomorphicOneForms X) := sorry

/-- **TODO(math)**: topology from a norm on the finite-dimensional space. -/
noncomputable instance : TopologicalSpace (HolomorphicOneForms X) := sorry

end Instances

section Curve

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **TODO(math)**: on a compact connected complex 1-manifold,
the space of global holomorphic 1-forms is finite-dimensional.
Proof: finite-dimensionality of cohomology of coherent sheaves on a
compact complex manifold (Cartan–Serre). -/
noncomputable instance : FiniteDimensional ℂ (HolomorphicOneForms X) := sorry

end Curve

/-! ### Pullback of forms along a holomorphic map. -/

section Functoriality

variable {X Y Z : Type*}
  [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
  [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

/-- **TODO(math)**: pullback of a holomorphic 1-form along a holomorphic
map. In local coordinates, if `ω = f(w) dw` on `Y`, then
`g^*ω = f(g(z)) g'(z) dz` on `X`. -/
noncomputable def pullbackForm (g : X → Y) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    HolomorphicOneForms Y →L[ℂ] HolomorphicOneForms X := sorry

/-- **TODO(math)**: `pullbackForm id = id`. -/
theorem pullbackForm_id : pullbackForm (id : X → X) contMDiff_id =
    ContinuousLinearMap.id ℂ (HolomorphicOneForms X) := sorry

/-- **TODO(math)**: `pullbackForm (g ∘ f) = pullbackForm f ∘ pullbackForm g`.
(Contravariance.) -/
theorem pullbackForm_comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f)) :
    pullbackForm (g ∘ f) hgf =
      (pullbackForm f hf).comp (pullbackForm g hg) := sorry

end Functoriality

/-! ### Pushforward of forms under a proper holomorphic map between curves.

For a non-constant holomorphic map `f : X → Y` of compact Riemann
surfaces of degree `d`, pushforward of 1-forms exists and satisfies
`f_* ∘ f^* = d • id` (integration over fibres). For constant maps,
pushforward is zero. -/

section PushforwardCurve

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **TODO(math)**: pushforward of holomorphic 1-forms under a
holomorphic map of compact Riemann surfaces. In local coordinates near
a regular value `y`, with preimages `x_1, …, x_d`, we have
`f_* ω (y) = Σ_i ω(x_i) · (f'(x_i))⁻¹ dy`. For constant `f`, zero. -/
noncomputable def pushforwardForm (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForms X →L[ℂ] HolomorphicOneForms Y := sorry

/-- **TODO(math)**: the headline identity `f_* ∘ f^* = deg(f) • id` on
holomorphic 1-forms. This is the integration-over-fibres calculation.

This is the identity that, after dualizing to the Jacobian, gives the
challenge's `pushforward_pullback = deg • id`.

The natural number `d` here should be `ContMDiff.degree f hf` once that
is defined. -/
theorem pushforwardForm_pullbackForm_eq (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (d : ℕ) (P : HolomorphicOneForms Y) :
    pushforwardForm f hf (pullbackForm f hf P) = (d : ℂ) • P := sorry

end PushforwardCurve

end Jacobians
