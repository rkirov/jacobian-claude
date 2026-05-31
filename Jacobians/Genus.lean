import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Genus of a compact Riemann surface

Defined as the ℂ-dimension of global holomorphic 1-forms:
`genus X := Module.finrank ℂ (HolomorphicOneForms X)`.

This matches the analytic definition; with real content
(`FiniteDimensional ℂ (HOF X)` from Cartan–Serre) it agrees with the
topological definition `finrank ℤ (H₁(X, ℤ)) / 2` by Riemann–Roch /
Dolbeault.

The `HolomorphicOneForms` definition is inlined here (rather than
imported from `HolomorphicForms.lean`) to avoid a circular dependency:
`HolomorphicForms.lean` imports `Genus.lean`.
-/

namespace Jacobians

open scoped Manifold ContDiff Bundle

/-- The ℂ-vector space of global analytic sections of the cotangent bundle
of a compact connected complex 1-manifold.

Mathematically: global holomorphic 1-forms on `X`. Defined here (rather
than in `HolomorphicForms.lean`) so that `genus` below can refer to it. -/
def HolomorphicOneForms (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type _ :=
  ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
    (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)

section HOFInstances

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

noncomputable instance : AddCommGroup (HolomorphicOneForms X) :=
  inferInstanceAs (AddCommGroup
    (ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)))

noncomputable instance : Module ℂ (HolomorphicOneForms X) :=
  inferInstanceAs (Module ℂ
    (ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)))

end HOFInstances

end Jacobians

open scoped Manifold ContDiff

/-- The genus of a compact Riemann surface, defined as the ℂ-dimension of
global holomorphic 1-forms. Since `Module.finrank` returns `0` for
non-finite-dimensional modules, this is well-defined unconditionally;
the `FiniteDimensional ℂ (HolomorphicOneForms X)` instance (in
`HolomorphicForms.lean`, content-gated) is required for `genus` to be
the "right" number. -/
noncomputable def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ :=
  Module.finrank ℂ (Jacobians.HolomorphicOneForms X)

/-- A compact Riemann surface has genus 0 iff it is homeomorphic to the sphere.
This is the "anti-hack" constraint preventing `∀ X, genus X = 0`.

Classical result: a compact Riemann surface of genus 0 is homeomorphic to the
2-sphere. The standard route is Riemann–Roch (Forster §16): genus 0 ⇒ a
non-constant meromorphic function with a single simple pole ⇒ a degree-1 map
`X → ℙ¹`, which by the proper-map degree (§4.24) is a biholomorphism, so
`X ≃ ℙ¹ ≃ₜ S²`. (Alternatively the uniformization / Riemann mapping theorem,
Forster §27.) Mathlib has neither Riemann–Roch nor uniformization nor a
complex `ℙ¹`/Riemann-sphere manifold, so this is the most theory-deficient
remaining sorry. -/
lemma genus_eq_zero_iff_homeo {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  sorry
