import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# Genus of a compact Riemann surface

Factored out of the challenge file `Jacobians.lean` so that content files
(`HolomorphicForms.lean`, `FormsToJacobian.lean`) can depend on `genus`
without a circular dependency.

The definition remains `sorry` — content. See `docs/recon.md` and
`docs/REFERENCES.md` for the math (topological definition:
`finrank ℤ (H₁(X, ℤ)) / 2`, equivalently half the first Betti number).
-/

open scoped Manifold ContDiff

/-- The genus of a compact Riemann surface. -/
def genus (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : ℕ := sorry

/-- A compact Riemann surface has genus 0 iff it is homeomorphic to the sphere.
This is the "anti-hack" constraint preventing `∀ X, genus X = 0`. -/
lemma genus_eq_zero_iff_homeo {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  sorry
