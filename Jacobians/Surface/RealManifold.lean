import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic

open scoped Manifold ContDiff

namespace Jacobians.Dolbeault

set_option backward.isDefEq.respectTransparency false in
/-- **A complex manifold is a real-`C^∞` manifold.** Holomorphic chart transitions are real-smooth,
so the ℂ-atlas is a `𝓘(ℝ,ℂ)`-smooth atlas. This is the foundational layer for real Dolbeault. -/
instance realManifold_of_complex {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : IsManifold (𝓘(ℝ, ℂ)) (⊤ : ℕ∞) X := by
  have hle : contDiffGroupoid ω 𝓘(ℂ) ≤ contDiffGroupoid (⊤ : ℕ∞) (𝓘(ℝ, ℂ)) := by
    intro e he
    have he' : e ∈ contDiffGroupoid ω 𝓘(ℂ) := he
    show e ∈ contDiffGroupoid (⊤ : ℕ∞) (𝓘(ℝ, ℂ))
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at he' ⊢
    simp only [contDiffPregroupoid] at he' ⊢
    obtain ⟨h1, h2⟩ := he'
    refine ⟨?_, ?_⟩
    · have key : ContDiffOn ℝ (⊤ : ℕ∞) _ _ := (h1.of_le le_top).restrict_scalars ℝ
      convert key using 2
    · have key : ContDiffOn ℝ (⊤ : ℕ∞) _ _ := (h2.of_le le_top).restrict_scalars ℝ
      convert key using 2
  haveI : HasGroupoid X (contDiffGroupoid (⊤ : ℕ∞) (𝓘(ℝ, ℂ))) :=
    hasGroupoid_of_le ‹IsManifold 𝓘(ℂ) ω X›.toHasGroupoid hle
  exact IsManifold.mk' _ _ _

end Jacobians.Dolbeault
