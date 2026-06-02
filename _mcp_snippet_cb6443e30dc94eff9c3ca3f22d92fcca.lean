import Jacobians.Dolbeault.RealForms
import Jacobians.DbarDisk

open scoped Manifold ContDiff Bundle
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

theorem mfderiv_apply_eq_fderiv_pullback (u : SmoothCFunctions X) (x : X) (v : ℂ) :
    (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x : ℂ →L[ℝ] ℂ) v
      = fderiv ℝ (fun z => u ((extChartAt 𝓘(ℝ, ℂ) x).symm z)) (extChartAt 𝓘(ℝ, ℂ) x x) v := by
  have hu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x := (u.contMDiff x).mdifferentiableAt (by simp)
  have hmf : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x =
      fderiv ℝ (writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x ⇑u) (extChartAt 𝓘(ℝ, ℂ) x x) := by
    rw [hu.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  have hpull : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) x ⇑u
      = fun z => u ((extChartAt 𝓘(ℝ, ℂ) x).symm z) := by
    ext z; simp only [writtenInExtChartAt, Function.comp_apply]; rfl
  rw [hpull] at hmf
  exact congrArg (fun (L : ℂ →L[ℝ] ℂ) => L v) hmf

end Jacobians.Dolbeault
