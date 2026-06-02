/-
  A finite cover whose every set is a coordinate disk — the cover the Dolbeault → Čech forward
  operator (`dolbeaultToCechCocycle`) solves `∂̄` over.

  The abstract `FiniteCover` only knows its sets cover `X`; solving `∂̄u_i = g` on a whole cover set
  `U_i` needs `U_i` to be a *coordinate disk* (so `g` pulls back through the chart to a planar
  function on a Euclidean ball, where `DbarDiskCohomology.dbar_solvable_ball` applies). Solving on an
  abstractly simply-connected `U_i` would instead require uniformization, which Mathlib lacks.

  `ChartDiskCover` bundles a `FiniteCover` with, for each index, a chart center and radius witnessing
  that `U_i` is exactly the chart-preimage of a Euclidean ball. All existing `𝔘.cechH1 / cocycles1`
  machinery applies verbatim through `toFiniteCover`. Design doc: `docs/dolbeault_comparison_forward_plan.md`.
-/
import Jacobians.Dolbeault.CechComplex

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A **finite chart-disk cover**: a `FiniteCover` together with, for each index `i`, a chart
`center i` and `radius i` so that `U i` is exactly the chart-preimage of the coordinate ball
`ball (e i) (radius i) ⊆ ℂ` (with `e i = extChartAt 𝓘(ℝ,ℂ) (center i) (center i)` the chart
coordinate of the center). The chart `extChartAt 𝓘(ℝ,ℂ) (center i)` therefore restricts to a
biholomorphism `U i ≃ ball (e i) (radius i)`, which is what lets the forward operator solve `∂̄`
on the whole of `U i` via the planar disk solve. -/
structure ChartDiskCover (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] extends FiniteCover X where
  /-- The chart center of `U i`. -/
  center : ι → X
  /-- The coordinate radius of the disk `U i`. -/
  radius : ι → ℝ
  radius_pos : ∀ i, 0 < radius i
  /-- The coordinate ball lies inside the chart target, so the chart is a homeomorphism onto it. -/
  ball_subset_target : ∀ i,
    Metric.ball (extChartAt 𝓘(ℝ, ℂ) (center i) (center i)) (radius i)
      ⊆ (extChartAt 𝓘(ℝ, ℂ) (center i)).target
  /-- `U i` is exactly the chart-preimage of the coordinate ball. -/
  isDisk : ∀ i, ((U i : Opens X) : Set X)
      = (extChartAt 𝓘(ℝ, ℂ) (center i)) ⁻¹'
            Metric.ball (extChartAt 𝓘(ℝ, ℂ) (center i) (center i)) (radius i)
          ∩ (extChartAt 𝓘(ℝ, ℂ) (center i)).source

namespace ChartDiskCover

variable (𝔇 : ChartDiskCover X)

/-- `U i` is contained in the chart source of its center. -/
theorem subset_chart_source (i : 𝔇.ι) :
    ((𝔇.U i : Opens X) : Set X) ⊆ (extChartAt 𝓘(ℝ, ℂ) (𝔇.center i)).source := by
  rw [𝔇.isDisk i]; exact Set.inter_subset_right

/-- The center lies in its own disk `U i` (the chart coordinate of the center is the ball center,
and the radius is positive). -/
theorem center_mem (i : 𝔇.ι) : 𝔇.center i ∈ ((𝔇.U i : Opens X) : Set X) := by
  rw [𝔇.isDisk i]
  exact ⟨by simp only [Set.mem_preimage]; exact Metric.mem_ball_self (𝔇.radius_pos i),
    mem_extChartAt_source (𝔇.center i)⟩

end ChartDiskCover

end Jacobians.Dolbeault
