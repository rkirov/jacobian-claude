import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Complex.Basic

namespace Jacobians.Discharge.Manifold

/-- `ℂ`, viewed as an ℝ-normed space, is locally path-connected. -/
instance instLocPathConnectedSpace_complex : LocPathConnectedSpace ℂ :=
  inferInstance

/-- Any topological space charted on `ℂ` is locally path-connected. -/
theorem locPathConnectedSpace_of_chartedSpace_complex
    {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y] :
    LocPathConnectedSpace Y :=
  ChartedSpace.locPathConnectedSpace ℂ Y

end Jacobians.Discharge.Manifold
