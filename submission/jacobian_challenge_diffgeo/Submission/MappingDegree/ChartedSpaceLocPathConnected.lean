/-
Copyright (c) 2026 Jacobian Lean Challenge contributors. All rights reserved.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Geometry.Manifold.ChartedSpace

/-! # Local path-connectedness of spaces charted on `ℂ`

Registers `LocPathConnectedSpace` for `ℂ` and for any topological space
charted on `ℂ`. Mathlib provides
`LocallyConvexSpace.toLocPathConnectedSpace` for real locally convex spaces
and `ChartedSpace.locPathConnectedSpace` to lift across charts; this file
wires them together for `ℂ` so downstream files can use `inferInstance`. -/

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
