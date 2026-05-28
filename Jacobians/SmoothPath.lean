/-
Foundations for the smooth-path construction (wall 6).

This file is being built across multiple sessions. The end goal is to close
the four open sorries in `PeriodLattice.lean:259,262,293` and
`Jacobians.lean:162` (`smoothPath`, `isSmoothPath_smoothPath`,
`smoothPath_basepoint_change`, `ofCurve_contMDiff`).

The construction is the classical Forster §§1–2 chart-cover + partition-of-
unity argument, but our `IsSmoothPath` only requires C^1 pieces (the `diff`
field is `DifferentiableAt ℝ ...`, not `ContMDiff … ω …`), so we can use C^1
smoothstep transitions at chart junctions rather than full partition-of-
unity.

## Session 1 (this file): foundations

* `ChartBallPath P Q hP hQ hb` — chart-ball-linear interpolation between
  `P, Q : X` whose chart-images `c P, c Q` lie in a common open ball
  `Metric.ball z₀ r ⊆ c.target` (where `c := chartAt ℂ P`). Linear in chart
  coordinates, hence stays inside the ball.

* `ChartBallPath.continuous`, `ChartBallPath.start`, `ChartBallPath.finish`
  — basic boundary/continuity properties.

## Future sessions

* Show that any continuous `Path P Q` in compact `X` can be subdivided into
  finitely many chart-ball-local sub-paths (chart-cover lemma).
* Define the global `smoothPath` by piecewise replacement with chart-ball
  paths and C^1 smoothstep gluing.
* Prove `IsSmoothPath` for the global construction.
* Prove `smoothPath_basepoint_change` via `periodVec_concat`.
* Prove joint smoothness for `ofCurve_contMDiff`.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Connected.LocPathConnected
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace Jacobians

open scoped Manifold ContDiff Topology

universe u

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]

/-! ## Chart-ball-local linear path

Given `P, Q : X` both in some `chartAt ℂ P`-source, AND with chart-images
`c P, c Q` both inside a common open ball `Metric.ball z₀ r` contained in
the chart target, the chart-coords linear interpolation
`t ↦ (1 - (t : ℂ)) * c P + (t : ℂ) * c Q` stays in the ball (balls are convex), hence in
the chart target, hence pulls back via `c.symm` to a path in `X`.
-/

/-- **Chart-ball-linear path.** Linear interpolation in the chart at `P`,
pulled back to `X`. Pre-conditions are not encoded in the type; the
auxiliary lemmas below assume `P ∈ c.source`, `Q ∈ c.source`, and that the
linear interpolation `(1 - (t : ℂ)) * c P + (t : ℂ) * c Q` stays in `c.target` for
`t ∈ [0,1]` (any convex subset of `c.target` containing `c P` and `c Q`
suffices). -/
noncomputable def ChartBallPath (P Q : X) : ℝ → X := fun t =>
  let c := chartAt ℂ P
  c.symm ((1 - (t : ℂ)) * c P + (t : ℂ) * c Q)

/-- The chart-ball-linear path at `t = 0` is `P`. -/
@[simp] lemma ChartBallPath.start (P Q : X) (hP : P ∈ (chartAt ℂ P).source) :
    ChartBallPath P Q 0 = P := by
  show (chartAt ℂ P).symm
      ((1 - ((0 : ℝ) : ℂ)) * (chartAt ℂ P) P + ((0 : ℝ) : ℂ) * (chartAt ℂ P) Q) = P
  simp [(chartAt ℂ P).left_inv hP]

/-- The chart-ball-linear path at `t = 1` is `Q`, provided `Q ∈ c.source`. -/
@[simp] lemma ChartBallPath.finish (P Q : X) (hQ : Q ∈ (chartAt ℂ P).source) :
    ChartBallPath P Q 1 = Q := by
  show (chartAt ℂ P).symm
      ((1 - ((1 : ℝ) : ℂ)) * (chartAt ℂ P) P + ((1 : ℝ) : ℂ) * (chartAt ℂ P) Q) = Q
  simp [(chartAt ℂ P).left_inv hQ]

/-- The chart-ball-linear path is continuous on `[0,1]`, provided the
linear interpolation stays in the chart's open target. -/
lemma ChartBallPath.continuousOn (P Q : X)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (t : ℂ)) * (chartAt ℂ P) P + (t : ℂ) * (chartAt ℂ P) Q) ∈ (chartAt ℂ P).target) :
    ContinuousOn (ChartBallPath P Q) (Set.Icc 0 1) := by
  set c := chartAt ℂ P with hc_def
  unfold ChartBallPath
  -- The linear interpolation is continuous as a map ℝ → ℂ.
  have h_lin_cont : Continuous (fun t : ℝ => (1 - (t : ℂ)) * c P + (t : ℂ) * c Q) := by
    refine Continuous.add ?_ ?_
    · exact (continuous_const.sub Complex.continuous_ofReal).mul continuous_const
    · exact Complex.continuous_ofReal.mul continuous_const
  -- Compose with the inverse chart, which is continuous on its target.
  have h_inv_cont : ContinuousOn c.symm c.target := c.continuousOn_invFun
  -- Composition.
  exact h_inv_cont.comp h_lin_cont.continuousOn h

end Jacobians
