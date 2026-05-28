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
import Mathlib.Topology.MetricSpace.Cover

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
noncomputable def ChartBallPath (anchor P Q : X) : ℝ → X := fun t =>
  (chartAt ℂ anchor).symm
    ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)

/-- The chart-ball-linear path at `t = 0` is `P`, when `P` is in the chart's source. -/
@[simp] lemma ChartBallPath.start (anchor P Q : X)
    (hP : P ∈ (chartAt ℂ anchor).source) :
    ChartBallPath anchor P Q 0 = P := by
  show (chartAt ℂ anchor).symm
      ((1 - ((0 : ℝ) : ℂ)) * (chartAt ℂ anchor) P
        + ((0 : ℝ) : ℂ) * (chartAt ℂ anchor) Q) = P
  simp [(chartAt ℂ anchor).left_inv hP]

/-- The chart-ball-linear path at `t = 1` is `Q`, when `Q` is in the chart's source. -/
@[simp] lemma ChartBallPath.finish (anchor P Q : X)
    (hQ : Q ∈ (chartAt ℂ anchor).source) :
    ChartBallPath anchor P Q 1 = Q := by
  show (chartAt ℂ anchor).symm
      ((1 - ((1 : ℝ) : ℂ)) * (chartAt ℂ anchor) P
        + ((1 : ℝ) : ℂ) * (chartAt ℂ anchor) Q) = Q
  simp [(chartAt ℂ anchor).left_inv hQ]

/-- The chart-ball-linear path is continuous on `[0,1]`, provided the
linear interpolation stays in the chart's open target. -/
lemma ChartBallPath.continuousOn (anchor P Q : X)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (t : ℂ)) * (chartAt ℂ anchor) P + (t : ℂ) * (chartAt ℂ anchor) Q)
        ∈ (chartAt ℂ anchor).target) :
    ContinuousOn (ChartBallPath anchor P Q) (Set.Icc 0 1) := by
  set c := chartAt ℂ anchor with hc_def
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

/-! ## Chart cover of a continuous path on a charted space

For any continuous `γ : ℝ → X` with `X` a `ChartedSpace ℂ X`, the image
`γ([0,1])` admits a finite subdivision of `[0,1]` into equal-length
sub-intervals such that each piece's image lies in a single chart source.
The proof is the standard Lebesgue-number-lemma argument applied to the
open cover of `[0,1]` by preimages of chart sources at each path point. -/

/-- **Chart cover existence (equidistant subdivision).** For any continuous
path `γ : ℝ → X` and any positive integer count, if `n` is large enough,
the equidistant subdivision `0 = 0/n, 1/n, ..., n/n = 1` has each piece
`γ([k/n, (k+1)/n])` contained in some chart source.

We package the existence as an `∃ n, ∃ x : Fin n → X, ...`, with `x k` the
"anchor" point of `X` whose chart covers the `k`-th piece. -/
theorem exists_chartCover (γ : ℝ → X) (hγ : Continuous γ) :
    ∃ (n : ℕ) (_hn : 0 < n) (x : Fin n → X),
      ∀ (k : Fin n) (s : ℝ),
        (k : ℝ) / n ≤ s → s ≤ ((k : ℝ) + 1) / n →
          γ s ∈ (chartAt ℂ (x k)).source := by
  -- The open cover of [0,1]: for each t ∈ [0,1], the preimage under γ of
  -- the chart source at γ(t).
  set s : Set ℝ := Set.Icc (0 : ℝ) 1 with hs_def
  set U : s → Set ℝ := fun t => γ ⁻¹' (chartAt ℂ (γ t.1)).source with hU_def
  have hU_open : ∀ t : s, IsOpen (U t) := fun t =>
    (chartAt ℂ (γ t.1)).open_source.preimage hγ
  have hU_cover : s ⊆ ⋃ t : s, U t := by
    intro t ht
    refine Set.mem_iUnion.mpr ⟨⟨t, ht⟩, ?_⟩
    exact mem_chart_source ℂ (γ t)
  -- Apply Lebesgue's number lemma.
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    lebesgue_number_lemma_of_metric isCompact_Icc hU_open hU_cover
  -- Pick n large enough that 1/n < δ.
  obtain ⟨n, hn_gt⟩ : ∃ n : ℕ, 1 / δ < (n : ℝ) := exists_nat_gt _
  have hn_pos : 0 < n := by
    have h1 : (0 : ℝ) < 1 / δ := by positivity
    have h2 : (0 : ℝ) < (n : ℝ) := lt_trans h1 hn_gt
    exact_mod_cast h2
  have hn : (1 : ℝ) / n < δ := by
    have hn_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
    rw [div_lt_iff₀ hn_R]
    have h := mul_lt_mul_of_pos_left hn_gt hδ_pos
    have h_simp : δ * (1 / δ) = 1 := by field_simp
    linarith
  -- For each k : Fin n, pick a chart-anchor.
  -- Use Lebesgue at the midpoint of [k/n, (k+1)/n].
  have key : ∀ k : Fin n, ∃ x : X, ∀ y : ℝ,
      (k : ℝ) / n ≤ y → y ≤ ((k : ℝ) + 1) / n → γ y ∈ (chartAt ℂ x).source := by
    intro k
    -- The midpoint m = ((2k + 1) / (2n)) lies in [0,1].
    set m : ℝ := ((k : ℝ) + 1/2) / n with hm_def
    have hm_mem : m ∈ s := by
      refine ⟨?_, ?_⟩
      · apply div_nonneg
        · have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
          linarith
        · exact Nat.cast_nonneg _
      · rw [hm_def, div_le_one (by exact_mod_cast hn_pos)]
        have hk : (k : ℝ) + 1 ≤ n := by
          have : (k.val + 1 : ℕ) ≤ n := k.isLt
          exact_mod_cast this
        linarith
    -- Apply Lebesgue at m.
    obtain ⟨t₀, ht₀⟩ := hδ m hm_mem
    refine ⟨γ t₀.1, fun y hy_low hy_high => ?_⟩
    -- y ∈ [k/n, (k+1)/n]. Show |y - m| < δ.
    apply ht₀
    show y ∈ Metric.ball m δ
    rw [Metric.mem_ball, Real.dist_eq]
    -- |y - m| ≤ 1/(2n) < δ/2 + ε ≤ δ
    have h_dist : |y - m| ≤ 1 / (2 * n) := by
      rw [abs_sub_le_iff]
      refine ⟨?_, ?_⟩
      · -- y - m ≤ 1/(2n): y ≤ (k+1)/n = m + 1/(2n).
        have : y - m ≤ ((k : ℝ) + 1) / n - ((k : ℝ) + 1/2) / n := by linarith
        have heq : ((k : ℝ) + 1) / n - ((k : ℝ) + 1/2) / n = 1 / (2 * n) := by
          field_simp
          ring
        linarith
      · -- m - y ≤ 1/(2n): y ≥ k/n = m - 1/(2n).
        have : m - y ≤ ((k : ℝ) + 1/2) / n - (k : ℝ) / n := by linarith
        have heq : ((k : ℝ) + 1/2) / n - (k : ℝ) / n = 1 / (2 * n) := by
          field_simp
          ring
        linarith
    have h1 : (1 : ℝ) / (2 * n) ≤ 1 / n := by
      apply div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hn_pos)
      have : (1 : ℝ) ≤ 2 := by norm_num
      have hnn : (0 : ℝ) < n := by exact_mod_cast hn_pos
      nlinarith
    linarith
  -- Use Classical.choice to extract a Fin n → X.
  classical
  refine ⟨n, hn_pos, fun k => (key k).choose, ?_⟩
  intro k y hy_low hy_high
  exact (key k).choose_spec y hy_low hy_high

end Jacobians
