import Jacobians.Montel.Compactness
import Mathlib.Topology.VectorBundle.Basic

/-!
# Montel path — chart-transition estimate

The **chart-transition estimate** lifts per-chart inner-shrunkChart
precompactness (from `Jacobians/Montel/Compactness.lean` B.8) to
supNormK precompactness:

  `supNormK α ≤ M · sup_{x₀ ∈ chartCover} ‖localRepOnInnerShrunk α x₀‖_bcf`

where `M > 0` is a universal constant depending only on `X`'s chart
structure (not on α). This closes the final structural gap in Montel's
`exists_convergent_subseq_of_bounded` / `closedBall_isCompact`.

## Proof outline

For y ∈ chart source x₀ ∩ chart source x₀', the two chart-tangent-basis
vectors `e_{x₀}.symmL y 1` and `e_{x₀'}.symmL y 1` are both nonzero in
the 1-dim `T_y X`, hence proportional:
  `e_{x₀'}.symmL y 1 = c(y) · e_{x₀}.symmL y 1`
with `c(y) ≠ 0`. By ℂ-linearity of `α.toFun y`:
  `localRep α x₀' y = c(y) · localRep α x₀ y`
and hence `|localRep α x₀ y| = |localRep α x₀' y| / |c(y)|`.

The factor `c(y) = (coordChangeL ℂ e_{x₀'} e_{x₀} y) 1` is continuous
and nonzero on the overlap. On any compact subset of the overlap,
`1/|c(y)|` is bounded. Applying this at y ∈ shrunkChart x₀ ∩
innerShrunkChart x₀' (with x₀' chosen so y lies in the inner cover)
yields the estimate. Taking max over `chartCover × chartCover`
(finite) gives the uniform `M`.
-/

namespace Jacobians.Montel

open scoped Manifold ContDiff Topology
open Bundle Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The transition factor -/

/-- The chart-transition factor between two tangent-bundle trivializations,
evaluated at a point `y`. Equals `1` by convention if `y` is not in both
base sets. -/
noncomputable def chartTransitionFactor (x₀ x₀' y : X) : ℂ :=
  Trivialization.coordChangeL ℂ
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀')
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀) y 1

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- The chart-transition factor is nonzero (a CLE sends nonzero to nonzero). -/
theorem chartTransitionFactor_ne_zero (x₀ x₀' y : X) :
    chartTransitionFactor (X := X) x₀ x₀' y ≠ 0 := by
  unfold chartTransitionFactor
  intro hzero
  have : (1 : ℂ) = 0 := by
    have hinj := (Trivialization.coordChangeL ℂ
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀')
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀) y).injective
    apply hinj
    rw [hzero, ContinuousLinearEquiv.map_zero]
  exact one_ne_zero this

/-! ### Chart-transition relation for localRep -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- Key identity: `e.symmL y (c(y)) = e'.symmL y 1`, where
`c(y) = chartTransitionFactor x₀ x₀' y`, for y in both base sets. -/
theorem symmL_apply_chartTransitionFactor (x₀ x₀' y : X)
    (hy₀' : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet)
    (hy₀ : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y
      (chartTransitionFactor (X := X) x₀ x₀' y) =
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').symmL ℂ y 1 := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  set e' := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀'
  -- c(y) = (e ⟨y, e'.symm y 1⟩).2 = (e.linearEquivAt ℂ y hy₀) (e'.symm y 1).
  -- Apply e.symm on both sides: e.symm y (c(y)) = e'.symm y 1 (by inverse property).
  change e.symm y (chartTransitionFactor (X := X) x₀ x₀' y) = e'.symm y 1
  -- e.symm y c = (e.linearEquivAt ℂ y hy₀).symm c (by linearEquivAt_symm_apply).
  have h1 : e.symm y (chartTransitionFactor (X := X) x₀ x₀' y) =
      (e.linearEquivAt ℂ y hy₀).symm (chartTransitionFactor (X := X) x₀ x₀' y) := by
    rw [Trivialization.linearEquivAt_symm_apply]
  rw [h1]
  -- c = (e.linearEquivAt ℂ y hy₀) (e'.symm y 1) (from coordChangeL + linearEquivAt_apply).
  have h2 : chartTransitionFactor (X := X) x₀ x₀' y =
      (e.linearEquivAt ℂ y hy₀) (e'.symm y 1) := by
    unfold chartTransitionFactor
    rw [e'.coordChangeL_apply e ⟨hy₀', hy₀⟩ 1]
    rw [Trivialization.linearEquivAt_apply]
  rw [h2]
  -- (linEq).symm ∘ (linEq) = id on E y.
  exact (e.linearEquivAt ℂ y hy₀).left_inv (e'.symm y 1)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- Chart-transition relation for `localRep`:
`localRep α x₀' y = c(y) · localRep α x₀ y` with `c = chartTransitionFactor`. -/
theorem localRep_chart_transition
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ x₀' y : X)
    (hy₀' : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet)
    (hy₀ : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet) :
    localRep α x₀' y = chartTransitionFactor (X := X) x₀ x₀' y * localRep α x₀ y := by
  unfold localRep
  rw [← symmL_apply_chartTransitionFactor x₀ x₀' y hy₀' hy₀]
  -- Goal: α.toFun y (e.symmL y c) = c * α.toFun y (e.symmL y 1).
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  set c := chartTransitionFactor (X := X) x₀ x₀' y with hc_def
  -- e.symmL y c = c • e.symmL y 1 (by ℂ-linearity + c = c·1 in ℂ).
  have h : e.symmL ℂ y c = c • e.symmL ℂ y 1 := by
    have : (c : ℂ) = c • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    conv_lhs => rw [this]
    exact map_smul (e.symmL ℂ y) c 1
  rw [h, map_smul, smul_eq_mul]

/-! ### Continuity of the chart-transition factor -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- Continuity of `chartTransitionFactor` on the overlap of two base sets. -/
theorem continuousOn_chartTransitionFactor (x₀ x₀' : X) :
    ContinuousOn (chartTransitionFactor (X := X) x₀ x₀')
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet ∩
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet) := by
  unfold chartTransitionFactor
  -- continuousOn_coordChange gives continuity of y ↦ coordChangeL ℂ e' e y as a CLM
  have h := continuousOn_coordChange ℂ
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀')
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀)
  -- Apply at 1: composing with (evaluation at 1) preserves continuity.
  exact (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).continuous.comp_continuousOn h

/-! ### Pairwise chart-transition bound -/

omit [ConnectedSpace X] [Nonempty X] in
/-- **Pairwise bound**: for each chart pair `(x₀, x₀') ∈ chartCover²`, there's
a universal constant `M ≥ 0` such that for any α and any point y in the
overlap `shrunkChart x₀ ∩ innerShrunkChart x₀'`,
`‖localRep α x₀ y‖ ≤ M · ‖localRep α x₀' y‖`.

Proof: `1/‖chartTransitionFactor x₀ x₀' y‖` is continuous and bounded on
the compact overlap (since `c ≠ 0` there); take the sup as M. -/
theorem exists_pairwise_chart_transition_bound
    (x₀ x₀' : X) (hx₀ : x₀ ∈ (chartCover : Finset X))
    (hx₀' : x₀' ∈ (chartCover : Finset X)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
      (y : X), y ∈ shrunkChart (X := X) x₀ → y ∈ innerShrunkChart (X := X) x₀' →
        ‖localRep α x₀ y‖ ≤ M * ‖localRep α x₀' y‖ := by
  set K := shrunkChart (X := X) x₀ ∩ innerShrunkChart (X := X) x₀' with hK_def
  have hKcpt : IsCompact K :=
    (shrunkChart_isCompact x₀).inter_right (innerShrunkChart_isClosed x₀')
  -- K sits inside both base sets
  have hKbase_x₀' : K ⊆ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet := by
    intro y hy
    exact innerShrunkChart_subset_baseSet x₀' hx₀' hy.2
  have hKbase_x₀ : K ⊆ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
    intro y hy
    exact shrunkChart_subset_baseSet x₀ hx₀ hy.1
  have hKbase : K ⊆ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet ∩
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
    intro y hy; exact ⟨hKbase_x₀' hy, hKbase_x₀ hy⟩
  -- g(y) := 1 / ‖c(y)‖ is continuous on K (c is cont, nonzero on overlap ⊇ K).
  have hg_cont : ContinuousOn (fun y => 1 / ‖chartTransitionFactor (X := X) x₀ x₀' y‖) K := by
    apply ContinuousOn.div₀ continuousOn_const
    · exact ((continuousOn_chartTransitionFactor x₀ x₀').mono hKbase).norm
    · intro y _
      exact norm_ne_zero_iff.mpr (chartTransitionFactor_ne_zero x₀ x₀' y)
  -- Bounded above on K
  have hbdd : BddAbove ((fun y => 1 / ‖chartTransitionFactor (X := X) x₀ x₀' y‖) '' K) :=
    hKcpt.bddAbove_image hg_cont
  obtain ⟨M, hMub⟩ := hbdd
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro α y hy_shrunk hy_inner
  have hy_K : y ∈ K := ⟨hy_shrunk, hy_inner⟩
  have hy_base_x₀' : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀').baseSet :=
    hKbase_x₀' hy_K
  have hy_base_x₀ : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet :=
    hKbase_x₀ hy_K
  -- localRep α x₀' y = c(y) * localRep α x₀ y.
  have hrel := localRep_chart_transition α x₀ x₀' y hy_base_x₀' hy_base_x₀
  -- So localRep α x₀ y = localRep α x₀' y / c(y). |localRep α x₀ y| ≤ (1/|c|) · |localRep α x₀' y|.
  have hc_ne : chartTransitionFactor (X := X) x₀ x₀' y ≠ 0 :=
    chartTransitionFactor_ne_zero x₀ x₀' y
  have hrel' : localRep α x₀ y =
      localRep α x₀' y / chartTransitionFactor (X := X) x₀ x₀' y := by
    rw [eq_div_iff hc_ne, mul_comm]
    exact hrel.symm
  rw [hrel', norm_div]
  have hg_y : (1 : ℝ) / ‖chartTransitionFactor (X := X) x₀ x₀' y‖ ≤ M :=
    hMub ⟨y, hy_K, rfl⟩
  have hg_y' : (1 : ℝ) / ‖chartTransitionFactor (X := X) x₀ x₀' y‖ ≤ max M 0 :=
    le_trans hg_y (le_max_left _ _)
  have hnorm_pos : 0 < ‖chartTransitionFactor (X := X) x₀ x₀' y‖ :=
    norm_pos_iff.mpr hc_ne
  rw [div_eq_inv_mul]
  calc ‖chartTransitionFactor (X := X) x₀ x₀' y‖⁻¹ * ‖localRep α x₀' y‖
      = (1 / ‖chartTransitionFactor (X := X) x₀ x₀' y‖) * ‖localRep α x₀' y‖ := by
        rw [one_div]
    _ ≤ max M 0 * ‖localRep α x₀' y‖ := by
        apply mul_le_mul_of_nonneg_right hg_y' (norm_nonneg _)

end Jacobians.Montel
