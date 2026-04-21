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

end Jacobians.Montel
