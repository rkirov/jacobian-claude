/-
  Forster GTM 81 Lemma 14.6 — the chart-disk `leray` lift (the global Bott–Tu `(0,1)`-form route).

  This file discharges the single `leray`-field obligation of
  `ChartDiskCover.holomorphicCoboundaries` (`ChartDiskFinitenessComplete.lean`): given a SHRINKING
  cocycle `s : 𝔇.overlapData.Cshr` (`s_{ab} ∈ BddHol (Wov (a,b))`, holomorphic on the
  relatively-compact shrinking overlaps `Wov (a,b) = φ_a '' (V_a ∩ V_b)`) with `δ¹s = 0`, produce a
  holomorphic 0-cochain `η : C0Holo`, a holomorphic COVER cocycle `x : Ccov` (on the FULL ball
  overlaps `Uov`), with `s = δ⁰η + ρ x`.

  ## The route (reuse the proven global-form Dolbeault machinery — NO cross-chart `∂̄g_a` gluing)

  The earlier attempts tried to GLUE the per-chart `∂̄g_a` into a global form by hand.  Instead we BUILD
  the global `(0,1)`-form `ω̂` directly (Bott–Tu, exactly as the proven `cechToDolbeaultForm`
  globalization in `DolbeaultComparisonInverse`, but with the SHRINKING-level PoU `shrinkPoU` and the
  germ sections obtained from `s`'s `BddHol` components).  Then the PROVEN
  `ChartDiskCover.dolbeaultToCechCocycle` (per-disk `∂̄`-solve via the Cauchy transform on each ball,
  `DolbeaultComparisonProof`) takes `ω̂` to a germ Čech cocycle `x'` holomorphic on the FULL overlaps —
  this is the no-cutoff ball solve that the Montel cover cannot reach.

  STAGE A (`s → σ`).  Each `s_{ab} : BddHol (Wov (a,b))` is read back through chart `a` to a germ
  section `σ_{ab} ∈ OmegaDGerm 0 (V_a ⊓ V_b)` (`bddHolToOmegaDGerm_zero_image`), with `holoFn σ_{ab} x
  = s_{ab}.toFun (φ_a x)` on `V_a ∩ V_b`.  `δ¹s = 0` makes `σ` a germ cocycle on the shrinking cover.

  STAGE B (global form).  `ω̂ := ∑_{a,c} (ρ_a · holoFn σ_{ac}) • ∂̄ρ_c` with `ρ = shrinkPoU` — a global
  smooth `(0,1)`-form by the confining 3-case `tsupport` argument (mirrors `cechTerm`).

  (Further stages — the per-disk solve via `dolbeaultToCechCocycle`, the corrector `η`, and the final
  `s = δ⁰η + ρ x` identity — are wired below.)
-/
import Jacobians.Dolbeault.ChartDiskFinitenessComplete
import Jacobians.Dolbeault.GoodCover
import Jacobians.Dolbeault.ChartDiskLeray

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Metric Complex Filter

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace ChartDiskCover

variable (𝔇 : ChartDiskCover X)

/-! ## §A — The germ cocycle `σ` on the shrinking cover from a `Cshr` cocycle

`s_{ab} : BddHol (Wov (a,b))` lives on `Wov (a,b) = φ_a '' (V_a ∩ V_b) = φ_a '' (shrinkOpens a ⊓
shrinkOpens b)`.  We read it back through chart `a` to an `𝒪_0` germ section on `V_a ⊓ V_b`. -/

/-- `Wov (a,b)` is exactly the chart-`a` image of the open `shrinkOpens a ⊓ shrinkOpens b`. -/
theorem Wov_eq_chartImage_shrinkInter (a b : 𝔇.ι) :
    𝔇.Wov (a, b)
      = (chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X) : Set X) := by
  show (chartAt (H := ℂ) (𝔇.center a)) '' (𝔇.shrinkSet a ∩ 𝔇.shrinkSet b) = _
  congr 1

/-- `V_a ∩ V_b ⊆ (chartAt (center a)).source`. -/
theorem shrinkInter_subset_source (a b : 𝔇.ι) :
    ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X) : Set X) ⊆ (chartAt (H := ℂ) (𝔇.center a)).source := by
  intro x hx
  exact 𝔇.shrinkOpens_subset_source a hx.1

/-- The `BddHol` component `s_{ab}`, retyped to live on the exact chart image of `shrinkOpens a ⊓
shrinkOpens b` (which is `Wov (a,b)`), ready for `bddHolToOmegaDGerm_zero_image`. -/
noncomputable def shrinkBddHolRetype (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) :
    BddHol ((chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X) : Set X)) :=
  BddHol.restrictOpenCLM (𝔇.Wov_eq_chartImage_shrinkInter a b).ge (s (a, b))

theorem shrinkBddHolRetype_toFun_of_mem (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) {z : ℂ}
    (hz : z ∈ 𝔇.Wov (a, b)) :
    (𝔇.shrinkBddHolRetype s a b).toFun z = (s (a, b)).toFun z := by
  refine BddHol.restrictOpenCLM_toFun_of_mem _ _ ?_
  rw [← 𝔇.Wov_eq_chartImage_shrinkInter a b]; exact hz

/-- **The germ section `σ_{ab}` on `V_a ⊓ V_b`** read back from `s_{ab}` through chart `a`. -/
noncomputable def shrinkGerm (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) :
    ↥(OmegaDGerm (0 : Divisor X) (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b)) :=
  bddHolToOmegaDGerm_zero_image (y := 𝔇.center a) (V := 𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b)
    (𝔇.shrinkInter_subset_source a b) (𝔇.shrinkBddHolRetype s a b)

theorem shrinkGerm_mem (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) :
    (𝔇.shrinkGerm s a b).1 ∈ OmegaDGerm (0 : Divisor X) (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b) :=
  (𝔇.shrinkGerm s a b).2

/-- **The value of `holoFn σ_{ab}`** at `y ∈ V_a ∩ V_b` is `s_{ab}.toFun (φ_a y)`.  (Mirror of
`diagPullbackGerm_holoFn`.) -/
theorem shrinkGerm_holoFn (s : 𝔇.overlapData.Cshr) (a b : 𝔇.ι) {y : X}
    (hy : y ∈ (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X)) :
    holoFn (𝔇.shrinkGerm s a b).2 y = (s (a, b)).toFun ((chartAt (H := ℂ) (𝔇.center a)) y) := by
  set g' := 𝔇.shrinkBddHolRetype s a b with hg'
  set F : ↥(𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b) → ℂ :=
    fun x => g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) x.1) with hF
  have hgerm : toGerm (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b) F = (𝔇.shrinkGerm s a b).1 := rfl
  have hmemImg : (chartAt (H := ℂ) (𝔇.center a)) y
      ∈ (chartAt (H := ℂ) (𝔇.center a)) '' ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X) : Set X) :=
    ⟨y, hy, rfl⟩
  -- `g'.toFun (φ_a y) = s_{ab}.toFun (φ_a y)` (`shrinkBddHolRetype` agrees on `Wov`).
  have hzW : (chartAt (H := ℂ) (𝔇.center a)) y ∈ 𝔇.Wov (a, b) := by
    rw [𝔇.Wov_eq_chartImage_shrinkInter a b]; exact hmemImg
  have hval : g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) y)
      = (s (a, b)).toFun ((chartAt (H := ℂ) (𝔇.center a)) y) :=
    𝔇.shrinkBddHolRetype_toFun_of_mem s a b hzW
  -- `Gext F` is continuous at `y` (analytic `g'` ∘ chart), agreeing with `F`-value near `y`.
  have hcont : ContinuousAt (fun z : X => g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) z)) y := by
    refine (g'.analyticOn.continuousOn.continuousAt ?_).comp
      ((chartAt (H := ℂ) (𝔇.center a)).continuousAt (𝔇.shrinkInter_subset_source a b hy))
    exact ((chartAt (H := ℂ) (𝔇.center a)).isOpen_image_of_subset_source
      (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b).isOpen (𝔇.shrinkInter_subset_source a b)).mem_nhds hmemImg
  have hev : Gext F =ᶠ[nhds y]
      (fun z : X => g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) z)) := by
    filter_upwards [(𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b).isOpen.mem_nhds hy] with z hz
    rw [Gext_apply_mem F hz]
  have htend : Filter.Tendsto (Gext F) (𝓝[≠] y)
      (𝓝 (g'.toFun ((chartAt (H := ℂ) (𝔇.center a)) y))) :=
    Filter.Tendsto.congr' (hev.filter_mono nhdsWithin_le_nhds).symm
      ((hcont.tendsto).mono_left nhdsWithin_le_nhds)
  rw [← hval]
  exact holoFn_eq_of_tendsto (𝔇.shrinkGerm s a b).2 F hgerm hy htend

/-- `chart_i y ∈ WovTriple (i,j,k)` for `y ∈ V_i ∩ V_j ∩ V_k`. -/
theorem chart_mem_WovTriple (i j k : 𝔇.ι) {y : X}
    (hy : y ∈ (𝔇.shrinkOpens i ⊓ 𝔇.shrinkOpens j ⊓ 𝔇.shrinkOpens k : Opens X)) :
    (chartAt (H := ℂ) (𝔇.center i)) y ∈ 𝔇.WovTriple (i, j, k) :=
  ⟨y, ⟨⟨hy.1.1, hy.1.2⟩, hy.2⟩, rfl⟩

/-- For `y ∈ V_i ∩ V_j ⊆ V_i ∩ V_j`, the transition point identity `(chart_j).symm (τ_{ij}(chart_i y))
= ...` collapses: `τ_{ij}(chart_i y) = chart_j y`. -/
theorem coverTransition_chart_shrink (i j : 𝔇.ι) {y : X}
    (hyi : y ∈ (𝔇.shrinkOpens i : Opens X)) (hyj : y ∈ (𝔇.shrinkOpens j : Opens X)) :
    𝔇.coverTransition i j ((chartAt (H := ℂ) (𝔇.center i)) y) = (chartAt (H := ℂ) (𝔇.center j)) y := by
  have hyiU : y ∈ ((𝔇.U i : Opens X) : Set X) := 𝔇.shrinkOpens_le_U i hyi
  have hyjU : y ∈ ((𝔇.U j : Opens X) : Set X) := 𝔇.shrinkOpens_le_U j hyj
  exact 𝔇.coverTransition_apply i j ⟨hyiU, hyjU⟩

/-- **The germ cocycle relation at the `holoFn` value level.**  For a `Cshr` cocycle `s` (i.e.
`δ¹s = 0`) and `y ∈ V_i ∩ V_j ∩ V_k`, `holoFn σ_{ik} y = holoFn σ_{ij} y + holoFn σ_{jk} y`.  Direct
from `delta1Model s = 0` evaluated at `chart_i y ∈ WovTriple (i,j,k)`, via `shrinkGerm_holoFn` and the
transition identity. -/
theorem shrinkGerm_cocycle_add (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0)
    (i j k : 𝔇.ι) {y : X} (hy : y ∈ (𝔇.shrinkOpens i ⊓ 𝔇.shrinkOpens j ⊓ 𝔇.shrinkOpens k : Opens X)) :
    holoFn (𝔇.shrinkGerm s i k).2 y
      = holoFn (𝔇.shrinkGerm s i j).2 y + holoFn (𝔇.shrinkGerm s j k).2 y := by
  have hyi : y ∈ (𝔇.shrinkOpens i : Opens X) := hy.1.1
  have hyj : y ∈ (𝔇.shrinkOpens j : Opens X) := hy.1.2
  have hyk : y ∈ (𝔇.shrinkOpens k : Opens X) := hy.2
  set z := (chartAt (H := ℂ) (𝔇.center i)) y with hz
  have hzW : z ∈ 𝔇.WovTriple (i, j, k) := 𝔇.chart_mem_WovTriple i j k hy
  -- `δ¹s = 0` value at `z`.
  have h0 : (𝔇.delta1Model s (i, j, k)).toFun z = 0 := by rw [hs]; rfl
  rw [𝔇.delta1Model_apply_apply s (i, j, k) hzW] at h0
  -- rewrite `s` components into `holoFn σ` via `shrinkGerm_holoFn` and the transition identity.
  rw [show 𝔇.coverTransition (i, j, k).1 (i, j, k).2.1 z = (chartAt (H := ℂ) (𝔇.center j)) y from
    𝔇.coverTransition_chart_shrink i j hyi hyj] at h0
  rw [← 𝔇.shrinkGerm_holoFn s i k ⟨hyi, hyk⟩,
    ← 𝔇.shrinkGerm_holoFn s i j ⟨hyi, hyj⟩, ← 𝔇.shrinkGerm_holoFn s j k ⟨hyj, hyk⟩] at h0
  linear_combination -h0

/-- `holoFn σ_{ii} y = 0` on `V_i` (diagonal vanishing).  From the cocycle relation with `j = k = i`:
`holoFn σ_{ii} = holoFn σ_{ii} + holoFn σ_{ii}`. -/
theorem shrinkGerm_diag_eq_zero (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0)
    (i : 𝔇.ι) {y : X} (hy : y ∈ (𝔇.shrinkOpens i : Opens X)) :
    holoFn (𝔇.shrinkGerm s i i).2 y = 0 := by
  have h := 𝔇.shrinkGerm_cocycle_add s hs i i i (y := y) ⟨⟨hy, hy⟩, hy⟩
  linear_combination -h

end ChartDiskCover

end Jacobians.Dolbeault
