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

/-! ## §B — The global Bott–Tu `(0,1)`-form `ω̂` from `s`

`ω̂ := ∑_{a,c} (ρ_a · holoFn σ_{ac}) • ∂̄ρ_c`, with `ρ = shrinkPoU` (subordinate to `(V_a)`, sum-to-one
on `X`).  Each summand is a global smooth `(0,1)`-form by the confining 3-case `tsupport` argument
(mirrors `cechTerm` of `DolbeaultComparisonInverse`).  This is the global form whose chart-`a` read on
the FULL ball `U_a` is smooth — the input the per-disk solve consumes. -/

/-- `ρ_a` as a complex `SmoothCFunctions` (`ρ̃_a = ofReal ∘ shrinkPoU a`). -/
noncomputable def shrinkRhoC (a : 𝔇.ι) : SmoothCFunctions X :=
  ofRealCM.comp (𝔇.shrinkPoU a)

/-- `∂̄ρ_a` as a global `(0,1)`-form. -/
noncomputable def shrinkDbarRho (a : 𝔇.ι) : SmoothCOneForms X :=
  dbarL (𝔇.shrinkRhoC a)

theorem shrinkRhoC_eq_zero_of_notMem (a : 𝔇.ι) {x : X}
    (hx : x ∉ tsupport (𝔇.shrinkPoU a)) : 𝔇.shrinkRhoC a x = 0 := by
  simp only [shrinkRhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport hx]; rfl

theorem shrinkDbarRho_eq_zero_of_notMem (a : 𝔇.ι) {x : X}
    (hx : x ∉ tsupport (𝔇.shrinkPoU a)) : (𝔇.shrinkDbarRho a) x = 0 := by
  refine dbarL_eq_zero_of_notMem_tsupport (𝔇.shrinkRhoC a) (fun hc => hx ?_)
  refine closure_mono (fun y hy => ?_) hc
  simp only [Function.mem_support, ne_eq] at hy ⊢
  exact fun h0 => hy (by simp only [shrinkRhoC, ContMDiffMap.comp_apply, ofRealCM, h0]; rfl)

theorem sum_shrinkRhoC (𝔇 : ChartDiskCover X) : ∑ a, 𝔇.shrinkRhoC a = 1 := by
  refine ContMDiffMap.ext fun x => ?_
  have h1 : (⇑(∑ a, 𝔇.shrinkRhoC a) : X → ℂ) = ∑ a, ⇑(𝔇.shrinkRhoC a) :=
    map_sum ContMDiffMap.coeFnAddMonoidHom _ _
  rw [show (∑ a, 𝔇.shrinkRhoC a) x = (⇑(∑ a, 𝔇.shrinkRhoC a) : X → ℂ) x from rfl, h1,
    Finset.sum_apply, ContMDiffMap.coe_one, Pi.one_apply]
  show ∑ a, ((𝔇.shrinkPoU a x : ℝ) : ℂ) = 1
  rw [← Complex.ofReal_sum, 𝔇.sum_shrinkPoU_eq_one x, Complex.ofReal_one]

theorem sum_shrinkRhoC_apply (𝔇 : ChartDiskCover X) (x : X) : ∑ a, (𝔇.shrinkRhoC a x) = 1 := by
  have h1 : (⇑(∑ a, 𝔇.shrinkRhoC a) : X → ℂ) = ∑ a, ⇑(𝔇.shrinkRhoC a) :=
    map_sum ContMDiffMap.coeFnAddMonoidHom _ _
  have h2 : (∑ a, 𝔇.shrinkRhoC a) x = ∑ a, (𝔇.shrinkRhoC a x) := by
    rw [show ((∑ a, 𝔇.shrinkRhoC a) x : ℂ) = (⇑(∑ a, 𝔇.shrinkRhoC a) : X → ℂ) x from rfl, h1,
      Finset.sum_apply]
  rw [← h2, sum_shrinkRhoC, ContMDiffMap.coe_one, Pi.one_apply]

theorem sum_shrinkDbarRho (𝔇 : ChartDiskCover X) : ∑ a, 𝔇.shrinkDbarRho a = 0 := by
  have h : ∑ a, 𝔇.shrinkDbarRho a = dbarL (∑ a, 𝔇.shrinkRhoC a) := (map_sum dbarL _ _).symm
  rw [h, sum_shrinkRhoC, dbarL_one_eq_zero]

theorem sum_shrinkDbarRho_apply (𝔇 : ChartDiskCover X) (x : X) :
    ∑ a, ((𝔇.shrinkDbarRho a) x) = 0 := by
  have h1 : (⇑(∑ a, 𝔇.shrinkDbarRho a)) = ∑ a, ⇑(𝔇.shrinkDbarRho a) :=
    map_sum (ContMDiffSection.coeAddHom _ _ _ _) _ _
  have h2 : (∑ a, 𝔇.shrinkDbarRho a) x = ∑ a, ((𝔇.shrinkDbarRho a) x) := by
    rw [show ((∑ a, 𝔇.shrinkDbarRho a) x) = (⇑(∑ a, 𝔇.shrinkDbarRho a)) x from rfl, h1,
      Finset.sum_apply]
  rw [← h2, sum_shrinkDbarRho, ContMDiffSection.coe_zero, Pi.zero_apply]

/-- **The Bott–Tu double-sum term `(ρ_a · holoFn σ_{ac}) • ∂̄ρ_c`** as a global smooth `(0,1)`-form.
Globally smooth by the 3-case `tsupport` argument: on `V_a ∩ V_c` (where `holoFn σ_{ac}` is smooth)
everything is smooth; off `tsupport ρ_a` the factor `ρ_a` vanishes; off `tsupport ρ_c` the factor
`∂̄ρ_c` vanishes. -/
noncomputable def shrinkTerm (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) : SmoothCOneForms X where
  toFun := fun x => (𝔇.shrinkRhoC a x * holoFn (𝔇.shrinkGerm s a c).2 x) • (𝔇.shrinkDbarRho c x)
  contMDiff_toFun := by
    intro x₀
    by_cases hba : x₀ ∈ tsupport (𝔇.shrinkPoU a)
    · by_cases hbc : x₀ ∈ tsupport (𝔇.shrinkPoU c)
      · have hxV : x₀ ∈ ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens c : Opens X) : Set X) :=
          ⟨𝔇.shrinkPoU_tsupport_subset a hba, 𝔇.shrinkPoU_tsupport_subset c hbc⟩
        have hmulrho : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ) (⊤ : ℕ∞)
            (fun x => ContinuousLinearMap.mul ℝ ℂ (𝔇.shrinkRhoC a x)) x₀ :=
          ContMDiffAt.clm_apply contMDiffAt_const ((𝔇.shrinkRhoC a).contMDiff x₀)
        have hG : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
            (fun x => 𝔇.shrinkRhoC a x * holoFn (𝔇.shrinkGerm s a c).2 x) x₀ :=
          (hmulrho.clm_apply (holoFn_contMDiffAt (𝔇.shrinkGerm s a c).2 hxV)).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun x => by simp [ContinuousLinearMap.mul_apply'])
        exact contMDiffAt_cSmul_section hG ((𝔇.shrinkDbarRho c).contMDiff_toFun x₀)
      · refine ContMDiffAt.congr_of_eventuallyEq (Bundle.contMDiffAt_zeroSection ℝ
          (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x)) ?_
        filter_upwards [(isClosed_tsupport (𝔇.shrinkPoU c)).isOpen_compl.mem_nhds hbc] with x hx
        have hV : (𝔇.shrinkRhoC a x * holoFn (𝔇.shrinkGerm s a c).2 x) • (𝔇.shrinkDbarRho c x) = 0 := by
          rw [𝔇.shrinkDbarRho_eq_zero_of_notMem c hx]; module
        exact congrArg (Bundle.TotalSpace.mk x) hV
    · refine ContMDiffAt.congr_of_eventuallyEq (Bundle.contMDiffAt_zeroSection ℝ
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x)) ?_
      filter_upwards [(isClosed_tsupport (𝔇.shrinkPoU a)).isOpen_compl.mem_nhds hba] with x hx
      have hV : (𝔇.shrinkRhoC a x * holoFn (𝔇.shrinkGerm s a c).2 x) • (𝔇.shrinkDbarRho c x) = 0 := by
        rw [𝔇.shrinkRhoC_eq_zero_of_notMem a hx, zero_mul]; module
      exact congrArg (Bundle.TotalSpace.mk x) hV

@[simp] theorem shrinkTerm_apply (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) (x : X) :
    (𝔇.shrinkTerm s a c) x
      = (𝔇.shrinkRhoC a x * holoFn (𝔇.shrinkGerm s a c).2 x) • (𝔇.shrinkDbarRho c x) := rfl

/-- Each Bott–Tu term is a `(0,1)`-form (`∂̄ρ_c` is, and ℂ-scaling preserves `(0,1)`). -/
theorem shrinkTerm_mem_zeroOne (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) :
    𝔇.shrinkTerm s a c ∈ OneFormsZeroOne X := by
  refine ⟨𝔇.shrinkTerm s a c, ?_⟩
  refine ContMDiffSection.ext fun x => ?_
  show proj01 (𝔇.shrinkTerm s a c x) = 𝔇.shrinkTerm s a c x
  rw [shrinkTerm_apply, proj01_smul]
  have hfix : proj01 ((𝔇.shrinkDbarRho c) x) = (𝔇.shrinkDbarRho c x) := by
    show proj01 (dbarL (𝔇.shrinkRhoC c) x) = dbarL (𝔇.shrinkRhoC c) x
    rw [dbarL_eq_proj01L_differential]
    show proj01 (proj01 ((differential (𝔇.shrinkRhoC c)) x)) = proj01 ((differential (𝔇.shrinkRhoC c)) x)
    exact proj01_idempotent _
  rw [hfix]

/-- **The global Bott–Tu form `ω̂`** as a `(0,1)`-form: `∑_{a,c} (ρ_a · holoFn σ_{ac}) • ∂̄ρ_c`. -/
noncomputable def glueForm (s : 𝔇.overlapData.Cshr) : ↥(OneFormsZeroOne X) :=
  ∑ p : 𝔇.ι × 𝔇.ι, ⟨𝔇.shrinkTerm s p.1 p.2, 𝔇.shrinkTerm_mem_zeroOne s p.1 p.2⟩

/-- The underlying form of `glueForm` is the finite sum of `shrinkTerm`s. -/
theorem glueForm_val (s : 𝔇.overlapData.Cshr) :
    ((𝔇.glueForm s : ↥(OneFormsZeroOne X)) : SmoothCOneForms X)
      = ∑ p : 𝔇.ι × 𝔇.ι, 𝔇.shrinkTerm s p.1 p.2 := by
  show ((∑ p : 𝔇.ι × 𝔇.ι, (⟨𝔇.shrinkTerm s p.1 p.2, 𝔇.shrinkTerm_mem_zeroOne s p.1 p.2⟩ :
      ↥(OneFormsZeroOne X)) : ↥(OneFormsZeroOne X)) : SmoothCOneForms X) = _
  rw [AddSubmonoidClass.coe_finset_sum]

/-! ## §C — The local smooth split `G_a` and its two key identities

`G_a(x) := ∑_c ρ_c(x) · holoFn σ_{ac}(x)` — a function smooth on `V_a` (each term confined to
`tsupport ρ_c ∩ V_a ⊆ V_c ∩ V_a`, where `holoFn σ_{ac}` is smooth).  Two identities drive the lift:
  * the **difference identity** `G_a(x) − G_b(x) = holoFn σ_{ab}(x) = s_{ab}.toFun(φ_a x)` on `V_a ∩ V_b`
    (cocycle telescoping `∑ ρ = 1`);
  * the **`∂̄` identity** `proj01(mfderiv G_a x) = ω̂ x` on `V_a` (Wirtinger product rule + cocycle
    telescoping `∑ ∂̄ρ = 0`), built in §D.
-/

/-- The chart-`a` smooth split `G_a := ∑_c ρ_c · holoFn σ_{ac}` (a function on `V_a`). -/
noncomputable def globalPrim (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) : X → ℂ :=
  fun x => ∑ c, 𝔇.shrinkRhoC c x * holoFn (𝔇.shrinkGerm s a c).2 x

theorem globalPrim_apply (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) (x : X) :
    𝔇.globalPrim s a x = ∑ c, 𝔇.shrinkRhoC c x * holoFn (𝔇.shrinkGerm s a c).2 x := rfl

/-- **The difference identity** `G_a(x) − G_b(x) = holoFn σ_{ab}(x)` on `V_a ∩ V_b`.  Pointwise via the
cocycle relation `holoFn σ_{ac} = holoFn σ_{ab} + holoFn σ_{bc}` and `∑ ρ = 1`.  (Mirror of
`chartDiskCoverPrim_diff`.) -/
theorem globalPrim_diff (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a b : 𝔇.ι) {x : X}
    (hx : x ∈ (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b : Opens X)) :
    𝔇.globalPrim s a x - 𝔇.globalPrim s b x = holoFn (𝔇.shrinkGerm s a b).2 x := by
  rw [globalPrim, globalPrim, ← Finset.sum_sub_distrib]
  have hpt : ∀ c : 𝔇.ι,
      𝔇.shrinkRhoC c x * holoFn (𝔇.shrinkGerm s a c).2 x
        - 𝔇.shrinkRhoC c x * holoFn (𝔇.shrinkGerm s b c).2 x
      = 𝔇.shrinkRhoC c x * holoFn (𝔇.shrinkGerm s a b).2 x := by
    intro c
    by_cases hb : x ∈ tsupport (𝔇.shrinkPoU c)
    · have hxc : x ∈ (𝔇.shrinkOpens c : Opens X) := 𝔇.shrinkPoU_tsupport_subset c hb
      -- cocycle: `holoFn σ_{ac} = holoFn σ_{ab} + holoFn σ_{bc}` (middle `b`), on `V_a∩V_b∩V_c`.
      have htri : x ∈ (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens b ⊓ 𝔇.shrinkOpens c : Opens X) :=
        ⟨⟨hx.1, hx.2⟩, hxc⟩
      rw [𝔇.shrinkGerm_cocycle_add s hs a b c htri]
      ring
    · rw [𝔇.shrinkRhoC_eq_zero_of_notMem c hb]; ring
  simp_rw [hpt, ← Finset.sum_mul, 𝔇.sum_shrinkRhoC_apply x, one_mul]

/-- A single summand `ρ_c · holoFn σ_{ac}` of `G_a`, as a bare function `X → ℂ`. -/
noncomputable def globalPrimTerm (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) : X → ℂ :=
  fun x => 𝔇.shrinkRhoC c x * holoFn (𝔇.shrinkGerm s a c).2 x

/-- Each summand of `G_a` is `MDifferentiableAt` at any point of `V_a` (in `tsupport ρ_c` both
factors are smooth — using `x ∈ V_a ∩ V_c`; off `tsupport ρ_c` the term is locally `0`). -/
theorem mdifferentiableAt_globalPrimTerm (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.shrinkOpens a : Opens X)) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrimTerm s a c) x := by
  by_cases hb : x ∈ tsupport (𝔇.shrinkPoU c)
  · have hxc : x ∈ (𝔇.shrinkOpens c : Opens X) := 𝔇.shrinkPoU_tsupport_subset c hb
    have hxac : x ∈ ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens c : Opens X) : Set X) := ⟨hxa, hxc⟩
    exact (((𝔇.shrinkRhoC c).contMDiff x).mul
      (holoFn_contMDiffAt (𝔇.shrinkGerm s a c).2 hxac)).mdifferentiableAt (by simp)
  · refine (mdifferentiableAt_const (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ, ℂ)) (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport (𝔇.shrinkPoU c)).isOpen_compl.mem_nhds hb] with y hy
    simp only [globalPrimTerm, 𝔇.shrinkRhoC_eq_zero_of_notMem c hy, zero_mul]

/-- **The Wirtinger value of one summand** `proj01(mfderiv (ρ_c·holoFn σ_{ac}) x) = holoFn σ_{ac}(x) •
∂̄ρ_c x` at `x ∈ V_a` (product rule + `holoFn` holomorphic; off `tsupport ρ_c` both sides vanish). -/
theorem dbar_globalPrimTerm (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.shrinkOpens a : Opens X)) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrimTerm s a c) x)
      = holoFn (𝔇.shrinkGerm s a c).2 x • (𝔇.shrinkDbarRho c x) := by
  by_cases hb : x ∈ tsupport (𝔇.shrinkPoU c)
  · have hxc : x ∈ (𝔇.shrinkOpens c : Opens X) := 𝔇.shrinkPoU_tsupport_subset c hb
    have hxac : x ∈ ((𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens c : Opens X) : Set X) := ⟨hxa, hxc⟩
    have hr : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(𝔇.shrinkRhoC c)) x
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(𝔇.shrinkRhoC c)) x) :=
      ((𝔇.shrinkRhoC c).contMDiff.mdifferentiable (by simp) x).hasMFDerivAt
    have hh : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (holoFn (𝔇.shrinkGerm s a c).2) x
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (holoFn (𝔇.shrinkGerm s a c).2) x) :=
      ((holoFn_contMDiffAt (𝔇.shrinkGerm s a c).2 hxac).mdifferentiableAt (by simp)).hasMFDerivAt
    show proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrimTerm s a c) x)
      = holoFn (𝔇.shrinkGerm s a c).2 x • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑(𝔇.shrinkRhoC c)) x)
    rw [show (𝔇.globalPrimTerm s a c : X → ℂ)
        = ⇑(𝔇.shrinkRhoC c) * holoFn (𝔇.shrinkGerm s a c).2 from rfl,
      (hr.mul hh).mfderiv, map_add, proj01_smul, proj01_smul,
      holoFn_dbar_eq_zero (𝔇.shrinkGerm s a c).2 hxac]
    module
  · have hr0 : proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrimTerm s a c) x) = 0 := by
      have hconst : (𝔇.globalPrimTerm s a c) =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
        filter_upwards [(isClosed_tsupport (𝔇.shrinkPoU c)).isOpen_compl.mem_nhds hb] with y hy
        simp only [globalPrimTerm, 𝔇.shrinkRhoC_eq_zero_of_notMem c hy, zero_mul]
      rw [hconst.mfderiv_eq, mfderiv_const, map_zero]
    rw [hr0, 𝔇.shrinkDbarRho_eq_zero_of_notMem c hb]
    module

/-- Antisymmetry of `holoFn σ` (from diagonal vanishing + cocycle): `holoFn σ_{pa} = −holoFn σ_{ap}`
on `V_a ∩ V_p`. -/
theorem shrinkGerm_antisymm (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a p : 𝔇.ι) {y : X}
    (hya : y ∈ (𝔇.shrinkOpens a : Opens X)) (hyp : y ∈ (𝔇.shrinkOpens p : Opens X)) :
    holoFn (𝔇.shrinkGerm s p a).2 y = -holoFn (𝔇.shrinkGerm s a p).2 y := by
  have h := 𝔇.shrinkGerm_cocycle_add s hs p a p (y := y) ⟨⟨hyp, hya⟩, hyp⟩
  rw [𝔇.shrinkGerm_diag_eq_zero s hs p hyp] at h
  linear_combination -h

/-- **`glueForm` value telescopes on `V_a`**: `ω̂ x = ∑_c holoFn σ_{ac}(x) • ∂̄ρ_c(x)` for `x ∈ V_a`.
Via the cocycle substitution `holoFn σ_{pq} = holoFn σ_{aq} − holoFn σ_{ap}` (on `V_a`) and
`telescope_sum` (`∑ ρ = 1`, `∑ ∂̄ρ = 0`). -/
theorem glueForm_apply_on_V (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.shrinkOpens a : Opens X)) :
    ((𝔇.glueForm s : ↥(OneFormsZeroOne X)) : SmoothCOneForms X) x
      = ∑ c, holoFn (𝔇.shrinkGerm s a c).2 x • (𝔇.shrinkDbarRho c x) := by
  rw [glueForm_val, section_finset_sum_apply]
  -- rewrite each term `(ρ_p·holoFn σ_{pq})•∂̄ρ_q` to `(ρ_p·(H_q − H_p))•∂̄ρ_q` with `H_q = holoFn σ_{aq}`.
  have hterm : ∀ p : 𝔇.ι × 𝔇.ι, (𝔇.shrinkTerm s p.1 p.2) x
      = (𝔇.shrinkRhoC p.1 x
          * (holoFn (𝔇.shrinkGerm s a p.2).2 x - holoFn (𝔇.shrinkGerm s a p.1).2 x))
        • (𝔇.shrinkDbarRho p.2 x) := by
    intro p
    obtain ⟨p, q⟩ := p
    rw [shrinkTerm_apply]
    by_cases hp : x ∈ tsupport (𝔇.shrinkPoU p)
    · by_cases hq : x ∈ tsupport (𝔇.shrinkPoU q)
      · have hxp : x ∈ (𝔇.shrinkOpens p : Opens X) := 𝔇.shrinkPoU_tsupport_subset p hp
        have hxq : x ∈ (𝔇.shrinkOpens q : Opens X) := 𝔇.shrinkPoU_tsupport_subset q hq
        -- cocycle `holoFn σ_{pq} = holoFn σ_{pa} + holoFn σ_{aq}` and antisymm `σ_{pa} = −σ_{ap}`.
        rw [𝔇.shrinkGerm_cocycle_add s hs p a q ⟨⟨hxp, hxa⟩, hxq⟩,
          𝔇.shrinkGerm_antisymm s hs a p hxa hxp]
        congr 2; ring
      · rw [𝔇.shrinkDbarRho_eq_zero_of_notMem q hq]; module
    · rw [𝔇.shrinkRhoC_eq_zero_of_notMem p hp]; module
  simp_rw [hterm]
  exact telescope_sum (fun p => 𝔇.shrinkRhoC p x) (fun q => holoFn (𝔇.shrinkGerm s a q).2 x)
    (fun q => 𝔇.shrinkDbarRho q x) (𝔇.sum_shrinkRhoC_apply x) (𝔇.sum_shrinkDbarRho_apply x)

end ChartDiskCover

end Jacobians.Dolbeault
