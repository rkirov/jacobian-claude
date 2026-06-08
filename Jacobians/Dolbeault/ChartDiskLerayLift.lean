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

/-- `G_a = ∑_c (ρ_c · holoFn σ_{ac})` as a sum of functions. -/
theorem globalPrim_eq_sum (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) :
    𝔇.globalPrim s a = ∑ c, 𝔇.globalPrimTerm s a c := by
  funext x
  rw [globalPrim_apply, Finset.sum_apply]
  rfl

/-- **The intrinsic `∂̄` identity** `proj01(mfderiv G_a x) = ω̂ x` for `x ∈ V_a`.  The per-term Wirtinger
values (`dbar_globalPrimTerm`) summed (`HasMFDerivAt.sum`), matched to `glueForm` by its `V_a`
telescoping. -/
theorem dbar_globalPrim (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.shrinkOpens a : Opens X)) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrim s a) x)
      = ((𝔇.glueForm s : ↥(OneFormsZeroOne X)) : SmoothCOneForms X) x := by
  -- `mfderiv G_a x = ∑_c mfderiv (term_c) x`.
  have hsum : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (∑ c, 𝔇.globalPrimTerm s a c) x
      (∑ c, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrimTerm s a c) x) :=
    HasMFDerivAt.sum (fun c _ =>
      (𝔇.mdifferentiableAt_globalPrimTerm s a c hxa).hasMFDerivAt)
  have hmf : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrim s a) x
      = ∑ c, mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrimTerm s a c) x := by
    rw [𝔇.globalPrim_eq_sum s a]; exact hsum.mfderiv
  rw [hmf, map_sum, 𝔇.glueForm_apply_on_V s hs a hxa]
  exact Finset.sum_congr rfl fun c _ => 𝔇.dbar_globalPrimTerm s a c hxa

/-! ## §D — The holomorphic corrector `η_a := u_a − G_a`

`u_a := diskVal a ω̂` is the per-disk `∂̄`-primitive (`proj01(mfderiv u_a) = ω̂` on `U_a`,
`dbar_diskValue_eq_g`).  Then `η_a := u_a − G_a` has `proj01(mfderiv η_a) = ω̂ − ω̂ = 0` on `V_a` —
holomorphic — and is bounded on `V_a` (`u_a` continuous on the compact `closure V_a ⊆ U_a`; `G_a`
bounded by `∑ ‖s_{·a}‖`).  So `η_a ∈ BddHol (Wov (a,a))`. -/

/-- The per-disk `∂̄`-primitive value `u_a := diskVal a ω̂` (a smooth function on `U_a`). -/
noncomputable def primVal (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) : X → ℂ :=
  diskVal 𝔇 a (𝔇.glueForm s)

/-- `proj01(mfderiv u_a x) = ω̂ x` on `U_a` (Forster 13.2 primitive; `dbar_diskValue_eq_g` upgraded to
the full CLM by `dbar_eq_of_apply_one'`). -/
theorem dbar_primVal (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) {x : X} (hxa : x ∈ (𝔇.U a : Set X)) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.primVal s a) x)
      = ((𝔇.glueForm s : ↥(OneFormsZeroOne X)) : SmoothCOneForms X) x :=
  dbar_eq_of_apply_one' (𝔇.glueForm s).2 (𝔇.dbar_diskValue_eq_g (𝔇.glueForm s).2 a hxa)

theorem mdifferentiableAt_primVal (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.U a : Set X)) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.primVal s a) x :=
  (contMDiffAt_diskVal 𝔇 a (𝔇.glueForm s) hxa).mdifferentiableAt (by simp)

/-- **Chart-`a` Wirtinger bridge from intrinsic vanishing.**  If `w` is `MDifferentiableAt y` with
intrinsic Wirtinger scalar `proj01(mfderiv w y)(1) = 0`, then for any chart `a` whose source contains
`y`, the chart-`a` planar `∂̄(w ∘ φ_a⁻¹)(φ_a y) = 0`.  Proof: `w∘φ_a⁻¹ = (w∘φ_y⁻¹)∘(φ_y∘φ_a⁻¹)`, the
inner map is holomorphic, so by the Wirtinger chain rule the chart-`a` `∂̄` is `conj(τ′)` times the
own-chart `∂̄(w∘φ_y⁻¹)(φ_y y) = proj01(mfderiv w y)(1) = 0`. -/
theorem dbar_chartFixed_of_intrinsic_zero {w : X → ℂ} {y : X} (a : 𝔇.ι)
    (hya : y ∈ (chartAt (H := ℂ) (𝔇.center a)).source)
    (hwmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w y)
    (hw0 : proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w y) (1 : ℂ) = 0) :
    DbarDisk.dbar (fun z => w ((chartAt (H := ℂ) (𝔇.center a)).symm z))
      ((chartAt (H := ℂ) (𝔇.center a)) y) = 0 := by
  set φa := chartAt (H := ℂ) (𝔇.center a) with hφa
  set φy := chartAt (H := ℂ) y with hφy
  set τ : ℂ → ℂ := φy ∘ φa.symm with hτ
  have hyy : y ∈ φy.source := mem_chart_source ℂ y
  -- own-chart `∂̄(w∘φ_y.symm)(φ_y y) = proj01(mfderiv w y)(1) = 0`.
  have hown : DbarDisk.dbar (fun z => w (φy.symm z)) (φy y) = 0 := by
    have := dbar_apply_one_eq_dbarDisk' hwmd
    rw [hw0] at this
    -- `extChartAt 𝓘(ℝ,ℂ) y = chartAt ℂ y = φy` (identity model).
    simpa only [hφy, show (extChartAt 𝓘(ℝ, ℂ) y : X → ℂ) = (chartAt (H := ℂ) y : X → ℂ) from rfl,
      show ((extChartAt 𝓘(ℝ, ℂ) y) y : ℂ) = (chartAt (H := ℂ) y) y from rfl] using this.symm
  -- `τ` holomorphic at `φ_a y`, `τ (φ_a y) = φ_y y`.
  have hτdiff : DifferentiableAt ℂ τ (φa y) := by
    rw [hτ, hφy, hφa]
    exact (transition_analyticAt_of_mem (y := 𝔇.center a) (z := y) (x := y)
      hya hyy).differentiableAt
  have hτpt : τ (φa y) = φy y := by
    rw [hτ, Function.comp_apply, φa.left_inv hya]
  -- `w∘φ_y.symm` is `ℝ`-diff at `φ_y y` (= `τ(φ_a y)`).
  have hwsymm_md : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) w (φy.symm (φy y)) := by
    rw [φy.left_inv hyy]; exact hwmd
  have hℝ : DifferentiableAt ℝ (fun z => w (φy.symm z)) (φy y) := by
    have hsymm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φy.symm (φy y) :=
      (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := y) _
        (φy.map_source hyy)).contMDiffAt
        (φy.open_target.mem_nhds (φy.map_source hyy)) |>.mdifferentiableAt (by simp)
    have hcomp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun z => w (φy.symm z)) (φy y) :=
      hwsymm_md.comp (φy y) hsymm
    have := hcomp.differentiableWithinAt_writtenInExtChartAt
    rw [writtenInExtChartAt, ModelWithCorners.Boundaryless.range_eq_univ,
      differentiableWithinAt_univ] at this
    simpa only [Function.comp, mfld_simps] using this
  -- Wirtinger chain rule: `∂̄((w∘φ_y.symm)∘τ)(φ_a y) = conj(τ′)·∂̄(w∘φ_y.symm)(φ_y y) = conj·0 = 0`.
  have hchain : DbarDisk.dbar ((fun z => w (φy.symm z)) ∘ τ) (φa y)
      = (starRingEnd ℂ) (deriv τ (φa y)) * DbarDisk.dbar (fun z => w (φy.symm z)) (τ (φa y)) :=
    dbarDisk_comp_holo (fun z => w (φy.symm z)) τ (φa y) (hτpt ▸ hℝ) hτdiff
  -- `w∘φ_a.symm = (w∘φ_y.symm)∘τ` on a NEIGHBOURHOOD of `φ_a y` (where `φ_a.symm ∈ φ_a.source`).
  have hcompfun : (fun z => w (φa.symm z)) =ᶠ[nhds (φa y)] ((fun z => w (φy.symm z)) ∘ τ) := by
    have hcont : ContinuousAt φa.symm (φa y) := φa.continuousAt_symm (φa.map_source hya)
    filter_upwards [hcont.preimage_mem_nhds (φy.open_source.mem_nhds (by
      rw [φa.left_inv hya]; exact hyy))] with z hz
    -- `hz : φa.symm z ∈ φy.source`; `τ z = φy (φa.symm z)`, `φy.symm (φy (φa.symm z)) = φa.symm z`.
    simp only [hτ, Function.comp_apply, φy.left_inv hz]
  rw [dbarDisk_congr hcompfun, hchain, hτpt, hown, mul_zero]

/-- **The corrector function** `η_a := u_a − G_a` (a bare `X → ℂ`, holomorphic on `V_a`). -/
noncomputable def etaFn (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) : X → ℂ :=
  fun x => 𝔇.primVal s a x - 𝔇.globalPrim s a x

/-- `η_a` is `MDifferentiableAt` at `x ∈ V_a` (difference of two `MDifferentiableAt` functions). -/
theorem mdifferentiableAt_etaFn (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.shrinkOpens a : Opens X)) :
    MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.etaFn s a) x := by
  have hxaU : x ∈ (𝔇.U a : Set X) := 𝔇.shrinkOpens_le_U a hxa
  have hpu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.primVal s a) x := 𝔇.mdifferentiableAt_primVal s a hxaU
  have hpg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrim s a) x := by
    rw [𝔇.globalPrim_eq_sum s a]
    exact MDifferentiableAt.sum fun c _ => 𝔇.mdifferentiableAt_globalPrimTerm s a c hxa
  exact hpu.sub hpg

/-- The intrinsic Wirtinger scalar of `η_a` vanishes on `V_a`: `proj01(mfderiv η_a y)(1) = 0` (both
`u_a` and `G_a` have it `= (ω̂ y)(1)`). -/
theorem dbar1_etaFn (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a : 𝔇.ι) {y : X}
    (hya : y ∈ (𝔇.shrinkOpens a : Opens X)) :
    proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.etaFn s a) y) (1 : ℂ) = 0 := by
  have hyaU : y ∈ (𝔇.U a : Set X) := 𝔇.shrinkOpens_le_U a hya
  have hpu : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.primVal s a) y := 𝔇.mdifferentiableAt_primVal s a hyaU
  have hpg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.globalPrim s a) y := by
    rw [𝔇.globalPrim_eq_sum s a]
    exact MDifferentiableAt.sum fun c _ => 𝔇.mdifferentiableAt_globalPrimTerm s a c hya
  -- own-chart planar `∂̄` of `η_a` = `∂̄(pu) − ∂̄(pg)` = `(ω̂)(1) − (ω̂)(1) = 0`; transfer back to scalar.
  set e := (extChartAt 𝓘(ℝ, ℂ) y) with he
  have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.etaFn s a) y := 𝔇.mdifferentiableAt_etaFn s a hya
  rw [dbar_apply_one_eq_dbarDisk' hmd]
  have hpullEq : (fun z => 𝔇.etaFn s a (e.symm z))
      = fun z => 𝔇.primVal s a (e.symm z) - 𝔇.globalPrim s a (e.symm z) := by
    funext z; simp only [etaFn]
  have hℝu : DifferentiableAt ℝ (fun z => 𝔇.primVal s a (e.symm z)) (e y) := by
    have := hpu.differentiableWithinAt_writtenInExtChartAt
    rw [writtenInExtChartAt, ModelWithCorners.Boundaryless.range_eq_univ,
      differentiableWithinAt_univ] at this
    simpa only [Function.comp, he, mfld_simps] using this
  have hℝg : DifferentiableAt ℝ (fun z => 𝔇.globalPrim s a (e.symm z)) (e y) := by
    have := hpg.differentiableWithinAt_writtenInExtChartAt
    rw [writtenInExtChartAt, ModelWithCorners.Boundaryless.range_eq_univ,
      differentiableWithinAt_univ] at this
    simpa only [Function.comp, he, mfld_simps] using this
  rw [hpullEq, dbarFun_sub hℝu hℝg]
  rw [← dbar_apply_one_eq_dbarDisk' hpu, ← dbar_apply_one_eq_dbarDisk' hpg,
    𝔇.dbar_primVal s a hyaU, 𝔇.dbar_globalPrim s hs a hya, sub_self]

/-- **`η_a` chart-`a`-read is `AnalyticOn` `Wov (a,a)`.**  At each `z = φ_a y` (`y ∈ V_a`) the chart-`a`
planar `∂̄(η_a ∘ φ_a⁻¹) = 0` (`dbar_chartFixed_of_intrinsic_zero` + `dbar1_etaFn`), and the pullback is
`ℝ`-differentiable on the open `W = φ_a.target ∩ φ_a.symm⁻¹'(V_a)`; an open `DifferentiableOn ℂ` ⟹
`AnalyticOn`. -/
theorem etaFn_chartA_analyticOn (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a : 𝔇.ι) :
    AnalyticOn ℂ (𝔇.etaFn s a ∘ (chartAt (H := ℂ) (𝔇.center a)).symm) (𝔇.Wov (a, a)) := by
  set φa := chartAt (H := ℂ) (𝔇.center a) with hφa
  set W : Set ℂ := φa.target ∩ φa.symm ⁻¹' ((𝔇.shrinkOpens a : Opens X) : Set X) with hW
  have hWopen : IsOpen W := φa.isOpen_inter_preimage_symm (𝔇.shrinkOpens a).isOpen
  -- `DifferentiableOn ℂ (η_a∘φa.symm) W`.
  have hDiffOn : DifferentiableOn ℂ (𝔇.etaFn s a ∘ φa.symm) W := by
    intro z hz
    have hzV : φa.symm z ∈ ((𝔇.shrinkOpens a : Opens X) : Set X) := hz.2
    have hzsrc : φa.symm z ∈ φa.source := φa.map_target hz.1
    have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.etaFn s a) (φa.symm z) :=
      𝔇.mdifferentiableAt_etaFn s a hzV
    -- `ℝ`-differentiability of the chart-`a` pullback at `z = φa (φa.symm z)`.
    have hℝ : DifferentiableAt ℝ (𝔇.etaFn s a ∘ φa.symm) z := by
      have hsymm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) φa.symm z :=
        (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := 𝔇.center a) _ hz.1).contMDiffAt
          (φa.open_target.mem_nhds hz.1) |>.mdifferentiableAt (by simp)
      have hcomp : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (𝔇.etaFn s a ∘ φa.symm) z :=
        hmd.comp z hsymm
      have := hcomp.differentiableWithinAt_writtenInExtChartAt
      rw [writtenInExtChartAt, ModelWithCorners.Boundaryless.range_eq_univ,
        differentiableWithinAt_univ] at this
      simpa only [Function.comp, mfld_simps] using this
    -- chart-`a` planar `∂̄ = 0` (bridge from intrinsic zero).
    have hdb0 : DbarDisk.dbar (fun w => 𝔇.etaFn s a (φa.symm w)) z = 0 := by
      have hzz : φa (φa.symm z) = z := φa.right_inv hz.1
      have := 𝔇.dbar_chartFixed_of_intrinsic_zero a hzsrc hmd (𝔇.dbar1_etaFn s hs a hzV)
      rwa [hzz] at this
    exact (differentiableAt_of_dbar_eq_zero_chartDisk hℝ hdb0).differentiableWithinAt
  -- `AnalyticOn` on `Wov (a,a) = φ_a '' (V_a ∩ V_a) ⊆ W`-image.
  rintro w ⟨y, hyVV, rfl⟩
  have hyV : y ∈ ((𝔇.shrinkOpens a : Opens X) : Set X) := hyVV.1
  have hysrc : y ∈ φa.source := 𝔇.shrinkOpens_subset_source a hyV
  have hwW : φa y ∈ W := ⟨φa.map_source hysrc, by
    simp only [hW, Set.mem_preimage, φa.left_inv hysrc]; exact hyV⟩
  exact (hDiffOn.analyticOnNhd hWopen (φa y) hwW).analyticWithinAt

/-- `‖holoFn σ_{ac} x‖ ≤ ‖s_{ac}‖` on `V_a ∩ V_c` (the germ-section value is `s.toFun∘φ_a`, bounded by
the `BddHol` norm). -/
theorem norm_shrinkGerm_holoFn_le (s : 𝔇.overlapData.Cshr) (a c : 𝔇.ι) {x : X}
    (hx : x ∈ (𝔇.shrinkOpens a ⊓ 𝔇.shrinkOpens c : Opens X)) :
    ‖holoFn (𝔇.shrinkGerm s a c).2 x‖ ≤ ‖s (a, c)‖ := by
  rw [𝔇.shrinkGerm_holoFn s a c hx]
  exact (s (a, c)).norm_toFun_le (𝔇.chart_mem_Wov_of_shrinkInter a c hx)

/-- `G_a` is bounded by `∑_c ‖s_{ac}‖` on `V_a`. -/
theorem norm_globalPrim_le (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) {x : X}
    (hxa : x ∈ (𝔇.shrinkOpens a : Opens X)) :
    ‖𝔇.globalPrim s a x‖ ≤ ∑ c, ‖s (a, c)‖ := by
  rw [globalPrim_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  by_cases hb : x ∈ tsupport (𝔇.shrinkPoU c)
  · have hxc : x ∈ (𝔇.shrinkOpens c : Opens X) := 𝔇.shrinkPoU_tsupport_subset c hb
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (𝔇.norm_shrinkGerm_holoFn_le s a c ⟨hxa, hxc⟩)
    -- `‖ρ̃_c x‖ = |ρ_c x| ≤ 1` (nonneg + `∑ρ = 1`).
    show ‖((𝔇.shrinkPoU c x : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ((𝔇.shrinkPoU).nonneg c x)]
    calc (𝔇.shrinkPoU c x : ℝ) ≤ ∑ d, 𝔇.shrinkPoU d x :=
          Finset.single_le_sum (fun d _ => (𝔇.shrinkPoU).nonneg d x) (Finset.mem_univ c)
      _ = 1 := 𝔇.sum_shrinkPoU_eq_one x
  · rw [𝔇.shrinkRhoC_eq_zero_of_notMem c hb, zero_mul, norm_zero]
    exact norm_nonneg _

/-- `primVal s a (φ_a.symm z) = planarPrimitive a ω̂ z` for `z ∈ φ_a.target` (chart round-trip). -/
theorem primVal_chartSymm (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) {z : ℂ}
    (hz : z ∈ (chartAt (H := ℂ) (𝔇.center a)).target) :
    𝔇.primVal s a ((chartAt (H := ℂ) (𝔇.center a)).symm z)
      = 𝔇.planarPrimitive a (𝔇.glueForm s) z := by
  show 𝔇.planarPrimitive a (𝔇.glueForm s)
      ((extChartAt 𝓘(ℝ, ℂ) (𝔇.center a)) ((chartAt (H := ℂ) (𝔇.center a)).symm z)) = _
  rw [show (extChartAt 𝓘(ℝ, ℂ) (𝔇.center a) : X → ℂ) = (chartAt (H := ℂ) (𝔇.center a) : X → ℂ) from rfl,
    (chartAt (H := ℂ) (𝔇.center a)).right_inv hz]

/-- **`η_a` chart-`a`-read is bounded on `Wov (a,a)`**: `‖planarPrimitive a ω̂ z‖` is bounded on the
compact `closure (Wov (a,a))` (`planarPrimitive` is globally continuous), and `‖G_a‖ ≤ ∑‖s_{a·}‖`. -/
theorem etaFn_chartA_bounded (s : 𝔇.overlapData.Cshr) (a : 𝔇.ι) :
    ∃ C, ∀ z ∈ 𝔇.Wov (a, a),
      ‖(𝔇.etaFn s a ∘ (chartAt (H := ℂ) (𝔇.center a)).symm) z‖ ≤ C := by
  obtain ⟨M, hM⟩ := (𝔇.isCompact_closure_Wov (a, a)).exists_bound_of_continuousOn
    (f := 𝔇.planarPrimitive a (𝔇.glueForm s))
    (𝔇.contDiff_planarPrimitive a (𝔇.glueForm s)).continuous.continuousOn
  refine ⟨M + ∑ c, ‖s (a, c)‖, fun z hz => ?_⟩
  obtain ⟨y, hyVV, rfl⟩ := hz
  have hyV : y ∈ ((𝔇.shrinkOpens a : Opens X) : Set X) := hyVV.1
  have hysrc : y ∈ (chartAt (H := ℂ) (𝔇.center a)).source := 𝔇.shrinkOpens_subset_source a hyV
  have htgt : (chartAt (H := ℂ) (𝔇.center a)) y ∈ (chartAt (H := ℂ) (𝔇.center a)).target :=
    (chartAt (H := ℂ) (𝔇.center a)).map_source hysrc
  -- value: `η_a∘φa.symm (φa y) = planarPrimitive a ω̂ (φa y) − G_a y`.
  have hval : (𝔇.etaFn s a ∘ (chartAt (H := ℂ) (𝔇.center a)).symm) ((chartAt (H := ℂ) (𝔇.center a)) y)
      = 𝔇.planarPrimitive a (𝔇.glueForm s) ((chartAt (H := ℂ) (𝔇.center a)) y) - 𝔇.globalPrim s a y := by
    simp only [Function.comp_apply, etaFn, (chartAt (H := ℂ) (𝔇.center a)).left_inv hysrc]
    -- `primVal s a y = planarPrimitive a ω̂ (extChartAt(center a) y) = planarPrimitive a ω̂ (φa y)`.
    rfl
  rw [hval]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (𝔇.norm_globalPrim_le s a hyV))
  exact hM _ (subset_closure ⟨y, hyVV, rfl⟩)

/-- **The holomorphic corrector `η_a ∈ BddHol (Wov (a,a))`** (`C0Holo`'s `a`-component). -/
noncomputable def etaBddHol (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a : 𝔇.ι) :
    BddHol (𝔇.Wov (a, a)) :=
  BddHol.ofAnalyticOn (𝔇.etaFn s a ∘ (chartAt (H := ℂ) (𝔇.center a)).symm)
    (𝔇.etaFn_chartA_analyticOn s hs a) (𝔇.etaFn_chartA_bounded s a)

theorem etaBddHol_toFun_of_mem (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) (a : 𝔇.ι)
    {z : ℂ} (hz : z ∈ 𝔇.Wov (a, a)) :
    (𝔇.etaBddHol s hs a).toFun z = 𝔇.etaFn s a ((chartAt (H := ℂ) (𝔇.center a)).symm z) :=
  BddHol.ofAnalyticOn_toFun_of_mem _ _ _ hz

/-- `η : C0Holo` — the holomorphic 0-cochain. -/
noncomputable def etaCochain (s : 𝔇.overlapData.Cshr) (hs : 𝔇.delta1Model s = 0) : 𝔇.C0Holo :=
  fun a => 𝔇.etaBddHol s hs a

end ChartDiskCover

end Jacobians.Dolbeault
