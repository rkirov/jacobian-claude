/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueInftyCoherence
import Jacobians.Dolbeault.FormTraceBundleBridge
import Jacobians.Dolbeault.MittagLeffler

/-!
# Gate A — the SOUND branch-value boundedness `hbnd` for a general meromorphic `α = ω₀·g`

This file discharges the branch-value boundedness `hbnd` of the genus-`0` simple-`∞` canonical
capstone `…_germ_CfullHreg_inftyClosed` **soundly**, for a general meromorphic numerator `g`, WITHOUT
the over-strong global-holomorphic-`αBr` route of `SerreResidueInftyClosedBnd.lean`.

## Why a new `hbnd` route (the `αBr` soundness finding)

`Jacobians.Dolbeault.SerreResidueTheorem.hbnd_canonical_of_offBranch` discharges `hbnd` via
`hbnd_of_eventual_sphereCoherence`, whose input `hαBrAgree` demands a **global** holomorphic 1-form
`αBr : HolomorphicOneForms X` agreeing with `ω₀·g` at **every** fibre point near each branch value
`b₀`.  Those fibre points sweep an **open** set `U = F⁻¹(punctured disk)`, so `αBr = ω₀·g` on `U`,
whence `αBr/ω₀ = g` GLOBALLY (identity theorem, `X` connected) — forcing every pole of `g` to sit at a
zero of `ω₀`.  For a general meromorphic `g` this is FALSE (the Serre-pairing consumer has `g = α/ω₀`
with poles wherever `α` has poles).  So that route is unsound for general `α`; see `human_input.md`
(2026-06-09, "8th bad field").

## The sound route (the `g`-weighted bundle SUM)

`hbnd` is genuinely TRUE (Miranda §VIII.3: the symmetric SUM extends across branch points).  The
geometric trace decomposes (`FormTraceBundleBridge.traceLocalCoeff_traceFun_eq_sheetSum`) as the
`g`-weighted fibre sum of the **global holomorphic** `ω₀`'s bundle summand:

> `valueChartTrace ω₀ f Φ z = ∑_{p ∈ F⁻¹(coe z)} g(p) · sheetPullback ω₀ p`.

We bound `(z − b₀)·[g-weighted sum] → 0` via a `g`-weighted analogue of
`TraceForm.traceLocalCoeff_mul_sub_tendsto_zero`: the per-preimage `ω₀`-summand boundedness
`TraceForm.traceSummand_localCoeff_mul_sub_tendsto` (applied to the GLOBAL HOLOMORPHIC `ω₀`, **not**
`ω₀·g`) times the BOUNDED weight `g(x)` (continuous at the fibre, since `b₀` is off the pole-values).
No global `αBr` — the form fed to the crux is `ω₀` itself.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `traceLocalCoeff_mul_sub_gWeighted_tendsto_zero_Y` — the `g`-weighted boundedness of the bundle SUM at
  a branch value, mirroring `traceLocalCoeff_mul_sub_tendsto_zero_Y` with the `g`-weight.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3, pp. 251–256.
* `Jacobians/TraceForm.lean` (`traceLocalCoeff_mul_sub_tendsto_zero_Y`, the un-weighted crux).
* `human_input.md` (2026-06-09 — the `αBr` soundness finding + this sound route).
-/

noncomputable section

open Complex Metric Filter Topology Set
open scoped Manifold ContDiff Real

namespace Jacobians.TraceResidue

open Jacobians

variable {X Y : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-! ### The `g`-weighted per-preimage summand boundedness

Near a preimage `x₀` of the branch value `y₀`, the `g`-weighted bundle summand
`(c(fx) − c(y₀)) · g(x) · inCoordinates(traceSummand ω₀ x) 1 = g(x) · bigPhi f ω₀ y₀ x`
tends to `0`: `bigPhi → 0` (the un-weighted summand crux `traceSummand_localCoeff_mul_sub_tendsto`,
applied to the *global holomorphic* `ω₀`) and `g` is continuous at `x₀` (so bounded). -/

/-- **`g`-weighted per-preimage summand boundedness.**  For a global holomorphic `ω₀`, a weight `g`
continuous at a preimage `x₀` of `y₀ = f x₀`, the scaled `g`-weighted bundle summand tends to `0` as
`x → x₀` through the off-critical punctured neighbourhood. -/
theorem traceSummand_localCoeff_mul_sub_gWeighted_tendsto (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (ω₀ : HolomorphicOneForms X) (g : X → ℂ) {y₀ : Y} {x₀ : X} (hfx₀ : f x₀ = y₀)
    (hg : ContinuousAt g x₀) :
    Tendsto (fun x => g x * bigPhi f ω₀ y₀ x)
      (𝓝[(criticalSet f)ᶜ \ {x₀}] x₀) (𝓝 0) := by
  -- The un-weighted summand tends to 0 (the proven crux, applied to the global holomorphic ω₀).
  have hbig : Tendsto (fun x => bigPhi f ω₀ y₀ x)
      (𝓝[(criticalSet f)ᶜ \ {x₀}] x₀) (𝓝 0) :=
    traceSummand_localCoeff_mul_sub_tendsto f hf hnonconst ω₀ hfx₀
  -- g continuous (bounded) × bigPhi → 0, so g · bigPhi → 0.
  have hgc : Tendsto g (𝓝[(criticalSet f)ᶜ \ {x₀}] x₀) (𝓝 (g x₀)) :=
    hg.mono_left nhdsWithin_le_nhds
  have := hgc.mul hbig
  simpa using this

/-! ### The `g`-weighted bundle SUM boundedness at a branch value

Mirror of `TraceForm.traceLocalCoeff_mul_sub_tendsto_zero_Y` with the `g`-weight inserted: in the
fixed chart `c := chartAt ℂ y₀`, the scaled `g`-weighted bundle local coefficient
`(c y − c y₀) · ∑ᶠ x ∈ f⁻¹{y}, g(x)·localCoeffLin(traceSummand ω₀ x) → 0`.  Each fibre term is
`g(x)·bigPhi f ω₀ y₀ x → 0` (the per-preimage `g`-weighted summand boundedness); the finite-subcover /
uniform off-branch card assembly is verbatim. -/

/-- **`g`-weighted bundle SUM boundedness (chart side).**  For a global holomorphic `ω₀` and a weight
`g` continuous at every preimage of the branch value `y₀`, the `g`-weighted bundle local coefficient
satisfies `(c y − c y₀) · ∑ᶠ x ∈ f⁻¹{y}, g(x)·localCoeffLin(traceSummand ω₀ x) → 0` as `y → y₀`
through `y ≠ y₀`.  No global `ω₀·g` form: the boundedness rides on the GLOBAL HOLOMORPHIC `ω₀` summand,
the `g` enters only as a bounded weight. -/
theorem traceLocalCoeff_mul_sub_gWeighted_tendsto_zero_Y (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    {y₀ : Y} (hy₀ : y₀ ∈ branchLocus f)
    (hg : ∀ x ∈ f ⁻¹' {y₀}, ContinuousAt g x) :
    Tendsto (fun y => ((chartAt ℂ y₀) y - (chartAt ℂ y₀) y₀)
        * ∑ᶠ x ∈ f ⁻¹' {y}, g x * localCoeffLin y₀ y (traceSummand f ω₀ x)) (𝓝[≠] y₀) (𝓝 0) := by
  classical
  set c := chartAt ℂ y₀ with hc
  -- Uniform off-branch fibre-cardinality bound near the branch point.
  obtain ⟨N, hN⟩ := fibre_ncard_bddAbove_near_branch f hf hnonconst hy₀
  -- Per-preimage open neighbourhood with the scaled `g`-weighted-coefficient bound.
  have hloc : ∀ (x₀ : X), f x₀ = y₀ → ∀ ε' : ℝ, 0 < ε' →
      ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
        ∀ x ∈ U, x ∉ criticalSet f → x ≠ x₀ → ‖g x * bigPhi f ω₀ y₀ x‖ < ε' := by
    intro x₀ hfx₀ ε' hε'
    have hgx₀ : ContinuousAt g x₀ := hg x₀ (by rw [Set.mem_preimage, Set.mem_singleton_iff]; exact hfx₀)
    have htend := traceSummand_localCoeff_mul_sub_gWeighted_tendsto f hf hnonconst ω₀ g hfx₀ hgx₀
    have hev : ∀ᶠ x in 𝓝[(criticalSet f)ᶜ \ {x₀}] x₀, ‖g x * bigPhi f ω₀ y₀ x‖ < ε' := by
      have := htend.eventually (Metric.ball_mem_nhds (0 : ℂ) hε')
      filter_upwards [this] with x hx
      simpa [Complex.dist_eq] using hx
    rw [eventually_nhdsWithin_iff] at hev
    rw [eventually_iff_exists_mem] at hev
    obtain ⟨V, hVnhd, hV⟩ := hev
    obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hVnhd
    refine ⟨U, hUopen, hxU, ?_⟩
    intro x hxU' hxcrit hxne
    exact hV x (hUsub hxU') ⟨hxcrit, hxne⟩
  have hproper : IsProperMap f := isProperMap_of_contMDiff f hf
  have hcompact : IsCompact (f ⁻¹' {y₀}) :=
    (isClosed_singleton.preimage hf.continuous).isCompact
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  set ε' : ℝ := ε / (N + 1) with hε'def
  have hε' : 0 < ε' := by positivity
  choose! U hUopen hUmem hUbnd using fun (p : X) (hp : f p = y₀) => hloc p hp ε' hε'
  obtain ⟨b, hbsub, hbfin, hbcover⟩ :=
    hcompact.elim_finite_subcover_image
      (b := f ⁻¹' {y₀}) (c := U)
      (fun i hi => hUopen i hi)
      (fun p hp => Set.mem_iUnion₂.mpr ⟨p, hp, hUmem p hp⟩)
  set V : Set X := ⋃ i ∈ b, U i with hVdef
  have hVopen : IsOpen V := isOpen_biUnion (fun i hi => hUopen i (hbsub hi))
  obtain ⟨W, hWopen, hWmem, hWsub⟩ := properNbhd hproper y₀ hVopen hbcover
  have hWnhd : W ∈ 𝓝[≠] y₀ := nhdsWithin_le_nhds (hWopen.mem_nhds hWmem)
  filter_upwards [hWnhd, hN, eventually_notMem_branchLocus f hf hnonconst y₀,
    self_mem_nhdsWithin] with y hyW hyN hybranch hyne
  have hynotbranch : y ∉ branchLocus f := hybranch
  have hyncard : (f ⁻¹' {y}).ncard ≤ N := hyN hynotbranch
  have hfin : (f ⁻¹' {y}).Finite := fiber_finite_off_branchLocus f hf hnonconst hynotbranch
  -- The `g`-weighted summand identity: `(c y − c y₀)·g(x)·localCoeffLin(traceSummand ω₀ x) = g(x)·bigPhi`.
  have hsummand : ∀ x ∈ f ⁻¹' {y},
      (c y - c y₀) * (g x * localCoeffLin y₀ y (traceSummand f ω₀ x)) = g x * bigPhi f ω₀ y₀ x := by
    intro x hx
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp only [bigPhi, localCoeffLin, LinearMap.coe_mk, AddHom.coe_mk, hc]
    rw [hx]; ring
  have heq : (c y - c y₀) * ∑ᶠ x ∈ f ⁻¹' {y}, g x * localCoeffLin y₀ y (traceSummand f ω₀ x)
      = ∑ᶠ x ∈ f ⁻¹' {y}, g x * bigPhi f ω₀ y₀ x := by
    rw [mul_finsum_mem _ _]
    exact finsum_mem_congr rfl hsummand
  have hxbound : ∀ x ∈ f ⁻¹' {y}, ‖g x * bigPhi f ω₀ y₀ x‖ < ε' := by
    intro x hx
    have hxy : f x = y := by rw [Set.mem_preimage, Set.mem_singleton_iff] at hx; exact hx
    have hxcrit : x ∉ criticalSet f := fun hmem => hynotbranch ⟨x, hmem, hxy⟩
    have hxW : x ∈ f ⁻¹' W := by rw [Set.mem_preimage, hxy]; exact hyW
    have hxV : x ∈ V := hWsub hxW
    rw [hVdef, Set.mem_iUnion₂] at hxV
    obtain ⟨i, hib, hiU⟩ := hxV
    have hfiy₀ : f i = y₀ := by
      have := hbsub hib; rw [Set.mem_preimage, Set.mem_singleton_iff] at this; exact this
    have hxne_i : x ≠ i := by
      intro hcontra; rw [hcontra, hfiy₀] at hxy; exact hyne (by rw [Set.mem_singleton_iff, hxy])
    exact hUbnd i hfiy₀ x hiU hxcrit hxne_i
  rw [heq, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hcardN : hfin.toFinset.card ≤ N := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]; exact hyncard
  calc ‖∑ x ∈ hfin.toFinset, g x * bigPhi f ω₀ y₀ x‖
      ≤ ∑ x ∈ hfin.toFinset, ‖g x * bigPhi f ω₀ y₀ x‖ := norm_sum_le _ _
    _ ≤ hfin.toFinset.card • ε' := by
        refine Finset.sum_le_card_nsmul _ _ _ (fun x hx => ?_)
        exact le_of_lt (hxbound x ((Set.Finite.mem_toFinset hfin).mp hx))
    _ = (hfin.toFinset.card : ℝ) * ε' := by rw [nsmul_eq_mul]
    _ ≤ (N : ℝ) * ε' := by
        apply mul_le_mul_of_nonneg_right _ (le_of_lt hε')
        exact_mod_cast hcardN
    _ < ε := by
        rw [hε'def]
        calc (N : ℝ) * (ε / (N + 1)) = (N / (N + 1)) * ε := by ring
          _ < 1 * ε := by
              apply mul_lt_mul_of_pos_right _ hε
              rw [div_lt_one (by positivity)]; linarith
          _ = ε := one_mul ε

end Jacobians.TraceResidue

namespace Jacobians.Dolbeault.FormTraceGlobal

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open OnePoint

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.RiemannSphere
  Jacobians.Dolbeault.FormTraceMovingFibre Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip

attribute [local instance] Classical.propDecidable

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}

/-! ### The geometric trace as the `g`-weighted bundle finsum (αBr-FREE)

The sound bridge: at a regular value `coe z` with a sphere sheet system `S`, the geometric fibre trace
equals the `g`-weighted bundle finsum of the **global holomorphic** `ω₀` over the fibre — with **no**
auxiliary global form `αBr`.  This is the αBr-free analogue of `fibreTrace_traceCoeff_eq_traceLocalCoeff`
(whose αBr-naming step we drop), feeding the `g`-weighted boundedness crux directly. -/

/-- **Per-sheet frame identity.**  On `RiemannSphere`, the `coe b₀`-frame local coefficient of the
`ω₀`-trace summand at the sheet point `s (coe z)` equals the raw bundle summand `sheetPullback ω₀ s
(coe z) 1`.  Frame swap (`localCoeffLin_coe_base_swap`) to the self `coe z`-frame, then
`inCoordinates_center_self`, then `traceSummandAt_sheet_eq` (summand = `sheetPullback`). -/
theorem localCoeffLin_traceSummand_eq_sheetPullback (ω₀ : HolomorphicOneForms X) {b₀ z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere))) (i : Fin S.n) :
    localCoeffLin (((b₀ : ℂ) : RiemannSphere)) (((z : ℂ) : RiemannSphere))
        (traceSummand f.toRiemannSphere ω₀ (S.sheet i (((z : ℂ) : RiemannSphere))))
      = sheetPullback ω₀ (S.sheet i) (((z : ℂ) : RiemannSphere)) (1 : ℂ) := by
  -- `traceSummand F ω₀ (S.sheet i (coe z)) = sheetPullback ω₀ (S.sheet i)(coe z)`.
  have hsummand : traceSummand f.toRiemannSphere ω₀ (S.sheet i (((z : ℂ) : RiemannSphere)))
      = sheetPullback ω₀ (S.sheet i) (((z : ℂ) : RiemannSphere)) := by
    have h := S.traceSummandAt_sheet_eq f.contMDiff_toRiemannSphere ω₀ i S.mem_V
    rw [traceSummandAt] at h; exact h
  rw [hsummand, localCoeffLin_coe_base_swap]
  -- Self-frame: `localCoeffLin (coe z)(coe z) φ = φ 1`.
  unfold localCoeffLin
  simp only [LinearMap.coe_mk, AddHom.coe_mk, inCoordinates_center_self]
  rfl

/-- **Geometric trace = `g`-weighted bundle finsum (αBr-FREE).**  At a regular value `coe z` with a
sphere sheet system `S` (regular fibre — `hderiv`, `hmero`), the geometric fibre trace coefficient
equals the `g`-weighted bundle finsum of `ω₀` over the fibre `F⁻¹(coe z)`, read in the `coe b₀`-frame:

> `(fibreTrace ω₀ f (ofSphereSheetSystem S hderiv hmero)).traceCoeff z
>    = ∑ᶠ x ∈ F⁻¹(coe z), g x · localCoeffLin (coe b₀) (coe z) (traceSummand F ω₀ x)`.

No global `αBr` — the boundedness rides on the global holomorphic `ω₀` summand weighted by `g`. -/
theorem fibreTrace_traceCoeff_eq_gWeighted_finsum (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) {b₀ z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderiv : ∀ i, deriv (fun w => f.holoRepr
        ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
        (S.sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmero : ∀ i, MeromorphicAt
      (fun w => g ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
        (S.sheet i (((z : ℂ) : RiemannSphere))))) :
    (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv hmero)).traceCoeff z
      = ∑ᶠ x ∈ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))},
          g x * localCoeffLin (((b₀ : ℂ) : RiemannSphere)) (((z : ℂ) : RiemannSphere))
            (traceSummand f.toRiemannSphere ω₀ x) := by
  -- The geometric side = `g`-weighted sheet sum (the proven αBr-free body via the moving sum).
  have hmoving := (fibreTrace_eventuallyEq_movingSum ω₀ f
    (FibreRegularData.ofSphereSheetSystem S hderiv hmero) (fun i => S.holoReprSheet i)
    (fun _ => rfl)
    (fun i => (S.holoReprSheet_contMDiffAt i).continuousAt)
    (fun i => S.holoReprSheet_section i)).self_of_nhds
  rw [hmoving]
  simp only []
  have hgeo : ∑ i, chartIntegrand ω₀ g ((FibreRegularData.ofSphereSheetSystem S hderiv hmero).xs i)
        ((chartAt ℂ ((FibreRegularData.ofSphereSheetSystem S hderiv hmero).xs i))
          (S.holoReprSheet i z))
        * deriv (fun w => (chartAt ℂ ((FibreRegularData.ofSphereSheetSystem S hderiv hmero).xs i))
            (S.holoReprSheet i w)) z
      = ∑ i, g (S.sheet i (((z : ℂ) : RiemannSphere)))
          * sheetPullback ω₀ (S.sheet i) (((z : ℂ) : RiemannSphere)) (1 : ℂ) :=
    Finset.sum_congr rfl (fun i _ =>
      movingSummand_eq_g_sheetPullback ω₀ g (S.sheet i) (S.sheet_mdifferentiableAt i S.mem_V))
  rw [hgeo]
  -- The `g`-weighted finsum side = `g`-weighted sheet sum (fibre = range of sheets + frame identity).
  rw [S.fibre_eq _ S.mem_V, finsum_mem_range (S.sheet_inj _ S.mem_V), finsum_eq_sum_of_fintype]
  exact (Finset.sum_congr rfl (fun i _ => by
    rw [localCoeffLin_traceSummand_eq_sheetPullback ω₀ S i])).symm

/-! ### The αBr-free eventual sphere-sheet coherence at a branch value

The first conjunct of `hev_canonical_of_offBranch` — `valueChartTrace = fibreTrace(ofSphereSheetSystem)`
near `b₀` — *without* any `αBr`.  Built from the canonical-selection regular-value data exactly as
`hev_canonical_of_offBranch`, but ending in `valueChartTrace_eq_sphereSheetFibreTrace` (αBr-free) rather
than the αBr-bundled `hevBr_of_regularData`. -/

/-- **αBr-free eventual sphere-sheet coherence at a branch value (canonical selection).**  For `b₀` off
the pole-centres `cs` (and `br ⊇ branchValues f`), eventually each `z` near `b₀` carries a sphere sheet
system `S_z` with `valueChartTrace ω₀ f (canonical) z = (fibreTrace ω₀ f (ofSphereSheetSystem S_z …))
.traceCoeff z` — the regular-value coherence (NO global form `αBr`). -/
theorem hev_coherence_canonical_of_offBranch (hdiv : (f.div : Divisor X) ≠ 0) {m : ℕ} {cs : Fin m → ℂ}
    {br : Finset ℂ} (hbr : branchValues f hdiv ⊆ br) {b₀ : ℂ}
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j))) :
    ∀ᶠ z in 𝓝[≠] b₀,
      ∃ (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
        (hderiv : ∀ i, deriv (fun w => f.holoRepr
            ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
          ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
            (S.sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
        (_hmero : ∀ i, MeromorphicAt
          (fun w => g ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
          ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
            (S.sheet i (((z : ℂ) : RiemannSphere))))),
        valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z
          = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv _hmero)).traceCoeff z := by
  classical
  -- The off-branch sphere system at each regular value `z` (off `image cs ∪ br`).
  set Sreg : ∀ z, z ∉ Finset.univ.image cs ∪ br →
      Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)) := fun z hz =>
    (exists_sphereSheetSystem f (exists_orderAtPoint_ne_zero f hdiv)
      (coe_notMem_branchLocus_of_notMem_branchValues f hdiv
        (fun h => (fun hmem => hz (Finset.mem_union_right _ hmem)) (hbr h)))).some with hSreg
  have hoff : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere := fun z hz =>
    coe_notMem_branchLocus_of_notMem_branchValues f hdiv
      (fun h => (fun hmem => hz (Finset.mem_union_right _ hmem)) (hbr h))
  -- Each sheet point is a regular point of `f` (off-branch local injectivity).
  have hderivReg' : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      deriv (fun w => f.holoRepr
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0 := fun z hz i =>
    sheet_holoRepr_deriv_ne_zero f hdiv (hoff z hz)
      ((Sreg z hz).sheet_section i _ (Sreg z hz).mem_V)
  -- The sphere-sheet fibre point lies in the full fibre `F⁻¹(coe z)` (good value); `g`-data follows.
  have hmeroReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      MeromorphicAt (fun w => g
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))) := by
    intro z hz i
    have hfib : (Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)) ∈
        f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact (Sreg z hz).sheet_section i _ (Sreg z hz).mem_V
    rw [← canonicalFibreSelection_xs_range g f hdiv (hgood_reg z hz),
      canonicalFibreSelection_eq_ofFullFibre g f hdiv (hgood_reg z hz)] at hfib
    obtain ⟨j, hj⟩ := hfib
    have hpt : (Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)) = fullFibreEnum f hdiv z j := hj.symm
    rw [hpt]; exact (hgood_reg z hz).2 j
  -- The canonical-fibre conditions near each regular `z` (same as `hev_canonical_of_offBranch`).
  have hΦinjReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective (canonicalFibreSelection g f hdiv b').xs := fun z hz =>
    canonicalFibreSelection_hΦinjReg g f hdiv (hoff z hz) (hgmero_reg z hz)
  have hΦrangeReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Set.range (canonicalFibreSelection g f hdiv b').xs
        = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))} := fun z hz =>
    canonicalFibreSelection_hΦrangeReg g f hdiv (hoff z hz) (hgmero_reg z hz)
  have hsheetInjReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, Function.Injective
        (fun i => (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere))) := fun z hz => by
    have hVnhds : ((fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' (Sreg z hz).V) ∈ 𝓝 z :=
      (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds
        ((Sreg z hz).isOpen_V.mem_nhds (Sreg z hz).mem_V)
    filter_upwards [hVnhds] with b' hb'
    exact (Sreg z hz).sheet_inj (((b' : ℂ) : RiemannSphere)) hb'
  have hsheetMemReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      ∀ᶠ b' in 𝓝 z, ∀ i, (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere)) ∈
        (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source := fun z hz => by
    have hev : ∀ i : Fin (Sreg z hz).n, ∀ᶠ b' in 𝓝 z,
        (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere)) ∈
          (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source := by
      intro i
      have hcont : ContinuousAt ((Sreg z hz).holoReprSheet i) z :=
        ((Sreg z hz).holoReprSheet_contMDiffAt i).continuousAt
      have hsrc : (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source ∈
          𝓝 ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))) :=
        (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).open_source.mem_nhds
          (mem_chart_source ℂ _)
      have := hcont.preimage_mem_nhds (show
        (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source ∈
          𝓝 ((Sreg z hz).holoReprSheet i z) from hsrc)
      filter_upwards [this] with b' hb' using hb'
    rw [eventually_all]; exact hev
  -- Eventually `z ∉ image cs ∪ br` on `𝓝[≠] b₀`: the finite bad set minus `{b₀}` is closed, avoids `b₀`.
  have hfin : (((Finset.univ.image cs ∪ br : Finset ℂ) : Set ℂ) \ {b₀}).Finite :=
    ((Finset.univ.image cs ∪ br).finite_toSet).diff
  have hcompl : ((((Finset.univ.image cs ∪ br : Finset ℂ) : Set ℂ) \ {b₀}))ᶜ ∈ 𝓝 b₀ :=
    hfin.isClosed.compl_mem_nhds (by simp)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hcompl] with z hz_ne hz_compl
  have hzb : z ≠ b₀ := by simpa using hz_ne
  have hz : z ∉ Finset.univ.image cs ∪ br := by
    intro hmem
    exact hz_compl ⟨hmem, fun h => hzb (by simpa using h)⟩
  refine ⟨Sreg z hz, hderivReg' z hz, hmeroReg z hz, ?_⟩
  exact valueChartTrace_eq_sphereSheetFibreTrace ω₀ g f (canonicalFibreSelection g f hdiv)
    (Sreg z hz) (hderivReg' z hz) (hmeroReg z hz) (hΦinjReg z hz) (hΦrangeReg z hz)
    (hsheetInjReg z hz) (hsheetMemReg z hz)

/-! ### The SOUND branch-value boundedness `hbnd` (canonical selection, general `g`)

Assembling the sound `hbnd`: at a branch value `b₀` (off pole-centres), the geometric trace germ-equals
the `g`-weighted bundle finsum (αBr-free coherence + the finsum bridge), and the `g`-weighted bundle SUM
boundedness crux gives `(z − b₀)·trace → 0`.  The form fed to the crux is the GLOBAL HOLOMORPHIC `ω₀`;
`g` enters only as the bounded fibre weight (continuous at the branch fibre, off the pole-values). -/

/-- **The SOUND `hbnd` for the canonical selection at a branch value (general meromorphic `g`).**
For a genuine branch value `b₀ ∈ branchValues f` off the pole-centres `cs`, the canonical full-fibre
trace satisfies `(z − b₀)·valueChartTrace ω₀ f (canonical) z → 0`.  Discharged via:

* `hev_coherence_canonical_of_offBranch` — `valueChartTrace =ᶠ[𝓝[≠] b₀] fibreTrace(ofSphereSheetSystem)`
  (αBr-FREE);
* `fibreTrace_traceCoeff_eq_gWeighted_finsum` — `fibreTrace.traceCoeff z = ∑ᶠ g·localCoeffLin(traceSummand
  ω₀)`;
* `traceLocalCoeff_mul_sub_gWeighted_tendsto_zero_Y` — the `g`-weighted bundle SUM boundedness (the form
  is the GLOBAL HOLOMORPHIC `ω₀`; `g` is the bounded weight, continuous at the branch fibre off the
  pole-values).

NO global `αBr` — the SOUND replacement of `hbnd_canonical_of_offBranch` for general `α = ω₀·g`. -/
theorem hbnd_canonical_sound (hdiv : (f.div : Divisor X) ≠ 0) {m : ℕ} {cs : Fin m → ℂ}
    {br : Finset ℂ} (hbr : branchValues f hdiv ⊆ br) {b₀ : ℂ}
    (hb₀branch : b₀ ∈ branchValues f hdiv)
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_fibre : ∀ x ∈ f.toRiemannSphere ⁻¹' {(((b₀ : ℂ) : RiemannSphere))}, ContinuousAt g x) :
    Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z)
      (𝓝[≠] b₀) (𝓝 0) := by
  classical
  -- `coe b₀ ∈ branchLocus`.
  have hbrloc : (((b₀ : ℂ) : RiemannSphere)) ∈ branchLocus f.toRiemannSphere :=
    (mem_branchValues f hdiv).mp hb₀branch
  -- The g-weighted bundle SUM boundedness (sphere side), read at `coe b₀`.
  have hcruxY := Jacobians.TraceResidue.traceLocalCoeff_mul_sub_gWeighted_tendsto_zero_Y
    f.toRiemannSphere f.contMDiff_toRiemannSphere (hncF_of_div_ne_zero f hdiv) ω₀ g hbrloc hg_fibre
  -- Pull back along `coe : ℂ → RiemannSphere` (carries `𝓝[≠] b₀` to `𝓝[≠] (coe b₀)`).
  have hmap : Tendsto (fun z : ℂ => ((z : ℂ) : RiemannSphere)) (𝓝[≠] b₀)
      (𝓝[≠] (((b₀ : ℂ) : RiemannSphere))) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(OnePoint.continuous_coe.continuousAt).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz_ne
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcoe
    exact hz_ne (by rw [Set.mem_singleton_iff]; exact OnePoint.coe_injective hcoe)
  have hcrux := hcruxY.comp hmap
  -- Read in the affine value chart: `chart(coe b₀)(coe b₀) = b₀`, `coe z` is the sphere value.
  simp only [Function.comp_apply, RiemannSphere.chartAt_coe, RiemannSphere.chartCoe_apply_coe]
    at hcrux
  -- Transport along the eventual coherence + the g-weighted finsum bridge.
  refine hcrux.congr' ?_
  filter_upwards [hev_coherence_canonical_of_offBranch hdiv hbr hgood_reg hgmero_reg]
    with z hz
  obtain ⟨S, hderiv, hmero, hcoh⟩ := hz
  rw [hcoh, fibreTrace_traceCoeff_eq_gWeighted_finsum ω₀ g f S hderiv hmero (b₀ := b₀)]
  simp only [Function.comp_apply, RiemannSphere.chartCoe_apply_coe]

end Jacobians.Dolbeault.FormTraceGlobal
