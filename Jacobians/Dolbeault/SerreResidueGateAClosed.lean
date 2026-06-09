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
