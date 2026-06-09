/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueDirectGenus0GermDischarge
import Jacobians.Discharge.Manifold.CriticalSetDerivBridge

/-!
# Gate A `∑Res = 0` — the `∞`-coherence engine (§VIII.3 at `∞`, reciprocal chart)

`Jacobians.Dolbeault.SerreResidueTheorem.residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg`
(`SerreResidueDirectGenus0GermDischarge.lean`) reduced Gate A `∑Res = 0` (genus `0`, simple `∞`-poles,
canonical full-fibre selection) to *exactly* the genericity bookkeeping, the branch-value boundedness
`hbnd`, and the **`∞`-coherence** `hcoh_geom`:

> `recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0]
>    recipCoeff (inftyMovingSumNF ω₀ f (inftyFibreDataNF_full g f hsimpleInf hmeroInf))`,

the §VIII.3 `∞`-single-valuedness (the value-trace's reciprocal-chart germ at `∞` equals the
`∞`-moving-fibre-sum's germ).  This is the `∞`-analogue of the *finite* moving coherence `Cfull`, which
was discharged via the symmetric-invariance lever
(`MovingCoherenceDatum.ofSphereSheetSystemCanon` / `…coherent`), and has — unlike `Cfull` — **no
engine** yet in the repo (only the *reduction* `hcoh_inf_of_inftyMovingCoherenceNF`).

This file builds the `∞`-sheet-system engine, the reciprocal-chart analogue of the proven finite engine.

## Step (1) — `∞` is off the branch locus when all `∞`-poles are simple

`exists_sphereSheetSystem` (the off-branch sheet system) requires the value `∞` to be off the branch
locus.  A pole `a` with `orderAtPoint a = −1` (a **simple** pole) is a *regular point* of
`F = f.toRiemannSphere`: reading `F` near `a` in the `∞`-chart `chartInfty`, the chart pullback is the
reciprocal `1/f`, a zero of order `= the pole order = 1`, so its derivative is nonzero
(`deriv_ne_zero_of_analyticOrderAt_eq_one`), hence `F` is locally injective at `a`
(`injOn_nhds_of_deriv_ne_zero`, transported through the charts).  The fibre `F⁻¹{∞}` is exactly the
pole set; if *every* pole is simple, *no* pole is critical, so `∞ ∉ branchLocus F = F '' criticalSet F`.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `notMem_criticalSet_of_orderAtPoint_eq_neg_one` — a simple pole is off the critical set of
  `F = f.toRiemannSphere` (the analytic core: reciprocal chart-pullback derivative `≠ 0` ⟹ locally
  injective).
* `infty_notMem_branchLocus_of_simpleInfty` — `∞ ∉ branchLocus f.toRiemannSphere`, given that every pole
  is simple (`hsimpleInf`, via `inftyFibreEnum` enumerating all poles).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (the trace `Tr`; single-valued by
  symmetry; the trace = symmetric moving fibre-sum near each value, including `∞`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22 (local sheet systems), §5/§4.22 (the local
  normal form, reciprocal chart), §17.
* `Jacobians/ToSphereGeneral.lean` (`contMDiffAt_toRiemannSphere_at_pole`: the reciprocal chart pullback
  `chartInfty ∘ F ∘ chart⁻¹ =ᶠ N⁻¹`, order `−orderAtPoint`).
* `Jacobians/Discharge/Manifold/CriticalSetDerivBridge.lean` (`injOn_nhds_of_deriv_ne_zero`,
  `deriv_ne_zero_of_analyticOrderAt_eq_one`).
* `docs/gate_a_genus0_infty_vanishing_2026-06-09.md`, `human_input.md` (the construction map).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip RiemannSphere

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ## Step (1): `∞` is off the branch locus when all `∞`-poles are simple -/

/-- **The reciprocal chart pullback at a pole is analytic of order `−orderAtPoint`.**  At a pole `P`
(`orderAtPoint P < 0`), the chart pullback of `F = f.toRiemannSphere` in the `∞`-chart `chartInfty`,
`G := chartInfty ∘ F ∘ (chart P).symm`, is analytic at `chart P P` with analytic order equal to the
*natural number* `(−orderAtPoint P).toNat ≥ 1` — the reciprocal `1/f` has a zero of order `= the pole
order`.  This is the analytic local normal form at `∞`, extracted from the proof of
`contMDiffAt_toRiemannSphere_at_pole` (the punctured/centre germ-match `G =ᶠ N⁻¹`). -/
theorem analyticAt_chartInfty_toRiemannSphere_pullback_of_pole (f : MeromorphicFunction X) {P : X}
    (hP : f.orderAtPoint P < 0) :
    AnalyticAt ℂ (chartInfty ∘ (f.toRiemannSphere) ∘ (chartAt (H := ℂ) P).symm)
        ((chartAt (H := ℂ) P) P) ∧
      analyticOrderAt (chartInfty ∘ (f.toRiemannSphere) ∘ (chartAt (H := ℂ) P).symm)
        ((chartAt (H := ℂ) P) P) = (((-f.orderAtPoint P).toNat : ℕ) : ℕ∞) := by
  set φ := chartAt (H := ℂ) P with hφ
  set F := f.toFun ∘ φ.symm with hFdef
  have hxsrc : P ∈ φ.source := mem_chart_source ℂ P
  have hmeroF : MeromorphicAt F (φ P) := f.meromorphic P
  set n : ℤ := f.orderAtPoint P with hn
  have hn_neg : n < 0 := hP
  have hordF : meromorphicOrderAt F (φ P) = (n : ℤ) :=
    f.meromorphicOrderAt_chartPullback_of_pole hP
  set N := toMeromorphicNFAt F (φ P) with hNdef
  have hNF : MeromorphicNFAt N (φ P) := meromorphicNFAt_toMeromorphicNFAt
  have hordN : meromorphicOrderAt N (φ P) = (n : ℤ) := by
    rw [hNdef, meromorphicOrderAt_congr hmeroF.eq_nhdsNE_toMeromorphicNFAt.symm, hordF]
  have hNFinv : MeromorphicNFAt (fun w => (N w)⁻¹) (φ P) := by
    have := hNF.inv; simpa [Pi.inv_def] using this
  have hordNinv : meromorphicOrderAt (fun w => (N w)⁻¹) (φ P) = ((-n : ℤ)) := by
    have : meromorphicOrderAt (N⁻¹) (φ P) = -meromorphicOrderAt N (φ P) := meromorphicOrderAt_inv
    rw [hordN] at this; simpa [Pi.inv_def] using this
  have hnn_pos : (0 : ℤ) < -n := by omega
  have hNinvAna : AnalyticAt ℂ (fun w => (N w)⁻¹) (φ P) := by
    refine hNFinv.meromorphicOrderAt_nonneg_iff_analyticAt.1 ?_
    rw [hordNinv]; exact_mod_cast le_of_lt hnn_pos
  have hNinvZero : (N (φ P))⁻¹ = 0 := by
    by_contra hne
    rw [hNFinv.meromorphicOrderAt_eq_zero_iff.2 hne] at hordNinv
    rw [eq_comm, WithTop.coe_eq_zero] at hordNinv; omega
  -- The chart pullback `G` equals `N⁻¹` near `φ P` (punctured: both `=ᶠ (N ·)⁻¹`; centre: both `0`).
  set G : ℂ → ℂ := chartInfty ∘ (f.toRiemannSphere) ∘ φ.symm with hGdef
  have hGeq : (fun w => (N w)⁻¹) =ᶠ[𝓝 (φ P)] G := by
    rw [Filter.EventuallyEq, ← nhdsNE_sup_pure (φ P), Filter.eventually_sup]
    refine ⟨?_, ?_⟩
    · have hN_ne : ∀ᶠ w in 𝓝[≠] (φ P), N w ≠ 0 := by
        rw [← meromorphicOrderAt_ne_top_iff_eventually_ne_zero hNF.meromorphicAt, hordN]
        exact WithTop.coe_ne_top
      have hrepr : f.holoRepr ∘ φ.symm =ᶠ[𝓝[≠] (φ P)] N :=
        f.holoRepr_chartPullback_eventuallyEq_NFAt P
      have hcoe : (fun w => f.toRiemannSphere (φ.symm w)) =ᶠ[𝓝[≠] (φ P)]
          (fun w => ((f.holoRepr (φ.symm w) : ℂ) : RiemannSphere)) :=
        f.toRiemannSphere_chartPullback_eventuallyEq_coe P
      filter_upwards [hN_ne, hrepr, hcoe] with w hwN0 hwrepr hwcoe
      show (N w)⁻¹ = chartInfty (f.toRiemannSphere (φ.symm w))
      rw [hwcoe, show f.holoRepr (φ.symm w) = N w from hwrepr,
        RiemannSphere.chartInfty_apply_coe hwN0]
    · simp only [Filter.eventually_pure]
      rw [hNinvZero]
      show (0 : ℂ) = chartInfty (f.toRiemannSphere (φ.symm (φ P)))
      rw [φ.left_inv hxsrc, f.toRiemannSphere_of_pole hP, RiemannSphere.chartInfty_apply_infty]
  refine ⟨hNinvAna.congr hGeq, ?_⟩
  -- Order transfer: `analyticOrderAt G = analyticOrderAt N⁻¹`, and the meromorphic order `−n` pins it.
  rw [← analyticOrderAt_congr hGeq]
  -- `N⁻¹` analytic with meromorphic order `−n`, so its analytic order maps to `−n` under `ℕ → ℤ`.
  rw [hNinvAna.meromorphicOrderAt_eq] at hordNinv
  have hmapeq : ENat.map (Nat.cast : ℕ → ℤ) (analyticOrderAt (fun w => (N w)⁻¹) (φ P))
      = ENat.map (Nat.cast : ℕ → ℤ) ((((-n).toNat : ℕ)) : ℕ∞) := by
    rw [hordNinv]; simp [Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -n)]
  have := ENat.map_natCast_injective hmapeq
  rw [this, hn]

/-- **A simple pole is off the critical set** of `F = f.toRiemannSphere`.  At a pole `P` with
`orderAtPoint P = −1`, the reciprocal chart pullback `G = chartInfty ∘ F ∘ (chart P).symm` has analytic
order `1`, so `deriv G (chart P P) ≠ 0` (`deriv_ne_zero_of_analyticOrderAt_eq_one`), hence `G` is locally
injective at `chart P P` (`injOn_nhds_of_deriv_ne_zero`); transporting through the chart homeomorphisms
`chart P` (source) and `chartInfty` (target) — both `OpenPartialHomeomorph`s, injective on their
sources — `F` is locally injective at `P`, i.e. `P ∉ criticalSet F`. -/
theorem notMem_criticalSet_of_orderAtPoint_eq_neg_one (f : MeromorphicFunction X) {P : X}
    (hP : f.orderAtPoint P = -1) :
    P ∉ Jacobians.Discharge.Manifold.criticalSetGeneral f.toRiemannSphere := by
  set φ := chartAt (H := ℂ) P with hφ
  have hPneg : f.orderAtPoint P < 0 := by rw [hP]; norm_num
  obtain ⟨hGana, hGord⟩ := analyticAt_chartInfty_toRiemannSphere_pullback_of_pole f hPneg
  set G : ℂ → ℂ := chartInfty ∘ (f.toRiemannSphere) ∘ φ.symm with hGdef
  -- Order `1` from `orderAtPoint P = −1`.
  have hGord1 : analyticOrderAt G (φ P) = 1 := by
    rw [hGord, hP]; norm_num
  have hGderiv : deriv G (φ P) ≠ 0 :=
    Jacobians.Dolbeault.FormTraceInftyFibre.deriv_ne_zero_of_analyticOrderAt_eq_one hGana hGord1
  -- Local injectivity of `G` at `φ P`.
  obtain ⟨U, hU_nhds, hU_inj⟩ :=
    Jacobians.Discharge.Manifold.injOn_nhds_of_deriv_ne_zero hGana hGderiv
  -- `P ∉ criticalSet` = `∃ V ∈ 𝓝 P, InjOn F V`.
  show ¬ ¬ ∃ V ∈ 𝓝 P, Set.InjOn f.toRiemannSphere V
  rw [not_not]
  -- Pull `U` (a nbhd of `φ P` in the target chart) back to a nbhd `V` of `P` in `X`.
  -- `V := φ.source ∩ φ ⁻¹' U`; on `V`, `F = chartInfty.symm ∘ G ∘ φ` and `φ` lands in `U`.
  refine ⟨φ.source ∩ φ ⁻¹' U, ?_, ?_⟩
  · -- `V ∈ 𝓝 P`: `φ.source` open with `P ∈`, and `φ` continuous at `P` with `φ P ∈ U`.
    have h1 : φ.source ∈ 𝓝 P := φ.open_source.mem_nhds (mem_chart_source ℂ P)
    have h2 : φ ⁻¹' U ∈ 𝓝 P :=
      (φ.continuousAt (mem_chart_source ℂ P)).preimage_mem_nhds hU_nhds
    exact Filter.inter_mem h1 h2
  · -- `InjOn F V`: `F x = F y` ⟹ `G (φ x) = G (φ y)` (as `F = chartInfty.symm ∘ G ∘ φ`-ish on `V`) ⟹
    -- `φ x = φ y` (`G` injective on `U`) ⟹ `x = y` (`φ` injective on its source).
    intro x ⟨hxsrc, hxU⟩ y ⟨hysrc, hyU⟩ hFxy
    -- `G (φ x) = chartInfty (F x)` and `G (φ y) = chartInfty (F y)`.
    have hGx : G (φ x) = chartInfty (f.toRiemannSphere x) := by
      show chartInfty (f.toRiemannSphere (φ.symm (φ x))) = chartInfty (f.toRiemannSphere x)
      rw [φ.left_inv hxsrc]
    have hGy : G (φ y) = chartInfty (f.toRiemannSphere y) := by
      show chartInfty (f.toRiemannSphere (φ.symm (φ y))) = chartInfty (f.toRiemannSphere y)
      rw [φ.left_inv hysrc]
    have hGeq : G (φ x) = G (φ y) := by rw [hGx, hGy, hFxy]
    have hφeq : φ x = φ y := hU_inj hxU hyU hGeq
    exact φ.injOn hxsrc hysrc hφeq

/-- **`∞` is off the branch locus when every pole is simple.**  The fibre `F⁻¹{∞}` is exactly the pole
set of `f`, enumerated by `inftyFibreEnum`.  If every pole is simple (`hsimpleInf : ∀ i, orderAtPoint
(inftyFibreEnum f i) = −1`), then no pole is in `criticalSet F`
(`notMem_criticalSet_of_orderAtPoint_eq_neg_one`); since `branchLocus F = F '' criticalSet F` and every
preimage of `∞` is a pole, `∞ ∉ branchLocus F`. -/
theorem infty_notMem_branchLocus_of_simpleInfty (f : MeromorphicFunction X)
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1) :
    OnePoint.infty ∉ branchLocus f.toRiemannSphere := by
  rw [branchLocus, Set.mem_image]
  rintro ⟨a, ha_crit, ha_inf⟩
  -- `F a = ∞` ⟹ `a` is a pole ⟹ `a = inftyFibreEnum f i` for some `i` ⟹ `a` simple ⟹ `a ∉ criticalSet`.
  obtain ⟨i, hi⟩ := inftyFibreEnum_surj f ha_inf
  have ha_simple : f.orderAtPoint a = -1 := by rw [← hi]; exact hsimpleInf i
  exact notMem_criticalSet_of_orderAtPoint_eq_neg_one f ha_simple ha_crit

end Jacobians.Dolbeault.SerreResidueTheorem
