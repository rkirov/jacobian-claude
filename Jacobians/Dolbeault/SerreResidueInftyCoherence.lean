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
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTraceFullFibre
  Jacobians.Dolbeault.FormTraceMovingFibre RiemannSphere

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

/-- **A `LocalSheetSystem` of `F = f.toRiemannSphere` at `∞`**, from simple `∞`-poles.  Since `∞ ∉
branchLocus F` (`infty_notMem_branchLocus_of_simpleInfty`) and `F` is a nonconstant holomorphic map to
`ℂℙ¹` (`f.div ≠ 0`), Forster §4.22 (`exists_localSheetSystem`) provides the moving sheets sweeping the
`∞`-fibre over a sphere neighbourhood `V ∋ ∞`.  This is the `∞`-analogue of `exists_sphereSheetSystem`
(specialized to finite values); it is the geometric source of an `InftyMovingCoherenceData` (the moving
sheets supply the index bijection at `∞`), exactly as the finite sphere sheet system supplies the finite
`Cfull` datum via `ofSphereSheetSystemCanon`. -/
theorem exists_inftySheetSystem (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1) :
    Nonempty (Jacobians.LocalSheetSystem f.toRiemannSphere OnePoint.infty) :=
  Jacobians.exists_localSheetSystem f.toRiemannSphere f.contMDiff_toRiemannSphere
    (f.toRiemannSphere_not_isConstant (exists_orderAtPoint_ne_zero f hdiv))
    (infty_notMem_branchLocus_of_simpleInfty f hsimpleInf)

/-! ## The reduction of `hcoh_geom` to the large-`z` diagonal

The target `∞`-coherence is `recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF
ω₀ f Dinf)`.  Since `recipCoeff R ζ = −R(ζ⁻¹)·ζ⁻²` depends on `R` *only* through `R(ζ⁻¹)`, this is
*equivalent* to the underlying functions agreeing for large `z` (i.e. at `ζ⁻¹`, `ζ → 0`):

> `∀ᶠ ζ in 𝓝[≠] 0, valueChartTrace ω₀ f Φ (ζ⁻¹) = inftyMovingSumNF ω₀ f Dinf (ζ⁻¹)`.

This is the honest, non-circular residual: the §VIII.3 statement "the trace = the moving `∞`-fibre sum near
`∞`" read in the value coordinate (large `z`).  It is a germ-equality on a *punctured* neighbourhood of
`0` (equivalently: for `|z|` large), **never evaluating at `∞` itself** — so no junk-value defect (the
value-trace reads `g` at the moving fibre points `Φ z`, all genuine non-`∞` points for large finite `z`).
And it is the moving-fibre-sum identity, *not* the residue cancellation — non-circular. -/

/-- **`hcoh_geom` from the large-`z` diagonal.**  `recipCoeff R₁ =ᶠ[𝓝[≠] 0] recipCoeff R₂` whenever the
functions agree at `ζ⁻¹` for `ζ` near `0` (`hdiag_inf`): both `recipCoeff`s are `−·(ζ⁻¹)·ζ⁻²`, so the
shared `R(ζ⁻¹)` value makes them equal.  This is the clean reduction of the `∞`-coherence `hcoh_geom` to
the large-`z` value-trace / `∞`-moving-sum agreement (the genuine §VIII.3 `∞`-single-valuedness). -/
theorem recipCoeff_eventuallyEq_of_eventuallyEq_inv {R₁ R₂ : ℂ → ℂ}
    (hdiag_inf : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), R₁ (ζ⁻¹) = R₂ (ζ⁻¹)) :
    recipCoeff R₁ =ᶠ[𝓝[≠] 0] recipCoeff R₂ := by
  filter_upwards [hdiag_inf] with ζ hζ
  show -(R₁ (ζ⁻¹)) * ζ ^ (-2 : ℤ) = -(R₂ (ζ⁻¹)) * ζ ^ (-2 : ℤ)
  rw [hζ]

/-- **`hcoh_geom` from the large-`z` diagonal (the `inftyFibreDataNF_full` instance).**  Specialization of
`recipCoeff_eventuallyEq_of_eventuallyEq_inv` to the value trace `R₁ := valueChartTrace ω₀ f Φ` and the
`∞`-moving sum `R₂ := inftyMovingSumNF ω₀ f Dinf`, giving the exact `hcoh_geom` shape consumed by
`residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg`. -/
theorem hcoh_geom_of_diagonalInfty (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (Dinf : InftyFibreDataNF g f)
    (hdiag_inf : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      valueChartTrace ω₀ f Φ (ζ⁻¹) = inftyMovingSumNF ω₀ f Dinf (ζ⁻¹)) :
    recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf) :=
  recipCoeff_eventuallyEq_of_eventuallyEq_inv hdiag_inf

/-! ## Step (3a): the `∞`-moving sum as a fixed-chart moving fibre sum (reciprocal-chart bookkeeping)

The `∞`-moving sum `inftyMovingSumNF ω₀ f Dinf z = ∑ i, chartIntegrand ω₀ g (Dinf.xs i) (recipSheet i
(z⁻¹))·deriv (w ↦ recipSheet i (w⁻¹)) z` reads the *reciprocal-chart* planar sections `recipSheet i :=
(inftyFibreTraceNF ω₀ f Dinf).sheet i` (the planar inverses of the repaired reciprocals `recip i`, with
`recipSheet i 0 = chart (Dinf.xs i)(Dinf.xs i)`).  Define the **manifold sections** through the
`∞`-fibre poles, `inftyManifoldSec i z := (chart (Dinf.xs i)).symm (recipSheet i (z⁻¹))`.  For `z⁻¹` near
`0` (i.e. `z` large), `recipSheet i (z⁻¹)` lies in `chart (Dinf.xs i).target` (continuity, since
`recipSheet i 0 = chart (Dinf.xs i)(Dinf.xs i) ∈ target`), so the chart and its inverse cancel:

* `chart (Dinf.xs i)(inftyManifoldSec i z) = recipSheet i (z⁻¹)`;
* `deriv (w ↦ chart (Dinf.xs i)(inftyManifoldSec i w)) z = deriv (w ↦ recipSheet i (w⁻¹)) z`.

Hence `inftyMovingSumNF ω₀ f Dinf z = ∑ i, chartIntegrand ω₀ g (Dinf.xs i) (chart (Dinf.xs i)
(inftyManifoldSec i z))·deriv (w ↦ chart (Dinf.xs i)(inftyManifoldSec i w)) z` — the **fixed-chart moving
fibre sum** along `inftyManifoldSec`, the exact RHS shape that `traceCoeff_diagonal_eq_fixedSum`
produces.  This is pure reciprocal-chart bookkeeping (no monodromy), discharged in full. -/

/-- **The manifold sections through the `∞`-fibre poles.**  `inftyManifoldSec ω₀ f Dinf i z` is the
manifold point on the `i`-th `∞`-fibre sheet over the value `z`: the chart inverse (at the pole `Dinf.xs
i`) of the reciprocal-chart planar section `recipSheet i` evaluated at the reciprocal coordinate `z⁻¹`.
For `z` large (`z⁻¹` near `0`), `recipSheet i (z⁻¹)` is near the chart-target point `pre i`, so this is a
genuine manifold point near the pole `Dinf.xs i`. -/
noncomputable def inftyManifoldSec (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) : ℂ → X :=
  fun z => (chartAt ℂ (Dinf.xs i)).symm ((inftyFibreTraceNF ω₀ f Dinf).sheet i (z⁻¹))

/-- **The reciprocal section value at `0` is the pole's chart image** (`recipSheet i 0 = pre i =
chart (Dinf.xs i)(Dinf.xs i)`). -/
theorem recipSheet_zero (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    (inftyFibreTraceNF ω₀ f Dinf).sheet i 0 = (chartAt ℂ (Dinf.xs i)) (Dinf.xs i) := by
  have := (inftyFibreTraceNF ω₀ f Dinf).sheet_base i
  rwa [inftyFibreTraceNF_b, inftyFibreTraceNF_pre] at this

/-- **Eventually (`ζ` near `0`), the reciprocal section lands in the pole's chart target.**  At `ζ = 0`
it is `recipSheet i 0 = pre i = chart (Dinf.xs i)(Dinf.xs i) ∈ target` (`recipSheet_zero`); continuity of
`recipSheet i` (analytic at `0`) and openness of the target extend this to a neighbourhood of `0`. -/
theorem eventually_recipSheet_mem_target (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ),
      (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target := by
  have hmem : (inftyFibreTraceNF ω₀ f Dinf).sheet i 0 ∈ (chartAt ℂ (Dinf.xs i)).target := by
    rw [recipSheet_zero]; exact (chartAt ℂ (Dinf.xs i)).map_source (mem_chart_source ℂ (Dinf.xs i))
  have hcont : ContinuousAt ((inftyFibreTraceNF ω₀ f Dinf).sheet i) 0 := by
    have han := (inftyFibreTraceNF ω₀ f Dinf).sheet_analytic i
    rw [inftyFibreTraceNF_b] at han
    exact han.continuousAt
  exact hcont.eventually_mem ((chartAt ℂ (Dinf.xs i)).open_target.mem_nhds hmem)

/-- **The reciprocal section is analytic (hence continuous) on a punctured neighbourhood of `0`.**  The
`inftyFibreTraceNF` sheets are `AnalyticAt 0`; analyticity propagates to a full neighbourhood
(`AnalyticAt.eventually_analyticAt`). -/
theorem eventually_recipSheet_analyticAt (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) :
    ∀ᶠ ζ in 𝓝 (0 : ℂ), AnalyticAt ℂ ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ := by
  have han := (inftyFibreTraceNF ω₀ f Dinf).sheet_analytic i
  rw [inftyFibreTraceNF_b] at han
  exact han.eventually_analyticAt

/-! ## Step (3a): the `∞`-moving sum as a fixed-chart moving fibre sum (reciprocal-chart bookkeeping)

The `∞`-moving sum `inftyMovingSumNF ω₀ f Dinf z = ∑ i, chartIntegrand ω₀ g (Dinf.xs i) (recipSheet i
(z⁻¹))·deriv (w ↦ recipSheet i (w⁻¹)) z` reads the reciprocal-chart planar sections `recipSheet i :=
(inftyFibreTraceNF ω₀ f Dinf).sheet i`.  Via the manifold sections `inftyManifoldSec i z =
(chart (Dinf.xs i)).symm (recipSheet i (z⁻¹))`, for `z` large (`z⁻¹` near `0`, so `recipSheet i (z⁻¹) ∈
chart (Dinf.xs i).target`) the chart cancels and `inftyMovingSumNF ω₀ f Dinf z` *equals the fixed-chart
moving fibre sum* along `inftyManifoldSec` — the RHS shape `traceCoeff_diagonal_eq_fixedSum` produces.
Pure reciprocal-chart bookkeeping (no monodromy). -/

/-- **The `∞`-moving sum equals the fixed-chart moving fibre sum** along `inftyManifoldSec`, at `z = ζ⁻¹`
(`ζ ≠ 0`), given the chart-target memberships: the per-`i` value membership `hmem`
(`recipSheet i ζ ∈ target`) for the value factor, and the eventual membership `hmemEv`
(`recipSheet i (w⁻¹) ∈ target` for `w` near `ζ⁻¹`) for the derivative factor.  Both come from
`eventually_recipSheet_mem_target` for `ζ` small enough.  *Proof.*  Termwise: the value factor's argument
`recipSheet i ζ = chart (Dinf.xs i)(inftyManifoldSec i (ζ⁻¹))` (chart∘symm cancellation at the target
point); the derivative factor's functions agree near `ζ⁻¹` (same cancellation), so equal derivatives. -/
theorem inftyMovingSumNF_eq_fixedSum (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) {ζ : ℂ} (hζ : ζ ≠ 0)
    (hmem : ∀ i, (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target)
    (hmemEv : ∀ i, ∀ᶠ w in 𝓝 (ζ⁻¹),
      (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹) ∈ (chartAt ℂ (Dinf.xs i)).target) :
    inftyMovingSumNF ω₀ f Dinf (ζ⁻¹)
      = ∑ i, chartIntegrand ω₀ g (Dinf.xs i)
            ((chartAt ℂ (Dinf.xs i)) (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)))
          * deriv (fun w => (chartAt ℂ (Dinf.xs i)) (inftyManifoldSec ω₀ f Dinf i w)) (ζ⁻¹) := by
  show (∑ i, chartIntegrand ω₀ g (Dinf.xs i) ((inftyFibreTraceNF ω₀ f Dinf).sheet i ((ζ⁻¹)⁻¹))
        * deriv (fun w => (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹)) (ζ⁻¹)) = _
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inv_inv]
  congr 1
  · -- value factor: `recipSheet i ζ = chart (Dinf.xs i)(inftyManifoldSec i (ζ⁻¹))`.
    rw [show (chartAt ℂ (Dinf.xs i)) (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))
          = (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ from by
        unfold inftyManifoldSec; rw [inv_inv, (chartAt ℂ (Dinf.xs i)).right_inv (hmem i)]]
  · -- derivative factor: the two functions agree near `ζ⁻¹`.
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hmemEv i] with w hw
    show (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹)
      = (chartAt ℂ (Dinf.xs i)) (inftyManifoldSec ω₀ f Dinf i w)
    unfold inftyManifoldSec
    rw [(chartAt ℂ (Dinf.xs i)).right_inv hw]

/-! ## Step (3b): the `∞`-analogue of `traceCoeff_diagonal_eq_fixedSum` (bare fixed frame)

`traceCoeff_diagonal_eq_fixedSum` (`FormTraceMovingFibre`) proves the *finite* diagonal identity — the
re-selected fibre trace equals the fixed-chart moving fibre sum — but ties the fixed chart frame to a
`FibreRegularData` over a *finite* base value.  At `∞` the natural fixed frame is the **pole set**
`Dinf.xs` (mapping to `∞`, *not* a finite-value fibre), so we transcribe `traceCoeff_diagonal_eq_fixedSum`
with the chart frame supplied as a *bare* indexed family `xsD : ιD → X` (the proof never uses the analytic
fields of the reference `FibreRegularData` — only its `ι`/`xs` as the chart frame and the explicit
index-bijection + chart-membership hypotheses).  This is the §VIII.3 well-definedness lever
(`movingSummand_chartIndep`) read with the pole charts as the fixed frame. -/

/-- **Diagonal trace = fixed-(bare-)frame moving fibre sum.**  Generalization of
`traceCoeff_diagonal_eq_fixedSum` with the fixed chart frame a bare `xsD : ιD → X` (instead of a
`FibreRegularData`'s fibre points).  Verbatim transcription of the finite proof (which uses only the
frame's `ι`/`xs` and the explicit hypotheses — never the reference fibre's analytic fields).  The
re-selected fibre `D'` over `b'`, the index bijection `e : D'.ι ≃ ιD`, the section identification
(`hxs`/`hsheet_deriv`), and the chart membership/transitions (`hmem`/`htrans_diff`/`htrans_diff_inv`)
discharge the diagonal via `movingSummand_chartIndep`. -/
theorem traceCoeff_diagonal_eq_fixedFrame {ιD : Type} [Fintype ιD] (xsD : ιD → X)
    (sec : ιD → ℂ → X) {b' : ℂ}
    (D' : FibreRegularData g f b') (e : D'.ι ≃ ιD)
    (hxs : ∀ i', D'.xs i' = sec (e i') b')
    (hsheet_deriv : ∀ i', deriv ((fibreTrace ω₀ f D').sheet i') b'
      = deriv (fun z => (chartAt ℂ (sec (e i') b')) (sec (e i') z)) b')
    (hcont : ∀ i, ContinuousAt (sec i) b')
    (hsP_diff : ∀ i, DifferentiableAt ℂ (fun z => (chartAt ℂ (sec i b')) (sec i z)) b')
    (hmem : ∀ i, sec i b' ∈ (chartAt ℂ (xsD i)).source)
    (htrans_diff : ∀ i, DifferentiableAt ℂ
      (fun w => (chartAt ℂ (xsD i)) ((chartAt ℂ (sec i b')).symm w)) ((chartAt ℂ (sec i b')) (sec i b')))
    (htrans_diff_inv : ∀ i, DifferentiableAt ℂ
      (fun w => (chartAt ℂ (sec i b')) ((chartAt ℂ (xsD i)).symm w)) ((chartAt ℂ (xsD i)) (sec i b'))) :
    (fibreTrace ω₀ f D').traceCoeff b'
      = ∑ i, chartIntegrand ω₀ g (xsD i) ((chartAt ℂ (xsD i)) (sec i b'))
        * deriv (fun z => (chartAt ℂ (xsD i)) (sec i z)) b' := by
  have hdiagsum : (fibreTrace ω₀ f D').traceCoeff b'
      = ∑ i', chartIntegrand ω₀ g (D'.xs i') ((chartAt ℂ (D'.xs i')) (D'.xs i'))
        * deriv ((fibreTrace ω₀ f D').sheet i') b' := by
    show (∑ i', (fibreTrace ω₀ f D').coeff i' ((fibreTrace ω₀ f D').sheet i' b')
        * deriv ((fibreTrace ω₀ f D').sheet i') b') = _
    refine Finset.sum_congr rfl (fun i' _ => ?_)
    rw [fibreTrace_coeff,
      show (fibreTrace ω₀ f D').sheet i' b' = (chartAt ℂ (D'.xs i')) (D'.xs i') from
        (fibreTrace ω₀ f D').sheet_base i']
  rw [hdiagsum]
  rw [← Equiv.sum_comp e (fun i => chartIntegrand ω₀ g (xsD i) ((chartAt ℂ (xsD i)) (sec i b'))
    * deriv (fun z => (chartAt ℂ (xsD i)) (sec i z)) b')]
  refine Finset.sum_congr rfl (fun i' _ => ?_)
  rw [hxs i', hsheet_deriv i']
  have hself_diff : DifferentiableAt ℂ
      (fun w => (chartAt ℂ (sec (e i') b')) ((chartAt ℂ (sec (e i') b')).symm w))
      ((chartAt ℂ (sec (e i') b')) (sec (e i') b')) := by
    have heqid : (fun w => (chartAt ℂ (sec (e i') b')) ((chartAt ℂ (sec (e i') b')).symm w))
        =ᶠ[𝓝 ((chartAt ℂ (sec (e i') b')) (sec (e i') b'))] id := by
      filter_upwards [(chartAt ℂ (sec (e i') b')).open_target.mem_nhds
        ((chartAt ℂ (sec (e i') b')).map_source (mem_chart_source ℂ (sec (e i') b')))] with w hw
      simp only [(chartAt ℂ (sec (e i') b')).right_inv hw, id_eq]
    exact (differentiableAt_id).congr_of_eventuallyEq heqid
  exact movingSummand_chartIndep ω₀ g (sec (e i')) (sec (e i') b') (xsD (e i')) (hcont (e i'))
    (hsP_diff (e i')) (mem_chart_source ℂ (sec (e i') b')) (hmem (e i')) hself_diff
    (htrans_diff (e i')) hself_diff (htrans_diff_inv (e i'))

/-- **`inftyManifoldSec i (ζ⁻¹)` lies in the pole's chart source.**  It is `(chart (Dinf.xs i)).symm
(recipSheet i ζ)` and `recipSheet i ζ ∈ chart (Dinf.xs i).target`, so its chart inverse lands in the
source (`PartialEquiv.map_target`). -/
theorem inftyManifoldSec_mem_source (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) {ζ : ℂ}
    (hmem : (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target) :
    inftyManifoldSec ω₀ f Dinf i (ζ⁻¹) ∈ (chartAt ℂ (Dinf.xs i)).source := by
  unfold inftyManifoldSec
  rw [inv_inv]
  exact (chartAt ℂ (Dinf.xs i)).map_target hmem

/-! ## Step (3c): the per-`ζ` diagonal `valueChartTrace (ζ⁻¹) = inftyMovingSumNF (ζ⁻¹)`

Combining the bare-frame diagonal (`traceCoeff_diagonal_eq_fixedFrame`, with the pole charts `Dinf.xs` as
the fixed frame and the manifold sections `inftyManifoldSec`) and the reciprocal-chart bookkeeping
(`inftyMovingSumNF_eq_fixedSum`), the per-`ζ` diagonal identity holds *given the index bijection + section
identification at `ζ`* (the genuine §VIII.3 `∞`-monodromy content — the reciprocal-chart analogue of the
finite `diagonal_of_pointwiseBijection`). -/

/-- **The per-`ζ` `∞`-diagonal.**  For `ζ ≠ 0` with the chart memberships (`hmem`/`hmemEv`), and the index
bijection `e : (Φ ζ⁻¹).ι ≃ Dinf.ι` matching the re-selected fibre `Φ ζ⁻¹` over the value `ζ⁻¹` to the
`∞`-fibre poles along the manifold sections `inftyManifoldSec` (`hxs`/`hsheet_deriv` + the chart
differentiability), the value trace equals the `∞`-moving sum at `ζ⁻¹`:

> `valueChartTrace ω₀ f Φ (ζ⁻¹) = inftyMovingSumNF ω₀ f Dinf (ζ⁻¹)`. -/
theorem diagonalInfty_pointwise (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (Dinf : InftyFibreDataNF g f)
    {ζ : ℂ} (hζ : ζ ≠ 0)
    (hmem : ∀ i, (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target)
    (hmemEv : ∀ i, ∀ᶠ w in 𝓝 (ζ⁻¹),
      (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹) ∈ (chartAt ℂ (Dinf.xs i)).target)
    (e : (Φ (ζ⁻¹)).ι ≃ Dinf.ι)
    (hxs : ∀ i', (Φ (ζ⁻¹)).xs i' = inftyManifoldSec ω₀ f Dinf (e i') (ζ⁻¹))
    (hsheet_deriv : ∀ i', deriv ((fibreTrace ω₀ f (Φ (ζ⁻¹))).sheet i') (ζ⁻¹)
      = deriv (fun z => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf (e i') (ζ⁻¹)))
          (inftyManifoldSec ω₀ f Dinf (e i') z)) (ζ⁻¹))
    (hcont : ∀ i, ContinuousAt (inftyManifoldSec ω₀ f Dinf i) (ζ⁻¹))
    (hsP_diff : ∀ i, DifferentiableAt ℂ (fun z => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)))
        (inftyManifoldSec ω₀ f Dinf i z)) (ζ⁻¹))
    (htrans_diff : ∀ i, DifferentiableAt ℂ
      (fun w => (chartAt ℂ (Dinf.xs i)) ((chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))).symm w))
        ((chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))) (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))))
    (htrans_diff_inv : ∀ i, DifferentiableAt ℂ
      (fun w => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))) ((chartAt ℂ (Dinf.xs i)).symm w))
        ((chartAt ℂ (Dinf.xs i)) (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)))) :
    valueChartTrace ω₀ f Φ (ζ⁻¹) = inftyMovingSumNF ω₀ f Dinf (ζ⁻¹) := by
  rw [valueChartTrace_apply,
    traceCoeff_diagonal_eq_fixedFrame (xsD := Dinf.xs) (sec := inftyManifoldSec ω₀ f Dinf)
      (D' := Φ (ζ⁻¹)) e hxs hsheet_deriv hcont hsP_diff
      (fun i => inftyManifoldSec_mem_source ω₀ f Dinf i (hmem i)) htrans_diff htrans_diff_inv,
    inftyMovingSumNF_eq_fixedSum ω₀ f Dinf hζ hmem hmemEv]

/-! ## Step (4): the `∞`-moving-coherence datum and the `hcoh_geom` assembly

We package the residual §VIII.3 `∞`-monodromy content — the *eventually-quantified index bijection +
section identification at `∞`* — into one structure `InftyMovingCoherenceData`, exactly mirroring the
finite `MovingCoherenceDatum.ofBijection`'s `hbij`.  Its single content field is, for `ζ` in a punctured
neighbourhood of `0` (large `z = ζ⁻¹`), an index bijection `e : (Φ ζ⁻¹).ι ≃ Dinf.ι` matching the
re-selected fibre `Φ ζ⁻¹` over `ζ⁻¹` to the `∞`-fibre poles along the manifold sections
`inftyManifoldSec`, plus the section identification (`hxs`/`hsheet_deriv`) and the chart-pullback
differentiability.  The chart-target memberships are discharged *internally* (from the analyticity of the
reciprocal sections near `0`, `eventually_recipSheet_analyticAt`, and `eventually_recipSheet_mem_target`),
so the caller supplies only the genuine monodromy.

From such a datum, `hcoh_geom` follows: the per-`ζ` diagonal (`diagonalInfty_pointwise`) gives
`valueChartTrace (ζ⁻¹) = inftyMovingSumNF (ζ⁻¹)` for `ζ` near `0`, and `hcoh_geom_of_diagonalInfty`
upgrades that large-`z` agreement to the reciprocal-chart germ-equality `hcoh_geom`. -/

/-- **A single-`i` `hmemEv` from continuity at `ζ`.**  Given the reciprocal section continuous at `ζ`
(`hcont`) with `recipSheet i ζ ∈ chart (Dinf.xs i).target` (`hmemζ`), the chart-target membership of
`recipSheet i (w⁻¹)` holds for `w` near `ζ⁻¹` (`w ↦ w⁻¹` continuous at `ζ⁻¹`, value `ζ`; openness of the
target). -/
theorem hmemEv_of_cont (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreDataNF g f) (i : Dinf.ι) {ζ : ℂ} (hζ : ζ ≠ 0)
    (hcont : ContinuousAt ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ)
    (hmemζ : (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target) :
    ∀ᶠ w in 𝓝 (ζ⁻¹), (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹) ∈ (chartAt ℂ (Dinf.xs i)).target := by
  have hinvcont : ContinuousAt (fun w : ℂ => w⁻¹) (ζ⁻¹) := continuousAt_inv₀ (inv_ne_zero hζ)
  have hcompcont : ContinuousAt (fun w => (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹)) (ζ⁻¹) := by
    have : (fun w : ℂ => (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹))
        = ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ∘ (fun w : ℂ => w⁻¹) := rfl
    rw [this]; refine ContinuousAt.comp ?_ hinvcont; rwa [inv_inv]
  refine hcompcont.eventually_mem ?_
  show (chartAt ℂ (Dinf.xs i)).target ∈ 𝓝 ((inftyFibreTraceNF ω₀ f Dinf).sheet i (ζ⁻¹)⁻¹)
  rw [inv_inv]
  exact (chartAt ℂ (Dinf.xs i)).open_target.mem_nhds hmemζ

/-- **The `∞`-moving-coherence datum** (the §VIII.3 `∞`-monodromy obligation, packaged).  For a global
fibre selection `Φ` and the `∞`-fibre data `Dinf`, the data exhibiting the value trace as the moving
`∞`-fibre sum near `∞`: an *eventually-quantified* (in `ζ` near `0`, i.e. large `z = ζ⁻¹`) index bijection
`e : (Φ ζ⁻¹).ι ≃ Dinf.ι` matching the re-selected fibre to the `∞`-fibre poles along the manifold sections
`inftyManifoldSec`, with the section identification and chart-pullback differentiability.  This is the
reciprocal-chart analogue of the finite `MovingCoherenceDatum.ofBijection` `hbij` field — the genuine
remaining `∞`-content (the continuously-varying index bijection at `∞`).  The chart-target memberships are
*not* fields (discharged internally from analyticity of the reciprocal sections near `0`). -/
structure InftyMovingCoherenceData (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) (Dinf : InftyFibreDataNF g f)
    where
  /-- **The eventually-quantified index bijection + section identification at `∞`.** -/
  hbij : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ), ∃ e : (Φ (ζ⁻¹)).ι ≃ Dinf.ι,
    (∀ i', (Φ (ζ⁻¹)).xs i' = inftyManifoldSec ω₀ f Dinf (e i') (ζ⁻¹)) ∧
    (∀ i', deriv ((fibreTrace ω₀ f (Φ (ζ⁻¹))).sheet i') (ζ⁻¹)
      = deriv (fun z => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf (e i') (ζ⁻¹)))
          (inftyManifoldSec ω₀ f Dinf (e i') z)) (ζ⁻¹)) ∧
    (∀ i, ContinuousAt (inftyManifoldSec ω₀ f Dinf i) (ζ⁻¹)) ∧
    (∀ i, DifferentiableAt ℂ (fun z => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)))
        (inftyManifoldSec ω₀ f Dinf i z)) (ζ⁻¹)) ∧
    (∀ i, DifferentiableAt ℂ
      (fun w => (chartAt ℂ (Dinf.xs i)) ((chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))).symm w))
        ((chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))) (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹)))) ∧
    (∀ i, DifferentiableAt ℂ
      (fun w => (chartAt ℂ (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))) ((chartAt ℂ (Dinf.xs i)).symm w))
        ((chartAt ℂ (Dinf.xs i)) (inftyManifoldSec ω₀ f Dinf i (ζ⁻¹))))

/-- **`hcoh_geom` from an `∞`-moving-coherence datum.**  The per-`ζ` diagonal
(`diagonalInfty_pointwise`) holds for `ζ` near `0` (the datum's `hbij` + the internally-discharged chart
memberships), giving `valueChartTrace (ζ⁻¹) = inftyMovingSumNF (ζ⁻¹)` eventually; `hcoh_geom_of_diagonalInfty`
upgrades it to the reciprocal-chart germ-equality `hcoh_geom`.  This is the assembled §VIII.3
`∞`-single-valuedness — the reciprocal-chart analogue of `MovingCoherenceDatum.coherent`. -/
theorem hcoh_geom_of_inftyMovingCoherenceData (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (Dinf : InftyFibreDataNF g f)
    (C : InftyMovingCoherenceData ω₀ g f Φ Dinf) :
    recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf) := by
  classical
  refine hcoh_geom_of_diagonalInfty ω₀ f Φ Dinf ?_
  -- The chart-target memberships (eventually near `0`): analyticity + target membership of the
  -- reciprocal sections, both eventual near `0`.
  have hmemAll : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      ∀ i, AnalyticAt ℂ ((inftyFibreTraceNF ω₀ f Dinf).sheet i) ζ
        ∧ (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target := by
    rw [Filter.eventually_all]
    intro i
    exact nhdsWithin_le_nhds
      ((eventually_recipSheet_analyticAt ω₀ f Dinf i).and (eventually_recipSheet_mem_target ω₀ f Dinf i))
  filter_upwards [C.hbij, hmemAll, self_mem_nhdsWithin] with ζ hbij hmemAll hζ0
  have hζ : ζ ≠ 0 := by simpa using hζ0
  obtain ⟨e, hxs, hsheet_deriv, hcont, hsP_diff, htrans_diff, htrans_diff_inv⟩ := hbij
  -- Discharge the per-`i` memberships from `hmemAll`.
  have hmem : ∀ i, (inftyFibreTraceNF ω₀ f Dinf).sheet i ζ ∈ (chartAt ℂ (Dinf.xs i)).target :=
    fun i => (hmemAll i).2
  have hmemEv : ∀ i, ∀ᶠ w in 𝓝 (ζ⁻¹),
      (inftyFibreTraceNF ω₀ f Dinf).sheet i (w⁻¹) ∈ (chartAt ℂ (Dinf.xs i)).target :=
    fun i => hmemEv_of_cont ω₀ f Dinf i hζ (hmemAll i).1.continuousAt (hmemAll i).2
  exact diagonalInfty_pointwise ω₀ f Φ Dinf hζ hmem hmemEv e hxs hsheet_deriv hcont hsP_diff
    htrans_diff htrans_diff_inv

/-! ## Step (5): wiring the `∞`-coherence datum into the genus-`0` capstone

Replacing the bare `∞`-coherence hypothesis `hcoh_geom` of
`residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg` by an
`InftyMovingCoherenceData` (at `Φ := canonicalFibreSelection`, `Dinf := inftyFibreDataNF_full`), the deep
`∞`-coherence is now reduced — *soundly* — to the genuine §VIII.3 `∞`-monodromy datum (the
continuously-varying index bijection at `∞`), the reciprocal-chart analogue of the finite `Cfull` datum.
This is the most-reduced genus-`0` Gate A capstone: every analytic heart is now a *geometric datum* (the
finite `Cfull`/`hreg` discharged by the symmetric lever; the `∞`-coherence reduced to its monodromy
datum), with only `hbnd` and the discrete genericity bookkeeping remaining as named obligations. -/

/-- **Gate A `∑Res = 0` (genus `0`, simple `∞`-poles, canonical selection) with the `∞`-coherence reduced
to its moving-coherence datum.**  Identical to `residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg`
except the bare `∞`-coherence `hcoh_geom` is replaced by an `InftyMovingCoherenceData` `Cinf` (at the
canonical selection and the full `∞`-fibre data) — the §VIII.3 `∞`-monodromy obligation (the
continuously-varying index bijection at `∞`).  `hcoh_geom` is recovered internally by
`hcoh_geom_of_inftyMovingCoherenceData`.  This is the reciprocal-chart analogue of discharging the finite
`Cfull` from `movingCoherenceDatum_canonical`: the deep `∞`-coherence is now a geometric datum, not an
opaque germ-hypothesis. -/
theorem residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyData
    (hdiv : (f.div : Divisor X) ≠ 0)
    (hgood : ∀ p, (∃ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      GoodValue g f hdiv p)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ) (hbr : branchValues f hdiv ⊆ br)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hoff_cs : ∀ i, (((cs i : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hc_good : ∀ i, GoodValue g f hdiv (cs i))
    (hgmero : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∀ j,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an_offpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x))
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i)))
    (hnonpole_inf_an : ∀ k, inftyFibreEnum f k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (inftyFibreEnum f k)).symm z))
        ((chartAt ℂ (inftyFibreEnum f k)) (inftyFibreEnum f k)))
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z)
        (𝓝[≠] b₀) (𝓝 0))
    (Cinf : InftyMovingCoherenceData ω₀ g f (canonicalFibreSelection g f hdiv)
      (inftyFibreDataNF_full g f hsimpleInf hmeroInf)) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg hdiv hgood m cs ρ hcs_ball hcs_inj
    br hbr hcenters_cs hoff_cs hc_good hgmero hgood_reg hgmero_reg hg_an_offpoles hsimpleInf hmeroInf
    hnonpole_inf_an hbnd
    (hcoh_geom_of_inftyMovingCoherenceData ω₀ f (canonicalFibreSelection g f hdiv)
      (inftyFibreDataNF_full g f hsimpleInf hmeroInf) Cinf)

end Jacobians.Dolbeault.SerreResidueTheorem
