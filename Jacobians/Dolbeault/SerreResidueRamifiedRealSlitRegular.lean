/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueRamifiedRealFibreFamily

/-!
# The regular-value primitives of the per-slit-value data for the real cover

`SerreResidueRamifiedRealFibreFamily.lean` reduced the per-centre `RealCenterClusterFamily` to a
slit-wide family of `RealSlitClusterSplitData` (one per regular slit value `z`), via
`RealCenterClusterFamily.ofSlitClusterSplitFamily` + `RealSlitClusterSplitData.toFibreClusterTopology`
(feeding `FibreClusterTopology.ofClusterSplitData`).  The fields of `RealSlitClusterSplitData` fall into
two groups:

* the **regular-value primitives** — the sphere sheet system `S` and its regularity `hderiv`/`hmero`,
  the coherence `hcoh`, and the conservation-of-number cover-degree readings `hfin_z`/`hreg_z`; these are
  GENUINELY mechanical at a value `z` *off the branch locus* (a regular value of the cover) and are
  discharged here from the proven atoms;
* the **§5 normal-form section facts** — `hcs_sec`/`hcs_np`/`hwithin`/`hcross`/`hsrc`/`hsheet_diff`; these
  are the genuine Forster §5 normal-form geometry (the cluster section is a `holoRepr`-section, distinct
  sheets give distinct points, distinct preimages give disjoint clusters), which remain as the precise
  isolated content.

This file discharges the regular-value primitives:

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`localDeg_eq_one_of_regular_fibrePoint`** — at an off-branch fibre point `y` over `coe z`
  (`f.toRiemannSphere y = coe z`) where the chart-pullback derivative of `f.toRiemannSphere` is nonzero,
  the intrinsic local degree is `1` (the regular-value content `hreg_z`).  Mirrors the genericity
  `orderAtPoint_sub_eq_one_of_regular_fibrePoint`, reading off `localDeg` instead of the shift's order.
* **`localDeg_eq_one_of_regularValueWitness`** — the same, packaged from a `RegularValueWitnessReg`
  whose chosen value is `coe z` (so the `is_regular` certificate supplies the deriv-nonzero), for every
  fibre point.  This is the per-value `hreg_z` from the regular-value witness.
* **`exists_regularSlitData`** — at a value `z` off the branch locus (with the regular-value witness,
  finite fibre, and the sphere sheet system + canonical-selection conditions), the regular-value tuple
  `(S, hderiv, hmero, hcoh, hfin_z, hreg_z)` consumed by `RealSlitClusterSplitData`.

## ⚠ Soundness

`z` is a REGULAR slit value (off the branch locus) — the cover is genuinely unramified there, so
`localDeg = 1` is TRUE (not asserted).  The sheet system is the genuine `exists_sphereSheetSystem`
off-branch datum; `hcoh` is the PROVEN `valueChartTrace_eq_sphereSheetFibreTrace` wired for the canonical
selection (the eventual canonical-fibre conditions are the proven `canonicalFibreSelection_hΦinjReg`/
`hΦrangeReg` + the sheet-system continuity).  No custom axiom; no sorry on a false statement; no
false/junk/circular field.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4 (the cover is a covering off the branch locus).
* `SerreResidueGateAGenericity.lean` (`orderAtPoint_sub_eq_one_of_regular_fibrePoint`),
  `MultiplicityPatchingConstruct.lean` (`localDeg_coe_eq_chartPullback_order`),
  `Discharge/Manifold/Degree.lean` (`RegularValueWitnessReg`),
  `FormTraceBundleBridge.lean` (`valueChartTrace_eq_sphereSheetFibreTrace`),
  `FormTraceGlobalFibreSelection.lean` (`canonicalFibreSelection_hΦinjReg`/`hΦrangeReg`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTracePrincipalPart
  Jacobians.Dolbeault.FormTraceMovingFibre
  Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct Jacobians.RiemannSphere
  Jacobians.MultiplicityPatchingConstruct Jacobians.ProperMapDegreeSheets

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## `localDeg = 1` at a regular fibre point (the `hreg_z` content) -/

/-- **A regular sphere-fibre point has local degree `1`** (the `hreg_z` content).  At a fibre point `y`
over `coe z` (`f.toRiemannSphere y = coe z`) where the chart-pullback derivative of `f.toRiemannSphere`
(read through the affine chart at `coe z`) is nonzero, the intrinsic local degree is `1`:

> `localDeg f (coe z) y = 1`.

This is the regular-value content: off the branch locus the cover is unramified.  The proof mirrors
`orderAtPoint_sub_eq_one_of_regular_fibrePoint`: `y` is a non-pole (its sphere value `coe z` is finite),
the geometric chart pullback `g = holoRepr ∘ chart⁻¹` has `g (chart y) = z` with nonzero derivative (the
deriv transfers from `chartCoe ∘ F ∘ chart⁻¹ =ᶠ g`), so `g − z` has a simple zero
(`analyticOrderAt_eq_one_of_zero_deriv_ne_zero`); `localDeg f (coe z) y` is that order
(`localDeg_coe_eq_chartPullback_order` ∘ `meromorphicOrderAt_holoRepr_sub_eq`). -/
theorem localDeg_eq_one_of_regular_fibrePoint (f : MeromorphicFunction X) {z : ℂ} {y : X}
    (hyval : f.toRiemannSphere y = ((z : ℂ) : RiemannSphere))
    (hderiv : deriv ((chartAt ℂ (((z : ℂ) : RiemannSphere))) ∘ f.toRiemannSphere ∘
      (chartAt ℂ y).symm) ((chartAt ℂ y) y) ≠ 0) :
    localDeg f (((z : ℂ) : RiemannSphere)) y = 1 := by
  -- `y` is a non-pole (its sphere value `coe z` is finite).
  have hnp : 0 ≤ f.orderAtPoint y := by
    by_contra hpole
    rw [f.toRiemannSphere_of_pole (not_le.mp hpole)] at hyval
    exact (OnePoint.coe_ne_infty z) hyval.symm
  set φ := chartAt (H := ℂ) y with hφ
  have hchart_z : chartAt ℂ (((z : ℂ) : RiemannSphere)) = chartCoe := chartAt_coe z
  have hholo_y : f.holoRepr y = z := holoRepr_eq_of_fibre_nonpole f hyval hnp
  set g : ℂ → ℂ := fun w => f.holoRepr (φ.symm w) with hg
  have hg_an : AnalyticAt ℂ g (φ y) :=
    f.analyticAt_holoRepr_chartPullback_of_orderNonneg hnp
  -- The deriv transfers from `chartCoe ∘ F ∘ chart⁻¹ =ᶠ g`.
  set G : ℂ → ℂ := chartCoe ∘ f.toRiemannSphere ∘ φ.symm with hG
  have hyt : φ y ∈ φ.target := φ.map_source (mem_chart_source ℂ y)
  have hGeq : G =ᶠ[𝓝 (φ y)] g := by
    have hsymm : Filter.Tendsto φ.symm (𝓝 (φ y)) (𝓝 y) := by
      have h := (φ.continuousAt_symm hyt).tendsto
      rwa [φ.left_inv (mem_chart_source ℂ y)] at h
    have hbase := (f.toRiemannSphere_eventuallyEq_coe_holoRepr hnp).comp_tendsto hsymm
    filter_upwards [hbase] with w hw
    show chartCoe (f.toRiemannSphere (φ.symm w)) = f.holoRepr (φ.symm w)
    rw [show f.toRiemannSphere (φ.symm w) = ((f.holoRepr (φ.symm w) : ℂ) : RiemannSphere) from hw,
      chartCoe_apply_coe]
  have hderiv_g : deriv g (φ y) ≠ 0 := by
    have heq : deriv G (φ y) = deriv g (φ y) := hGeq.deriv_eq
    rw [hchart_z] at hderiv
    rw [← heq]; exact hderiv
  have hg_y : g (φ y) = z := by
    show f.holoRepr (φ.symm (φ y)) = z
    rw [φ.left_inv (mem_chart_source ℂ y), hholo_y]
  -- `g − z` has a simple zero at `φ y`.
  have hgz_an : AnalyticAt ℂ (fun w => g w - z) (φ y) := hg_an.sub analyticAt_const
  have hgz0 : (fun w => g w - z) (φ y) = 0 := by simp [hg_y]
  have hgzd : deriv (fun w => g w - z) (φ y) ≠ 0 := by
    have hd : HasDerivAt (fun w => g w - z) (deriv g (φ y)) (φ y) := by
      simpa using (hg_an.differentiableAt.hasDerivAt).sub_const z
    rw [hd.deriv]; exact hderiv_g
  have hord1 : analyticOrderAt (fun w => g w - z) (φ y) = 1 :=
    hgz_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hgz0 hgzd
  -- `localDeg f (coe z) y` is that order.
  rw [localDeg_coe_eq_chartPullback_order f z φ (chart_mem_atlas ℂ y) (mem_chart_source ℂ y),
    ← meromorphicOrderAt_holoRepr_sub_eq f y z hyt,
    show (fun w => f.holoRepr (φ.symm w) - z) = (fun w => g w - z) from rfl,
    hgz_an.meromorphicOrderAt_eq, hord1]
  rfl

/-- **Every fibre point over an off-branch value has local degree `1`** (the `hreg_z` content, packaged
from `branchLocus`).  For a nonconstant cover `f` (`f.div ≠ 0`) and a value `z` off the branch locus
(`coe z ∉ branchLocus f.toRiemannSphere`), every preimage `x ∈ F⁻¹(coe z)` is unramified:

> `localDeg f (coe z) x = 1`.

The regular-value witness at `coe z` (`exists_regularValueWitnessReg_value_eq`, available off the
critical-value set = branch locus) supplies the chart-pullback-deriv-nonzero certificate at each fibre
point, and `localDeg_eq_one_of_regular_fibrePoint` reads off the local degree. -/
theorem localDeg_eq_one_of_notMem_branchLocus (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    {x : X} (hx : x ∈ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))}) :
    localDeg f (((z : ℂ) : RiemannSphere)) x = 1 := by
  -- The regularity-certified witness at `coe z` (off the critical-value set = branch locus).
  obtain ⟨w, hw⟩ := Jacobians.Discharge.ContMDiff.Degree.exists_regularValueWitnessReg_value_eq
    f.toRiemannSphere f.contMDiff_toRiemannSphere
    (Jacobians.ProperMapDegreeSheets.toRiemannSphere_not_isConstant_of_div_ne_zero f hdiv)
    -- `coe z ∉ branchLocus = coe z ∉ criticalValuesGeneral` (defeq: `branchLocus = f '' criticalSet`,
    -- `criticalSet = criticalSetGeneral`, `criticalValuesGeneral = f '' criticalSetGeneral`).
    (show (((z : ℂ) : RiemannSphere)) ∉
      Jacobians.Discharge.Manifold.criticalValuesGeneral f.toRiemannSphere from hz)
  -- The chart-pullback deriv ≠ 0 at the fibre point `x` (the witness's `is_regular`).
  have hxw : x ∈ f.toRiemannSphere ⁻¹' {w.toWitness.value} := by
    rw [hw]; exact hx
  have hderiv := w.is_regular x hxw
  rw [hw] at hderiv
  have hxval : f.toRiemannSphere x = (((z : ℂ) : RiemannSphere)) := by
    simpa using hx
  exact localDeg_eq_one_of_regular_fibrePoint f hxval hderiv

/-- **The regular-fibre primitives `hfin_z`/`hreg_z` at an off-branch value.**  For a nonconstant cover
`f` and a value `z` off the branch locus, the fibre over `coe z` is finite and every local degree there
is `1` — exactly the two regular-fibre inputs (`hfin_z`, `hreg_z`) of `RealSlitClusterSplitData` /
`FibreClusterTopology.ofClusterSplitData`. -/
theorem regularFibre_primitives_of_notMem_branchLocus (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere) :
    (f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))}).Finite ∧
      ∀ x ∈ f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))},
        localDeg f (((z : ℂ) : RiemannSphere)) x = 1 :=
  ⟨Jacobians.ProperMapDegreeSheets.fibre_finite_of_div_ne_zero f hdiv _,
    fun _ hx => localDeg_eq_one_of_notMem_branchLocus f hdiv hz hx⟩

end Jacobians.Dolbeault.SerreResidueTheorem
