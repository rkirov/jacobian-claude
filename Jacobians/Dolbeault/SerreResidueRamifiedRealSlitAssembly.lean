/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueRamifiedRealSlitRegular

/-!
# Assembling `RealCenterClusterFamily` from the §5 normal-form section facts (the precise residual)

`SerreResidueRamifiedRealSlitRegular.lean` discharged the **regular-value primitives** of
`RealSlitClusterSplitData` (`hderiv`/`hmero`/`hcoh`/`hfin_z`/`hreg_z`/`hsheet_diff`) at any slit value
`z` off the branch locus, via `RealSlitClusterSplitData.ofRegularValue`.  This file performs the
remaining bookkeeping reduction: it packages the genuinely-remaining **§5 normal-form section facts** as a
single per-slit-value predicate `RealSlitSectionData` and assembles a `RealCenterClusterFamily` from a
slit-wide family of them.

After this file, the per-centre obligation `RealCenterClusterFamily` (hence the residue theorem
`∑Res = 0`, via `residueSum_eq_zero_of_realCenterClusterFamily` + the PROVEN genericity
`existsAdaptedFRamified`) reduces to **exactly**:

* a small slit `Sset` accumulating at `c`, off the branch locus, with a sphere sheet system per value;
* the cluster data `Cl` (the §5 normal form, e.g. from `ClusterTraceData.ofFibrePointNormalForm`) of
  matching multiplicity, with its residue split `hsplit0` and the meromorphy bound `hbnd`;
* per regular slit value, the **§5 section facts** `RealSlitSectionData` — the cluster section is a
  `holoRepr`-section (`hcs_sec`) at a non-pole (`hcs_np`), with within-cluster and cross-cluster
  distinctness (`hwithin`/`hcross`) and chart-target locality (`hsrc`).

This is the precise irreducible content — the genuine Forster §5 normal-form geometry on a slit near a
ramified centre; everything else (the residue calculus, the conservation-of-number `hcard`, the
off-centre/∞ machinery, the regular-value primitives, the genericity) is PROVEN.

## ⚠ Soundness

`Sset` is a slit accumulating at `c`, off the branch locus (so the regular-value primitives apply at every
`z ∈ Sset`).  The §5 section facts are the genuine normal-form geometry — the cluster sections are
genuine local sections of `f.holoRepr` (the §5 atom `exists_clusterSplit_at_fibrePoint`), distinct at
distinct sheets/preimages (the primitive root + T2 separation).  No custom axiom; no sorry on a false
statement; no false/junk/circular field.  The genuine non-vacuity is the standard slit-near-`c` regime,
where the §5 normal form holds for the cluster arguments `ζʲ·w₀ z → 0`.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4–5.
* `SerreResidueRamifiedRealSlitRegular.lean` (`RealSlitClusterSplitData.ofRegularValue`),
  `SerreResidueRamifiedRealFibreFamily.lean` (`RealCenterClusterFamily.ofSlitClusterSplitFamily`,
  `RealCoverClusterGeometry`, `residueTheorem_of_realCoverClusterGeometry`).
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

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The per-slit-value §5 normal-form section facts (the irreducible residual) -/

/-- **The §5 normal-form section facts at one regular slit value `z`** (the precise residual).  Bundles,
for the whole-fibre cluster data `D = realFibreData g hdiv c hnp` and the §5 cluster data `Cl` on the slit
`Sset`, exactly the fields of `RealSlitClusterSplitData.ofRegularValue` that are NOT discharged by the
regular-value primitives:

* `hcs_sec` — the cluster section is a genuine local section of `f.holoRepr` near `z` (the §5 normal-form
  section property `f.holoRepr (clusterSection … w) = w`);
* `hcs_np` — the cluster section is a non-pole at `z`;
* `hwithin`/`hcross` — within-cluster injectivity (the §5 straightening uniqueness) and cross-cluster
  separation (distinct preimages give disjoint clusters);
* `hsrc` — the cluster sheet value stays in the fixed preimage's chart target near `z`.

The regular-value primitives (`hderiv`/`hmero`/`hcoh`/`hfin_z`/`hreg_z`) and the cluster-sheet
differentiability (`hsheet_diff`) are discharged by `RealSlitClusterSplitData.ofRegularValue`. -/
structure RealSlitSectionData (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ) {Sset : Set ℂ}
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i))
    (Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset) (z : ℂ) where
  /-- The cluster section is a genuine local section of `f.holoRepr` near `z` (§5 normal form). -/
  hcs_sec : ∀ (i : (realFibreData g hdiv c hnp).ι) (j : Fin ((realFibreData g hdiv c hnp).mult i)),
    ∀ᶠ w in 𝓝 z, f.holoRepr (clusterSection (realFibreData g hdiv c hnp) Cl i j w) = w
  /-- The cluster section is a non-pole at `z` (`0 ≤ orderAtPoint`). -/
  hcs_np : ∀ (i : (realFibreData g hdiv c hnp).ι) (j : Fin ((realFibreData g hdiv c hnp).mult i)),
    0 ≤ f.orderAtPoint (clusterSection (realFibreData g hdiv c hnp) Cl i j z)
  /-- Within-cluster injectivity at `z` (§5 straightening uniqueness). -/
  hwithin : ∀ (i : (realFibreData g hdiv c hnp).ι)
    (j k : Fin ((realFibreData g hdiv c hnp).mult i)),
    clusterSection (realFibreData g hdiv c hnp) Cl i j z
        = clusterSection (realFibreData g hdiv c hnp) Cl i k z → j = k
  /-- Cross-cluster separation at `z` (distinct preimages give disjoint clusters). -/
  hcross : ∀ (i i' : (realFibreData g hdiv c hnp).ι)
    (j : Fin ((realFibreData g hdiv c hnp).mult i)) (k : Fin ((realFibreData g hdiv c hnp).mult i')),
    i ≠ i' → clusterSection (realFibreData g hdiv c hnp) Cl i j z
      ≠ clusterSection (realFibreData g hdiv c hnp) Cl i' k z
  /-- The cluster sheet value stays in the fixed preimage's chart target near `z`. -/
  hsrc : ∀ (i : (realFibreData g hdiv c hnp).ι) (j : Fin ((realFibreData g hdiv c hnp).mult i)),
    ∀ᶠ w in 𝓝 z, clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j w
      ∈ (chartAt ℂ ((realFibreData g hdiv c hnp).xs i)).target

/-- **`RealSlitClusterSplitData` from a `RealSlitSectionData` at an off-branch slit value.**  Feeds the §5
section facts together with a sphere sheet system into `RealSlitClusterSplitData.ofRegularValue` (which
discharges the regular-value primitives + `hsheet_diff`). -/
noncomputable def RealSlitSectionData.toClusterSplitData {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0} {c : ℂ}
    {Sset : Set ℂ} {hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)}
    {Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset} {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere) (hz_slit : z ∈ Sset)
    (hmult : ∀ i, (Cl i).m = (realFibreData g hdiv c hnp).mult i)
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (P : RealSlitSectionData ω₀ g hdiv c hnp Cl z) :
    RealSlitClusterSplitData ω₀ g hdiv c hnp Cl z :=
  RealSlitClusterSplitData.ofRegularValue hz hz_slit hmult S
    P.hcs_sec P.hcs_np P.hwithin P.hcross P.hsrc

/-! ## Assembling `RealCenterClusterFamily` from the slit-wide §5 section data -/

/-- **`RealCenterClusterFamily` from a slit-wide §5 section-data family** (the precise residual assembly).
At a finite pole-value centre `c`, given:

* `Sset`/`hS_acc` — a slit accumulating at `c`, off the branch locus (`hSset_offBranch`), with a sphere
  sheet system per value (`hSsys`);
* `hanalytic`/`hbnd`/`ppord` — the eventual analyticity and pole-order bound of the geometric trace;
* `Cl`/`hmult`/`hsplit0` — the §5 cluster data of matching multiplicity, with its residue split;
* `hsec` — per regular slit value `z ∈ Sset`, the §5 section facts `RealSlitSectionData`;

build the per-centre `RealCenterClusterFamily`.  Each slit value's `FibreClusterTopology` is assembled by
`RealSlitSectionData.toClusterSplitData` (the regular-value primitives discharged) →
`RealSlitClusterSplitData.toFibreClusterTopology` (the conservation-of-number `hcard` proven internally) →
`RealCenterClusterFamily.ofSlitClusterSplitFamily`.

This isolates the per-centre residual to **exactly** the §5 section facts on the slit (plus the standard
meromorphy bookkeeping `hanalytic`/`hbnd`/`hsplit0` and the slit-near-`c` construction). -/
noncomputable def RealCenterClusterFamily.ofRegularSlitData {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {f : MeromorphicFunction X} {hdiv : (f.div : Divisor X) ≠ 0}
    {poles : Finset X} {c : ℂ}
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i))
    (hanalytic : ∀ᶠ z in 𝓝[≠] c,
      AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv)) z)
    {Sset : Set ℂ} (hS_acc : ∃ᶠ z in 𝓝[≠] c, z ∈ Sset)
    (hSset_offBranch : ∀ z ∈ Sset, (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hSsys : ∀ z ∈ Sset, Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset)
    (hmult : ∀ i, (Cl i).m = (realFibreData g hdiv c hnp).mult i)
    (hsplit0 : ∀ i, straightenedIntegrand ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) (Cl i).s
        =ᶠ[𝓝[≠] 0] fun u => negTail 0 (Cl i).ppb (Cl i).ppN u + (Cl i).ppR u)
    (ppord : ℕ)
    (hbnd : Tendsto (fun z => (z - c) ^ ppord *
      valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv) z) (𝓝[≠] c) (𝓝 0))
    (hsec : ∀ z ∈ Sset, RealSlitSectionData ω₀ g hdiv c hnp Cl z) :
    RealCenterClusterFamily ω₀ g hdiv poles c :=
  RealCenterClusterFamily.ofSlitClusterSplitFamily hnp hanalytic hS_acc Cl hmult hsplit0 ppord hbnd
    (fun z hz => (hsec z hz).toClusterSplitData (hSset_offBranch z hz) hz hmult (hSsys z hz))

end Jacobians.Dolbeault.SerreResidueTheorem
