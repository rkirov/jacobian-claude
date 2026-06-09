/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueRamifiedFullFibreReindexBuilder
import Jacobians.Dolbeault.SerreResidueRamifiedFibreConservation
import Jacobians.Dolbeault.SerreResidueRamifiedMultiplicityBridge

/-!
# The per-centre §5-data assembly for the real cover (feeding the SOUND `∑Res = 0` capstone)

`SerreResidueRamifiedFullFibreReindexBuilder.lean` reduced Gate-A `∑Res = 0`, for the real cover, to the
per-centre SOUND residual `FullFibreCenterReindex`, built by `ofFibreClusterTopologyFamily_adaptedFRamified`
from, at each finite pole-value centre `c`:

* a slit `Sset` accumulating at `c`;
* the WHOLE pole-value fibre `D : FibreRamifiedData g f c` (all `deg f` preimages — non-poles drop out at
  the residue level via `hnonpole_of_adaptedFRamified`);
* per-preimage cluster data `Cl i : ClusterTraceData ω₀ g (D.xs i) c Sset`;
* a slit-wide `FibreClusterTopology` family `hfam : ∀ z ∈ Sset, FibreClusterTopology … D Cl z`.

This file performs that per-centre assembly for the **real** canonical cover, discharging the genuinely
constructible parts and isolating the irreducible per-slit conservation-of-number geometry.

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`realFibreData`** — the WHOLE pole-value fibre `D` as a genuine `FibreRamifiedData g.toFun f c`: the
  index is `Fin (fullFibreCard f hdiv c)` (the whole sphere fibre `F⁻¹(coe c)`), the preimages are
  `fullFibreEnum`, the multiplicities are the genuine intrinsic local degrees
  `mult i = (localDeg f (coe c) (xs i)).toNat`, with `g.toFun`'s chart pullback meromorphic at each
  (`g.meromorphic`).  Injective (`fullFibreEnum_injective`), range the whole fibre
  (`fullFibreEnum_range`), surjective onto poles.  This is the SOUND whole fibre — NOT poles only.
* **`realFibreData_mult_pos_of_nonpole`** — at a non-pole preimage the multiplicity is `≥ 1` (the
  multiplicity bridge); ⇒ `D.hmult_pos`.
* **`RealCenterClusterFamily`** — the precise per-centre residual as a named predicate: the slit, the
  whole-fibre `D`, the per-preimage `Cl`, and the slit-wide `FibreClusterTopology` family (the genuine
  §4 conservation-of-number + §5 normal-form geometry).  **Not** asserted.
* **`FullFibreCenterReindex.ofRealCenterClusterFamily`** — builds the SOUND per-centre residual from a
  `RealCenterClusterFamily`, via `ofFibreClusterTopologyFamily_adaptedFRamified` (`hnonpole` automatic).
* **`residueSum_eq_zero_of_realCenterClusterFamily`** — Gate-A `∑Res = 0` from an `AdaptedFRamified`
  datum + a per-centre `RealCenterClusterFamily`, anchoring the precise remaining content.

## ⚠ Soundness

`D` = the WHOLE fibre `F⁻¹(coe c)` (all `deg f` preimages — NOT poles).  The multiplicities are the
genuine intrinsic `localDeg` (the §17.9 conservation-of-number multiplicity, the one
`exists_properMapDegree` is built from), never ad-hoc.  No `hD_mem` (no all-poles assumption — the #17
fix).  The cluster data / topology family is the SAME genuine §5/§4 content the capstone consumes; this
file constructs the real-cover `D`/slit and isolates the per-slit topology as `RealCenterClusterFamily`.
No custom axiom; no sorry on a false statement; no false/junk/circular field.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4 (conservation of number), §5 (`z = wᵐ`), §17.
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (3.1, Lemma 3.2).
* `SerreResidueRamifiedFullFibreReindexBuilder.lean`
  (`FullFibreCenterReindex.ofFibreClusterTopologyFamily_adaptedFRamified`,
  `residueSum_eq_zero_of_fullFibreReindex_adaptedFRamified`),
  `SerreResidueRamifiedFibreConservation.lean` (`FibreClusterTopology.ofClusterSplitData`),
  `SerreResidueRamifiedMultiplicityBridge.lean` (`analyticOrderAt_holoRepr_sub_eq_mult`),
  `FormTraceGlobalFibreSelection.lean` (`fullFibreEnum`, `fullFibreCard`).
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
  Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The WHOLE pole-value fibre as a genuine `FibreRamifiedData` (the SOUND `D`)

At a finite value-centre `c` of a non-constant cover `f` (`f.div ≠ 0`), the sphere fibre `F⁻¹(coe c)` is
finite (`fibre_finite_of_div_ne_zero`).  We enumerate it by `fullFibreEnum` and equip each preimage with
its genuine intrinsic ramification multiplicity `(localDeg f (coe c) ·).toNat`.  For the numerator a
genuine meromorphic `g : MeromorphicFunction X`, `g.toFun`'s chart pullback is meromorphic at every
preimage (`g.meromorphic`).  This is the SOUND whole fibre — *all* `deg f` preimages, NOT poles only. -/

/-- **The genuine intrinsic multiplicity of a non-pole fibre preimage is positive.**  At a preimage `p`
over `coe c` with `0 ≤ f.orderAtPoint p` (a non-pole — the case at a finite value-centre), the
multiplicity bridge gives `1 ≤ (localDeg f (coe c) p).toNat`. -/
theorem realFibre_mult_pos {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ}
    {p : X} (hp_fib : f.toRiemannSphere p = ((c : ℂ) : RiemannSphere)) (hp_np : 0 ≤ f.orderAtPoint p) :
    0 < (localDeg f ((c : ℂ) : RiemannSphere) p).toNat :=
  (Jacobians.analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np).1

/-- **The WHOLE pole-value fibre `D` for the real cover** (the SOUND `D`).  At a finite value-centre `c`
of a non-constant cover `f` (`f.div ≠ 0`) where **every** fibre preimage is a non-pole (`hnp` — true at
a finite value-centre, where `coe c ≠ ∞`), the whole sphere fibre `F⁻¹(coe c)` is a genuine
`FibreRamifiedData g.toFun f c`:

* index `Fin (fullFibreCard f hdiv c)`, preimages `fullFibreEnum f hdiv c`;
* multiplicities the genuine intrinsic `localDeg` (`mult i = (localDeg f (coe c) (xs i)).toNat`);
* `g.toFun`'s chart pullback meromorphic at each preimage (`g.meromorphic`).

**Soundness:** the whole fibre (all `deg f` preimages), the genuine `localDeg` multiplicities — NOT an
all-poles assumption.  The non-pole hypothesis `hnp` is true at any finite value-centre. -/
noncomputable def realFibreData (g : MeromorphicFunction X) {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)) :
    FibreRamifiedData g.toFun f c where
  ι := Fin (fullFibreCard f hdiv c)
  fintype_ι := inferInstance
  xs := fullFibreEnum f hdiv c
  hmem := fullFibreEnum_mem f hdiv c
  mult := fun i => (localDeg f ((c : ℂ) : RiemannSphere) (fullFibreEnum f hdiv c i)).toNat
  hmult_pos := fun i => realFibre_mult_pos hdiv (fullFibreEnum_mem f hdiv c i) (hnp i)
  hg_mero := fun i => by
    -- `g.toFun`'s chart pullback is meromorphic at every point (`g.meromorphic`).
    have h := g.meromorphic (fullFibreEnum f hdiv c i)
    simpa [Function.comp] using h

@[simp] theorem realFibreData_xs (g : MeromorphicFunction X) {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)) (i) :
    (realFibreData g hdiv c hnp).xs i = fullFibreEnum f hdiv c i := rfl

@[simp] theorem realFibreData_mult (g : MeromorphicFunction X) {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)) (i) :
    (realFibreData g hdiv c hnp).mult i
      = (localDeg f ((c : ℂ) : RiemannSphere) (fullFibreEnum f hdiv c i)).toNat := rfl

/-- `realFibreData.xs` is injective (`fullFibreEnum_injective`). -/
theorem realFibreData_inj (g : MeromorphicFunction X) {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)) :
    Function.Injective (realFibreData g hdiv c hnp).xs :=
  fullFibreEnum_injective f hdiv c

/-- `realFibreData.xs` has range exactly the sphere fibre `F⁻¹(coe c)` (`fullFibreEnum_range`). -/
theorem realFibreData_range (g : MeromorphicFunction X) {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ)
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)) :
    Set.range (realFibreData g hdiv c hnp).xs
      = f.toRiemannSphere ⁻¹' {(((c : ℂ) : RiemannSphere))} :=
  fullFibreEnum_range f hdiv c

/-- **Pole surjectivity of the whole fibre** (`hD_surj`).  Every preimage `a` of `coe c` (in particular
every α-pole there) is enumerated by `realFibreData.xs`, since the range is the whole fibre. -/
theorem realFibreData_surj (g : MeromorphicFunction X) {f : MeromorphicFunction X}
    (hdiv : (f.div : Divisor X) ≠ 0) (c : ℂ) {poles : Finset X}
    (hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)) :
    ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) →
      ∃ i, (realFibreData g hdiv c hnp).xs i = a := by
  intro a _ ha
  have : a ∈ Set.range (realFibreData g hdiv c hnp).xs := by
    rw [realFibreData_range g hdiv c hnp]; exact ha
  exact this

/-! ## The precise per-centre residual `RealCenterClusterFamily` (the genuine remaining geometry)

We isolate, as a named predicate, exactly the per-centre data the SOUND capstone
`FullFibreCenterReindex.ofFibreClusterTopologyFamily_adaptedFRamified` consumes for the real cover at one
finite pole-value centre `c`: the slit `Sset` accumulating at `c`, the per-preimage cluster data `Cl` on
the WHOLE-fibre `D = realFibreData …`, the residue-split / meromorphy bookkeeping, and the slit-wide
`FibreClusterTopology` family (the genuine §4 conservation-of-number + §5 normal-form geometry, built per
slit value by `FibreClusterTopology.ofClusterSplitData`).  **Not** asserted — it is the named target. -/

/-- **The precise per-centre cluster-family residual for the real cover** at a finite pole-value centre
`c`.  Bundles, for the WHOLE-fibre `D = realFibreData g hdiv c hnp`:

* `hnp` — every fibre preimage is a non-pole (true at a finite value-centre `coe c ≠ ∞`);
* `Sset`/`hS_acc` — a slit accumulating at `c` (the simply-connected punctured-disk-minus-a-ray where the
  `m`-th-root branches live);
* `hanalytic` — eventual off-centre analyticity of the geometric trace (the meromorphy input);
* `Cl`/`hmult`/`hsplit0` — per-preimage genuine §5 cluster data of matching `localDeg` multiplicity, with
  the residue split on `𝓝[≠] 0`;
* `ppord`/`hbnd` — a finite pole-order bound feeding the meromorphy;
* `hfam` — a slit-wide `FibreClusterTopology` family (the conservation-of-number geometry, `hcard = deg f`).

This is the genuine remaining content the `∑Res = 0` close needs at each centre; everything outside it
(the residue calculus, the off-centre/∞ machinery, the genericity `AdaptedFRamified`) is PROVEN. -/
structure RealCenterClusterFamily (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0) (poles : Finset X) (c : ℂ) where
  /-- Every fibre preimage over `coe c` is a non-pole (true at a finite value-centre). -/
  hnp : ∀ i, 0 ≤ f.orderAtPoint (fullFibreEnum f hdiv c i)
  /-- The eventual off-centre analyticity of the geometric trace. -/
  hanalytic : ∀ᶠ z in 𝓝[≠] c,
    AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv)) z
  /-- The slit on which the per-cluster branches are defined. -/
  Sset : Set ℂ
  /-- The slit accumulates at `c`. -/
  hS_acc : ∃ᶠ z in 𝓝[≠] c, z ∈ Sset
  /-- The per-preimage genuine §5 cluster data on the slit. -/
  Cl : ∀ i, ClusterTraceData ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) c Sset
  /-- The cluster multiplicity matches the genuine `localDeg` fibre multiplicity. -/
  hmult : ∀ i, (Cl i).m = (realFibreData g hdiv c hnp).mult i
  /-- The principal-part split of each straightened integrand on `𝓝[≠] 0`. -/
  hsplit0 : ∀ i, straightenedIntegrand ω₀ g.toFun ((realFibreData g hdiv c hnp).xs i) (Cl i).s
      =ᶠ[𝓝[≠] 0] fun u => negTail 0 (Cl i).ppb (Cl i).ppN u + (Cl i).ppR u
  /-- The pole order of the geometric trace at `c`. -/
  ppord : ℕ
  /-- The finite pole-order bound feeding the meromorphy. -/
  hbnd : Tendsto (fun z => (z - c) ^ ppord *
    valueChartTrace ω₀ f (canonicalFibreSelection g.toFun f hdiv) z) (𝓝[≠] c) (𝓝 0)
  /-- **The slit-wide conservation-of-number topology family** (the genuine §4/§5 geometry). -/
  hfam : ∀ z ∈ Sset,
    FibreClusterTopology (canonicalFibreSelection g.toFun f hdiv) (realFibreData g hdiv c hnp) Cl z

/-- **The SOUND per-centre residual `FullFibreCenterReindex` from a `RealCenterClusterFamily`.**  Feeds
the real-cover whole-fibre `D = realFibreData …`, the per-preimage cluster data, the meromorphy bound,
the slit, the pole surjectivity (automatic from the whole-fibre range), and the slit-wide
`FibreClusterTopology` family into `ofFibreClusterTopologyFamily_adaptedFRamified` (so `hnonpole` is
automatic from `A.hg_an_offpoles`).  **No `hD_mem` (no all-poles assumption)** — `D` is the whole fibre,
non-poles drop out at the residue level. -/
noncomputable def FullFibreCenterReindex.ofRealCenterClusterFamily {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} (A : AdaptedFRamified ω₀ g poles) {c : ℂ}
    (R : RealCenterClusterFamily ω₀ g A.hdiv poles c) :
    FullFibreCenterReindex ω₀ g.toFun A.f A.hdiv poles c :=
  FullFibreCenterReindex.ofFibreClusterTopologyFamily_adaptedFRamified A R.hanalytic
    (realFibreData g A.hdiv c R.hnp) (realFibreData_inj g A.hdiv c R.hnp)
    (realFibreData_surj g A.hdiv c R.hnp) R.hS_acc R.Cl R.hmult R.hsplit0 R.ppord R.hbnd R.hfam

/-- **Gate-A `∑Res = 0` from an `AdaptedFRamified` + per-centre `RealCenterClusterFamily`** (the SOUND
real-cover close, modulo the per-slit conservation-of-number geometry).  For a genuine meromorphic
numerator `g`, an `AdaptedFRamified` datum `A`, and at each finite pole-value centre `A.cs i` a
`RealCenterClusterFamily` (the slit + whole-fibre `D` + per-preimage §5 cluster data + slit-wide
`FibreClusterTopology` family), the total residue of `α = ω₀·g` vanishes:

> `∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0`.

This anchors the precise remaining content of the residue theorem for the real cover to **exactly** the
per-centre `RealCenterClusterFamily` (and via `FibreClusterTopology.ofClusterSplitData`, the per-slit
§5 normal-form + §4 conservation-of-number facts).  The full-fibre-vs-pole inconsistency is resolved
(`D` is the WHOLE fibre, non-poles → residue `0`), and the genericity `AdaptedFRamified` is PROVEN. -/
theorem residueSum_eq_zero_of_realCenterClusterFamily {ω₀ : HolomorphicOneForms X}
    {g : MeromorphicFunction X} {poles : Finset X} (A : AdaptedFRamified ω₀ g poles)
    (R : ∀ i, RealCenterClusterFamily ω₀ g A.hdiv poles (A.cs i)) :
    ∑ a ∈ poles, formFnResidue ω₀ g.toFun a = 0 :=
  residueSum_eq_zero_of_fullFibreReindex_adaptedFRamified A
    (fun i => FullFibreCenterReindex.ofRealCenterClusterFamily A (R i))

end Jacobians.Dolbeault.SerreResidueTheorem
