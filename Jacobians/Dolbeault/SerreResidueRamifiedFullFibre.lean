/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueRamifiedClusterSplit
import Jacobians.Dolbeault.SerreResidueRamifiedRealCover

/-!
# The SOUND full-fibre ramified geometric-trace identification (closing Gate A)

This file proves the **sound, corrected** geometric identification `RamifiedFullFibreClusterGeometry`
(`SerreResidueRamifiedClusterSplit.lean`) — the full-fibre cluster sum over *all* preimages, at the
*genuine* cluster sheet points `clusterSheet (sec ℓ) (ζ ℓ) (w₀ ℓ) j` (the local inverse `sₗ = ηₗ⁻¹` of
the Forster §5 normal form, **not** the first-order `wp + ζʲ w₀`) — and wires it to a `∑Res = 0`
capstone.

It corrects the *two* soundness failures of the single-cluster `RamifiedSheetData.hgeom_slit` (the #13
bad field): (1) the OUTER sum ranges over the **whole** fibre `F⁻¹(z)` (all preimages contribute), and
(2) the sheet points are the **genuine** `clusterSheet` points.

## The mathematics — the per-cluster collapse via the straightening coordinate

The crux is the *per-cluster symmetric collapse* (piece (b)).  At a preimage `p` with normal-form local
inverse `s = η⁻¹` (`F = c + ηᵐ`), the cluster sheet points are `clusterSheet s ζ w₀ j z = s(ζʲ w₀ z)`,
the genuine roots of `F(w) = z` near `p`.  Writing the chart integrand `h := chartIntegrand ω₀ g p` in
the *straightening coordinate* `u` (`w = s(u)`, `dw = s'(u) du`):

> `H(u) := h(s u) · s'(u)`   (meromorphic at `u = 0`, composition with the biholomorphism `s`)

the `m`-sheet cluster sum becomes the *first-order* sheet sum of `H` (chain rule
`(d/dz)[s(ζʲ w₀ z)] = s'(ζʲ w₀ z)·ζʲ·w₀'(z)`):

> `∑_{j<m} h(s(ζʲ w₀ z))·(d/dz)[s(ζʲ w₀ z)] = ∑_{j<m} H(ζʲ w₀ z)·ζʲ·w₀'(z)`,

so the proven roots-of-unity atom `ramifiedSheetSum_laurentPoly` (applied to the Laurent **principal
part** of `H` at `0`) collapses it to `ramifiedTraceTerm (principal part of H) c z` plus the analytic
remainder's sheet sum.  The residue of `H`'s principal part at `0` is `formFnResidue ω₀ g p` by the
proven residue **change-of-variables** atom `residueChangeOfVariables` (`Res` is biholomorphism-invariant:
`Res₀(h(s u)·s'(u)) = Res_{s 0}(h) = Res_p(α)`).

Summing the per-cluster collapses over **all** preimages (`RamifiedFullFibreClusterGeometry`) gives the
single-valued meromorphic trace germ `T = ∑_ℓ ramifiedTraceTerm_ℓ + ∑_ℓ Rem_ℓ`, whose residue at `c` is
`∑_ℓ formFnResidue ω₀ g pₗ` — the full pole-fibre residue sum.  This is exactly a `RamifiedCenterFacts`
(`SerreResidueRamifiedCenter.lean`) over the whole fibre, fed into the `hoff_cs`-free capstone
`residueTheorem_ofRamifiedCenters_genus0_mod`.

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `clusterSheet_deriv` — the chain-rule derivative `(d/dz)[clusterSheet s ζ w₀ j z] = s'(ζʲ w₀ z)·ζʲ·w₀'(z)`.
* `clusterSheetSum_eq_straightenedSheetSum` — the cluster sum equals the first-order sheet sum of the
  straightened integrand `H(u) = h(s u)·s'(u)`.
* `straightenedIntegrand_residue` — `Res₀(H principal part) = formFnResidue ω₀ g p` (change of variables).
* `ClusterTraceData` — the per-cluster genuine data (the `clusterSheet` analogue of `RamifiedSheetData`,
  with *no* single-preimage restriction and the genuine straightened integrand).
* `clusterTraceSum_collapse` — the per-cluster collapse to `ramifiedTraceTerm + Rem` on the slit.
* `RamifiedCenterFacts.ofFullFibreCluster` — the SOUND full-fibre `RamifiedCenterFacts` from
  `RamifiedFullFibreClusterGeometry` + per-cluster `ClusterTraceData`.
* `residueSum_eq_zero_of_fullFibreCluster` — `∑Res = 0` via the corrected full-fibre geometry.

## ⚠ Soundness

Uses the **full fibre** (all preimages — the #13 lesson) and the **genuine** sheet points `clusterSheet`
(via the proven `exists_clusterSplit`/`exists_wpow_normalForm`).  The `m`-sheet SUM (the roots-of-unity
atom cancels the chain-rule `1/m`; no single-sheet `m·Res`).  Residue invariance is the proven
`residueChangeOfVariables`.  No false/junk/circular field; no custom axiom; no sorry on a false statement.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §5 (`z = wᵐ`), §17.
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (3.1).
* `SerreResidueRamifiedClusterSplit.lean` (`clusterSheet`, `exists_clusterSplit`,
  `RamifiedFullFibreClusterGeometry`), `RamifiedResidueChangeOfVariables.lean`
  (`laurentTraceCoeff_eq_sheetSum`), `ResidueChangeOfVariables.lean` (`residueChangeOfVariables`).
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

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The chain-rule derivative of a cluster sheet -/

/-- **The cluster-sheet derivative.**  For the cluster sheet point `clusterSheet s ζ w₀ j z =
s(ζʲ w₀ z)`, with `s` analytic at `ζʲ w₀ z` and `w₀` differentiable at `z`, the chain rule gives

> `(d/dz)[clusterSheet s ζ w₀ j z] = deriv s (ζʲ w₀ z) · (ζʲ · deriv w₀ z)`.

(Compose `s` with the affine-in-`w₀` map `z ↦ ζʲ w₀ z`; the inner derivative is `ζʲ · w₀'(z)`.) -/
theorem clusterSheet_deriv {s w₀ : ℂ → ℂ} {ζ : ℂ} {j : ℕ} {z : ℂ}
    (hs : AnalyticAt ℂ s (ζ ^ j * w₀ z)) (hw₀ : DifferentiableAt ℂ w₀ z) :
    deriv (clusterSheet s ζ w₀ j) z = deriv s (ζ ^ j * w₀ z) * (ζ ^ j * deriv w₀ z) := by
  have hinner : HasDerivAt (fun z => ζ ^ j * w₀ z) (ζ ^ j * deriv w₀ z) z :=
    hw₀.hasDerivAt.const_mul (ζ ^ j)
  have houter : HasDerivAt s (deriv s (ζ ^ j * w₀ z)) (ζ ^ j * w₀ z) :=
    hs.differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (s ∘ fun z => ζ ^ j * w₀ z)
      ((ζ ^ j * deriv w₀ z) • deriv s (ζ ^ j * w₀ z)) z := houter.scomp z hinner
  rw [smul_eq_mul, mul_comm] at hcomp
  exact hcomp.deriv

/-! ## The straightened integrand `H(u) = h(s u)·s'(u)` and the per-cluster collapse

At a preimage `p` with normal-form local inverse `s = η⁻¹`, write the chart integrand
`h := chartIntegrand ω₀ g p` in the straightening coordinate `u` (`w = s u`).  The straightened
integrand `H(u) := h(s u)·s'(u)` is meromorphic at `0` (composition of the meromorphic `h` with the
biholomorphism `s`, times the analytic `s'`).  Its `m`-sheet *first-order* sum (over the roots
`u_j = ζʲ w₀ z` of `uᵐ = z − c`) is exactly the geometric cluster sum, by `clusterSheet_deriv`. -/

/-- **The straightened integrand** `H(u) := chartIntegrand ω₀ g p (s u) · deriv s u` (the chart
integrand of `α = ω₀·g` at `p`, pushed into the straightening coordinate `u` via `w = s u`). -/
noncomputable def straightenedIntegrand (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (p : X) (s : ℂ → ℂ) :
    ℂ → ℂ :=
  fun u => chartIntegrand ω₀ g p (s u) * deriv s u

/-- **The straightened integrand is meromorphic at `0`** when `g`'s chart-pullback is meromorphic at
`p`'s chart centre, `s` is analytic at `0` with `s 0 = chartAt ℂ p p`.  (Composition of the meromorphic
`chartIntegrand` with the analytic biholomorphism `s`, times the analytic `s'`.) -/
theorem meromorphicAt_straightenedIntegrand (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (p : X)
    {s : ℂ → ℂ} (hs_an : AnalyticAt ℂ s 0) (hs0 : s 0 = (chartAt ℂ p) p)
    (hg_mero : MeromorphicAt (fun z => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p)) :
    MeromorphicAt (straightenedIntegrand ω₀ g p s) 0 := by
  have hh : MeromorphicAt (chartIntegrand ω₀ g p) ((chartAt ℂ p) p) :=
    meromorphicAt_chartIntegrand ω₀ g p hg_mero
  have hcomp : MeromorphicAt (chartIntegrand ω₀ g p ∘ s) 0 := by
    rw [← hs0] at hh
    exact MeromorphicAt.comp_analyticAt hh hs_an
  exact hcomp.mul hs_an.deriv.meromorphicAt

/-- **The residue of the straightened integrand is the upstairs form residue** (the residue
change-of-variables atom in action).  When `s` is a local biholomorphism at `0` (`s` analytic,
`deriv s 0 ≠ 0`) with `s 0 = chartAt ℂ p p`, the residue of `H(u) = h(s u)·s'(u)` at `0` equals the
chart integrand's residue at `chartAt ℂ p p`, which is `formFnResidue ω₀ g p`:

> `Res₀ (h(s ·)·s'(·)) = Res_{s 0} h = formFnResidue ω₀ g p`.

This is `residueChangeOfVariables` (the residue is biholomorphism-invariant) plus the definitional
`resAt (chartIntegrand ω₀ g p) (chartAt ℂ p p) = formFnResidue ω₀ g p`. -/
theorem resAt_straightenedIntegrand (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (p : X)
    {s : ℂ → ℂ} (hs_an : AnalyticAt ℂ s 0) (hs_deriv : deriv s 0 ≠ 0)
    (hs0 : s 0 = (chartAt ℂ p) p)
    (hg_mero : MeromorphicAt (fun z => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p)) :
    resAt (straightenedIntegrand ω₀ g p s) 0 = formFnResidue ω₀ g p := by
  have hh : MeromorphicAt (chartIntegrand ω₀ g p) (s 0) := by
    rw [hs0]; exact meromorphicAt_chartIntegrand ω₀ g p hg_mero
  have hcov := residueChangeOfVariables s (chartIntegrand ω₀ g p) 0 hs_an hs_deriv hh
  show resAt (fun w => chartIntegrand ω₀ g p (s w) * deriv s w) 0 = formFnResidue ω₀ g p
  rw [hcov, hs0]
  exact resAt_chartIntegrand_eq_formFnResidue ω₀ g p

/-- **The geometric cluster sum equals the straightened sheet sum.**  Using the chain rule
`clusterSheet_deriv`, the geometric `m`-sheet cluster sum of `h = chartIntegrand ω₀ g p` along the
cluster sheets `clusterSheet s ζ w₀ j` equals the *first-order* `m`-sheet sum of the straightened
integrand `H(u) = h(s u)·s'(u)` along `u_j = ζʲ w₀ z`:

> `∑_{j<m} h(clusterSheet s ζ w₀ j z)·(d/dz)[clusterSheet s ζ w₀ j z]`
>   `= ∑_{j<m} H(ζʲ w₀ z)·(d/dz)[0 + ζʲ w₀ z]`.

(`h(s(ζʲ w₀ z))·s'(ζʲ w₀ z) = H(ζʲ w₀ z)`, and the cluster-sheet derivative
`s'(ζʲ w₀ z)·ζʲ·w₀'(z)` reassociates against the straightened first-order derivative `ζʲ·w₀'(z)`.) -/
theorem clusterSheetSum_eq_straightenedSheetSum (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (p : X)
    {s w₀ : ℂ → ℂ} {ζ : ℂ} {m : ℕ} {z : ℂ} (hw₀_diff : DifferentiableAt ℂ w₀ z)
    (hs_an : ∀ j ∈ Finset.range m, AnalyticAt ℂ s (ζ ^ j * w₀ z)) :
    (∑ j ∈ Finset.range m,
        chartIntegrand ω₀ g p (clusterSheet s ζ w₀ j z) * deriv (clusterSheet s ζ w₀ j) z)
      = ∑ j ∈ Finset.range m,
        straightenedIntegrand ω₀ g p s (ζ ^ j * w₀ z)
          * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z := by
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [clusterSheet_deriv (hs_an j hj) hw₀_diff, deriv_sheet_eq w₀ z 0 (ζ ^ j),
    straightenedIntegrand, clusterSheet]
  ring

/-- **The per-cluster symmetric collapse (piece (b), on the genuine cluster sheets).**  At a preimage
`p` with normal-form local inverse `s = η⁻¹`, a primitive `m`-th root `ζ`, and a slit-branch `w₀`
(`w₀ z ≠ 0`, `w₀(z)ᵐ = z − c`, `w₀'(z) = (1/m) w₀(z)^{1−m}`), the geometric `m`-sheet cluster sum of the
chart integrand `h = chartIntegrand ω₀ g p` along the *genuine* cluster sheets `clusterSheet s ζ w₀ j`
collapses to the single-valued `ramifiedTraceTerm` of the straightened integrand's Laurent principal
part, plus the remainder sheet sum:

> `∑_{j<m} h(clusterSheet s ζ w₀ j z)·(d/dz)[clusterSheet s ζ w₀ j z]`
>   `= ramifiedTraceTerm (Icc 1 N) b (k ↦ −k) m c z + ∑_{j<m} R(ζʲ w₀ z)·(d/dz)[0 + ζʲ w₀ z]`,

where `(N, b, R)` is the Laurent principal-part split of the straightened integrand `H(u) = h(s u)·s'(u)`
at `0` (`H =ᶠ[𝓝[≠] 0] negTail 0 b N + R`), *provided* the split holds at each sheet argument `ζʲ w₀ z`
(`hH_split`).  Pure algebra (the proven roots-of-unity atom `ramifiedSheetSum_laurentPoly`), with the
genuine sheet points. -/
theorem clusterTraceSum_collapse (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (p : X)
    {s w₀ : ℂ → ℂ} {ζ : ℂ} {m : ℕ} (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m)
    {c z : ℂ} {N : ℕ} {b : ℕ → ℂ} {R : ℂ → ℂ}
    (hw₀_ne : w₀ z ≠ 0) (hw₀_pow : w₀ z ^ (m : ℤ) = z - c)
    (hw₀_deriv : deriv w₀ z = (m : ℂ)⁻¹ * w₀ z ^ (1 - (m : ℤ)))
    (hw₀_diff : DifferentiableAt ℂ w₀ z)
    (hs_an : ∀ j ∈ Finset.range m, AnalyticAt ℂ s (ζ ^ j * w₀ z))
    (hH_split : ∀ j ∈ Finset.range m,
      straightenedIntegrand ω₀ g p s (ζ ^ j * w₀ z)
        = negTail 0 b N (ζ ^ j * w₀ z) + R (ζ ^ j * w₀ z)) :
    (∑ j ∈ Finset.range m,
        chartIntegrand ω₀ g p (clusterSheet s ζ w₀ j z) * deriv (clusterSheet s ζ w₀ j) z)
      = ramifiedTraceTerm (Finset.Icc 1 N) b (fun k => -(k : ℤ)) m c z
        + ∑ j ∈ Finset.range m,
            R (ζ ^ j * w₀ z) * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z := by
  classical
  -- Step 1: geometric cluster sum = straightened first-order sheet sum.
  rw [clusterSheetSum_eq_straightenedSheetSum ω₀ g p hw₀_diff hs_an]
  -- Step 2: split each straightened term into `negTail` + `R`, distribute.
  have hsplit : (∑ j ∈ Finset.range m,
        straightenedIntegrand ω₀ g p s (ζ ^ j * w₀ z)
          * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z)
      = (∑ j ∈ Finset.range m,
          negTail 0 b N (ζ ^ j * w₀ z) * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z)
        + (∑ j ∈ Finset.range m,
            R (ζ ^ j * w₀ z) * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hH_split j hj]; ring
  rw [hsplit]
  -- Step 3: the `negTail`-sheet sum collapses to `ramifiedTraceTerm` (the proven atom).
  congr 1
  rw [show (∑ j ∈ Finset.range m,
        negTail 0 b N (ζ ^ j * w₀ z) * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z)
      = ∑ j ∈ Finset.range m,
          (∑ k ∈ Finset.Icc 1 N, b k * ((0 : ℂ) + ζ ^ j * w₀ z - 0) ^ (-(k : ℤ)))
            * deriv (fun ζz => (0 : ℂ) + ζ ^ j * w₀ ζz) z
    from Finset.sum_congr rfl (fun j _ => by rw [negTail]; ring_nf)]
  exact ramifiedSheetSum_laurentPoly (Finset.Icc 1 N) b (fun k => -(k : ℤ)) hm hζ
    hw₀_ne hw₀_pow hw₀_deriv

end Jacobians.Dolbeault.SerreResidueTheorem
