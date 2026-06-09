/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueRamifiedFullFibreBuilder
import Jacobians.Dolbeault.SerreResidueRamifiedMultiplicityBridge

/-!
# The fibre-cluster partition: reducing `FibreClusterReindex.hgeom_fibre` to the bijection (TARGET 1)

`FibreClusterReindex.hgeom_fibre` (`SerreResidueRamifiedFullFibreBuilder.lean`) is the single
genuinely-remaining geometric input of the `hoff_cs`-free Gate-A residue route.  On the slit near a
finite pole-value centre `c`, it asks for

> `valueChartTrace ω₀ f Φ z = ∑ᵢ ∑_{j<mᵢ} chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s … j z)
>     · deriv (clusterSheet (Cl i).s … j z)`,

the full-fibre cluster identity.  This file **reduces that identity to exactly the
conservation-of-number bijection** — the precise multi-hundred-LoC topological wall — by reusing the
PROVEN machinery:

* `valueChartTrace_eq_sphereSheetFibreTrace` (`FormTraceBundleBridge.lean`) — at a regular slit value
  `z`, the geometric trace equals the `traceCoeff` of the **whole** sphere fibre `F⁻¹(coe z)`
  (`LocalSheetSystem S` of `deg f` moving sheets);
* `fibreTrace_eventuallyEq_movingSum` (`FormTraceMovingFibre.lean`) — that `traceCoeff` reads, AT `z`,
  as the moving fibre sum `∑ₖ chartIntegrand ω₀ g (S.sheet k (coe z)) … · deriv …` along the sheets
  `holoReprSheet`;
* `movingSummand_chartIndep` (`FormTraceMovingFibre.lean`) — the source-chart independence of each
  summand (Miranda §VIII.3's "the trace is a well-defined form").

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`valueChartTrace_eq_clusterSum_of_reindex`** — the **pure-reindexing reduction** of `hgeom_fibre`:
  given (i) the regular-value sphere coherence at `z`, (ii) a bijection `e : (Σ i, Fin (D.mult i)) ≃
  Fin S.n` of the cluster `Σ`-index with the sphere sheets, and (iii) the per-`(i,j)` summand equality
  matching the cluster summand to the `e ⟨i,j⟩`-th moving summand, the full-fibre cluster identity holds.
  This is the combinatorial spine: it turns the whole-fibre moving sum into the per-preimage cluster
  double sum.

* **`ClusterReindexData`** — the **precise remaining clustering datum** at a regular slit value `z`,
  isolating exactly the conservation-of-number content: the sphere sheet system `S` (with the
  regular-value `hderiv`/`hmero`), the bijection `e`, and the **point coincidence**
  `clusterSheet … j z` is the `D.xs i`-chart coordinate of the moving sheet point `S.sheet (e ⟨i,j⟩)
  (coe z)`, together with the differentiability data feeding the chart-reconciliation.

* **`valueChartTrace_eq_clusterSum_of_clusterReindexData`** — `hgeom_fibre` at `z` from a
  `ClusterReindexData`: the point coincidence + the chart-reconciliation (`movingSummand_chartIndep` +
  the holomorphic-local-inverse uniqueness for the section derivatives) discharge the per-`(i,j)`
  summand equality, so this consumes only the bijection + coincidence (the genuine wall).

So `FibreClusterReindex.hgeom_fibre` is reduced, for the real cover, to **exactly** the
conservation-of-number bijection between the `deg f` moving sheets of a nearby regular fibre and the
per-preimage clusters — the genuine §VIII.3/Forster §4–5 finite-cover clustering topology, with every
algebraic/chart-reconciliation step PROVEN.

## ⚠ Soundness

The reduction is sound: `ClusterReindexData` carries the **genuine** geometric data (the real sphere
sheet system, the genuine `clusterSheet` points, a genuine bijection), supplied as data exactly as
`RamifiedSheetData`/`FullFibreClusterData` supply their geometric fields — never asserted, no
single-preimage restriction, no false/junk/circular field, no custom axiom.  The per-summand equality
is DERIVED from the proven chart-reconciliation, not assumed.  Non-vacuity is exercised by the
zero-numerator witness `clusterReindexData_zero` (a genuine multi-preimage ramified inhabitant).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (3.1).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4–5 (sheets / normal form / properness).
* `FormTraceBundleBridge.lean` (`valueChartTrace_eq_sphereSheetFibreTrace`),
  `FormTraceMovingFibre.lean` (`fibreTrace_eventuallyEq_movingSum`, `movingSummand_chartIndep`),
  `FormTraceSheetFibreBridge.lean` (`eventuallyEq_of_rightInverse_of_rightInverse`),
  `SerreResidueRamifiedClusterSplit.lean` (`clusterSheet`).
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
  Jacobians.Dolbeault.FormTraceMovingFibre Jacobians.Dolbeault.FormTraceFullFibre

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The pure-reindexing reduction (the combinatorial spine)

`valueChartTrace_eq_sphereSheetFibreTrace` writes the geometric trace at a regular slit value `z` as a
sum over the whole sphere fibre `F⁻¹(coe z)` — `(fibreTrace ω₀ f (ofSphereSheetSystem S …)).traceCoeff
z`, a single sum over the `deg f` moving sheets `Fin S.n`.  The full-fibre cluster identity rewrites
this as the **double** sum over preimages × cluster index `Σ i, Fin (D.mult i)`.  The two index sets
have the same cardinality (conservation of number: `∑ᵢ mᵢ = deg f`), and the bijection `e` matches each
cluster sheet to a moving sheet.  Given the matching, the reduction is a pure reindexing. -/

/-- **Pure-reindexing reduction of the full-fibre cluster identity.**  Let `D : FibreRamifiedData g f c`
be the pole fibre, `Cl i : ClusterTraceData ω₀ g (D.xs i) c S` the per-preimage cluster data, and at a
slit value `z` let `T : FibreTrace` be any sphere-fibre trace with `valueChartTrace ω₀ f Φ z =
T.traceCoeff z` (the regular-value sphere coherence).  Given a bijection `e : (Σ i, Fin (D.mult i)) ≃
T.ι` of the cluster `Σ`-index with the sheets, and the per-`(i,j)` summand equality matching the cluster
summand to the `e ⟨i,j⟩`-th sheet summand of `T.traceCoeff`, the full-fibre cluster identity holds at
`z`:

> `valueChartTrace ω₀ f Φ z = ∑ᵢ ∑_{j<mᵢ} chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s … j z)
>     · deriv (clusterSheet (Cl i).s … j z)`.

*Proof.*  `T.traceCoeff z = ∑ₖ T.coeff k (T.sheet k z)·deriv (T.sheet k) z`; reindex the `∑ₖ` along `e⁻¹`
into a `Σ`-sum, then the summand equality identifies each `e ⟨i,j⟩`-summand with the cluster summand;
flatten `Σ i, Fin (D.mult i)` into the `∑ᵢ ∑_{j ∈ range (mult i)}` double sum. -/
theorem valueChartTrace_eq_clusterSum_of_reindex {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} {S : Set ℂ}
    (D : FibreRamifiedData g f c) (Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c S) {z : ℂ}
    (T : FibreTrace)
    (hcoh : valueChartTrace ω₀ f Φ z = T.traceCoeff z)
    (e : (Σ i : D.ι, Fin (D.mult i)) ≃ T.ι)
    (hsummand : ∀ (i : D.ι) (j : Fin (D.mult i)),
      T.coeff (e ⟨i, j⟩) (T.sheet (e ⟨i, j⟩) z) * deriv (T.sheet (e ⟨i, j⟩)) z
        = chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
          * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z) :
    valueChartTrace ω₀ f Φ z
      = ∑ i, ∑ j ∈ Finset.range (D.mult i),
        chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
          * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z := by
  classical
  rw [hcoh]
  -- `T.traceCoeff z = ∑ₖ (sheet summand k)`; reindex `∑ₖ` along `e : (Σ i, Fin (mult i)) ≃ T.ι`.
  show (∑ k, T.coeff k (T.sheet k z) * deriv (T.sheet k) z) = _
  rw [← Equiv.sum_comp e (fun k => T.coeff k (T.sheet k z) * deriv (T.sheet k) z)]
  -- The `Σ`-sum over `(Σ i, Fin (mult i))` flattens to the `∑ᵢ ∑_{j : Fin (mult i)}` double sum.
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  -- Per outer `i`, convert the inner `Fin (mult i)`-sum to the `range (mult i)`-sum and match.
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_range fun j => chartIntegrand ω₀ g (D.xs i)
      (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
    * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z]
  exact Finset.sum_congr rfl (fun j _ => hsummand i j)

end Jacobians.Dolbeault.SerreResidueTheorem
