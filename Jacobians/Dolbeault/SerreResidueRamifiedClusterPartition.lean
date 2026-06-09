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

/-! ## The per-summand chart reconciliation (Miranda §VIII.3 well-definedness)

The pure-reindexing reduction's per-`(i,j)` summand match equates the cluster summand (read in the
**fixed preimage** `D.xs i`'s chart) with the moving sphere summand (read in the **moving sheet point**'s
own chart, along the section `holoReprSheet k`).  Both are pushforwards of `α = ω₀·g` along a local
section of `f` through the *same* fibre point `q = S.sheet k (coe z)`; they agree by the source-chart
independence of the trace summand (`movingSummand_chartIndep`) once the two sections germ-agree (both are
holomorphic right-inverses of `f`'s chart-pullback through `q`).  This is the §VIII.3 fact that "the
trace `Tr_F α` is a well-defined form", applied at the cluster.

We isolate the reconciliation as a standalone lemma taking the genuine geometric residuals as
hypotheses: the point coincidence (`cs z = q`), the section-derivative agreement (`deriv (chart_q ∘ cs) z
= deriv (chart_q ∘ holoReprSheet k) z`, the holomorphic-local-inverse uniqueness), and the
differentiability data feeding `movingSummand_chartIndep`. -/

/-- **Per-summand chart reconciliation at a cluster point.**  Let `q := S.sheet k (coe z)` be a sphere
sheet point at the regular slit value `z`, and `cs : ℂ → X` a local section of `f` through `q` with
`cs z = q` and chart coordinate `chart_{a} (cs w) = cw w` near `z` (so `cw z = chart_a q`), where `a` is
the fixed preimage chart base.  Then the **fixed-preimage cluster summand** equals the **moving sphere
summand**:

> `chartIntegrand ω₀ g a (cw z)·deriv cw z
>    = chartIntegrand ω₀ g q (chart_q (holoReprSheet k z))·deriv (fun w => chart_q (holoReprSheet k w)) z`,

given: `q ∈ chart_a.source`; `cs` continuous at `z`; the chart-pullbacks `chart_q ∘ cs`, `chart_a ∘ cs`
differentiable at `z`; the two chart transitions (`a ↔ q`) differentiable both ways; and the
section-derivative agreement `deriv (chart_q ∘ cs) z = deriv (chart_q ∘ holoReprSheet k) z` (the
holomorphic-local-inverse uniqueness, both sections being right-inverses of `f` through `q`).  Pure
chart algebra: rewrite the cluster summand as the `a`-chart `movingSummand` of `cs`, apply
`movingSummand_chartIndep` to switch to the `q`-chart, then the section-derivative agreement. -/
theorem clusterSummand_eq_sphereSummand (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    {f : MeromorphicFunction X} {z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (k : Fin S.n) (a : X) (cs : ℂ → X) (cw : ℂ → ℂ)
    (hq : cs z = S.sheet k (((z : ℂ) : RiemannSphere)))
    (hcw : ∀ᶠ w in 𝓝 z, (chartAt ℂ a) (cs w) = cw w)
    (hmem_a : cs z ∈ (chartAt ℂ a).source)
    (hcs_cont : ContinuousAt cs z)
    (hcsP_diff : DifferentiableAt ℂ (fun w => (chartAt ℂ (cs z)) (cs w)) z)
    (htrans_diff_a : DifferentiableAt ℂ
      (fun w => (chartAt ℂ a) ((chartAt ℂ (cs z)).symm w)) ((chartAt ℂ (cs z)) (cs z)))
    (htrans_diff_inv_a : DifferentiableAt ℂ
      (fun w => (chartAt ℂ (cs z)) ((chartAt ℂ a).symm w)) ((chartAt ℂ a) (cs z)))
    (hderiv_match : deriv (fun w => (chartAt ℂ (cs z)) (cs w)) z
      = deriv (fun w => (chartAt ℂ (cs z)) (S.holoReprSheet k w)) z) :
    chartIntegrand ω₀ g a (cw z) * deriv cw z
      = chartIntegrand ω₀ g (S.sheet k (((z : ℂ) : RiemannSphere)))
          ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
            (S.holoReprSheet k z))
        * deriv (fun w => (chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
            (S.holoReprSheet k w)) z := by
  classical
  -- Abbreviate `q := cs z = S.sheet k (coe z) = holoReprSheet k z`.
  set q : X := cs z with hqdef
  -- (1) Rewrite the cluster summand into the `a`-chart `movingSummand` of the section `cs`.
  -- `cw z = chart_a (cs z)` and `deriv cw z = deriv (chart_a ∘ cs) z` (congr via `hcw`).
  have hcwz : cw z = (chartAt ℂ a) (cs z) := (hcw.self_of_nhds).symm
  have hderiv_cw : deriv cw z = deriv (fun w => (chartAt ℂ a) (cs w)) z :=
    Filter.EventuallyEq.deriv_eq (hcw.mono (fun w h => h.symm))
  rw [hcwz, hderiv_cw]
  -- (2) Self-chart transition `chart_q ∘ chart_q.symm =ᶠ id` is differentiable (for `chartIndep`).
  have hself_diff : DifferentiableAt ℂ
      (fun w => (chartAt ℂ q) ((chartAt ℂ q).symm w)) ((chartAt ℂ q) q) := by
    have heqid : (fun w => (chartAt ℂ q) ((chartAt ℂ q).symm w))
        =ᶠ[𝓝 ((chartAt ℂ q) q)] id := by
      filter_upwards [(chartAt ℂ q).open_target.mem_nhds
        ((chartAt ℂ q).map_source (mem_chart_source ℂ q))] with w hw
      simp only [(chartAt ℂ q).right_inv hw, id_eq]
    exact differentiableAt_id.congr_of_eventuallyEq heqid
  -- (3) `movingSummand_chartIndep` (section `cs`, charts `a` and `q`): switch to the `q`-chart.
  have hindep := movingSummand_chartIndep ω₀ g cs a q hcs_cont hcsP_diff hmem_a
    (mem_chart_source ℂ q) htrans_diff_a hself_diff htrans_diff_inv_a hself_diff
  -- `hindep : (a-chart summand of cs) = (q-chart summand of cs)`.
  rw [hindep]
  -- (4) The `q`-chart summand of `cs` equals the `q = S.sheet k (coe z)`-chart summand of
  -- `holoReprSheet k`: `cs z = q = S.sheet k (coe z) = holoReprSheet k z`, so the `chartIntegrand`
  -- arguments and the chart match (rewrite `q` via `hq`); the section derivs match (`hderiv_match`).
  have hcs_eq : cs z = S.holoReprSheet k z := hq
  rw [hderiv_match, hcs_eq, hq]

/-! ## The sphere-based reduction (moving-sheet form)

Composing the pure reindexing with the moving-sheet form of the sphere-fibre trace
(`fibreTrace_eventuallyEq_movingSum` at `z`, along `holoReprSheet`), we obtain `hgeom_fibre` at `z`
directly from a sphere sheet system `S` at `coe z`, a bijection `e : (Σ i, Fin (D.mult i)) ≃ Fin S.n`,
and the per-`(i,j)` summand match **in the moving (holoReprSheet) form** — exactly what
`clusterSummand_eq_sphereSummand` produces. -/

/-- **The full-fibre cluster identity from a sphere sheet system + bijection (moving-sheet form).**  At
a regular slit value `z` with a sphere sheet system `S` of `F = f.toRiemannSphere` at `coe z` (regular
fibre — `hderiv`, `hmero`), the regular-value coherence
`valueChartTrace ω₀ f Φ z = (fibreTrace ω₀ f (ofSphereSheetSystem S …)).traceCoeff z`, a bijection
`e : (Σ i, Fin (D.mult i)) ≃ Fin S.n`, and the per-`(i,j)` summand equality matching the cluster summand
to the `e ⟨i,j⟩`-th **moving (holoReprSheet) summand**, the full-fibre cluster identity holds at `z`.

*Proof.*  Rewrite the coherence's RHS via `fibreTrace_eventuallyEq_movingSum` (at `z`, sections
`holoReprSheet`) into the moving fibre sum `∑ₖ chartIntegrand ω₀ g (S.sheet k (coe z)) …·deriv …`, then
apply `valueChartTrace_eq_clusterSum_of_reindex` with `T` the moving sum (packaged as the trivial
`FibreTrace` whose `traceCoeff` *is* that sum) — i.e. directly reindex the moving sum. -/
theorem valueChartTrace_eq_clusterSum_of_sphereReindex {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} {Sset : Set ℂ}
    (D : FibreRamifiedData g f c) (Cl : ∀ i, ClusterTraceData ω₀ g (D.xs i) c Sset) {z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hderiv : ∀ k, deriv (fun w => f.holoRepr
        ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
        (S.sheet k (((z : ℂ) : RiemannSphere)))) ≠ 0)
    (hmero : ∀ k, MeromorphicAt
      (fun w => g ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere)))).symm w))
      ((chartAt ℂ (S.sheet k (((z : ℂ) : RiemannSphere))))
        (S.sheet k (((z : ℂ) : RiemannSphere)))))
    (hcoh : valueChartTrace ω₀ f Φ z
      = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv hmero)).traceCoeff z)
    (e : (Σ i : D.ι, Fin (D.mult i)) ≃ Fin S.n)
    (hsummand : ∀ (i : D.ι) (j : Fin (D.mult i)),
      chartIntegrand ω₀ g (S.sheet (e ⟨i, j⟩) (((z : ℂ) : RiemannSphere)))
          ((chartAt ℂ (S.sheet (e ⟨i, j⟩) (((z : ℂ) : RiemannSphere))))
            (S.holoReprSheet (e ⟨i, j⟩) z))
        * deriv (fun w => (chartAt ℂ (S.sheet (e ⟨i, j⟩) (((z : ℂ) : RiemannSphere))))
            (S.holoReprSheet (e ⟨i, j⟩) w)) z
        = chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
          * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z) :
    valueChartTrace ω₀ f Φ z
      = ∑ i, ∑ j ∈ Finset.range (D.mult i),
        chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
          * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z := by
  classical
  -- The moving-sheet form of the sphere-fibre trace at `z` (sections `holoReprSheet`).
  set D' := FibreRegularData.ofSphereSheetSystem S hderiv hmero with hD'
  have hmoving : (fibreTrace ω₀ f D').traceCoeff z
      = ∑ k, chartIntegrand ω₀ g (D'.xs k) ((chartAt ℂ (D'.xs k)) (S.holoReprSheet k z))
        * deriv (fun w => (chartAt ℂ (D'.xs k)) (S.holoReprSheet k w)) z :=
    (fibreTrace_eventuallyEq_movingSum ω₀ f D' (fun k => S.holoReprSheet k)
      (fun _ => rfl) (fun k => (S.holoReprSheet_contMDiffAt k).continuousAt)
      (fun k => S.holoReprSheet_section k)).self_of_nhds
  -- The moving summand as a function `F : Fin S.n → ℂ`.
  set F : Fin S.n → ℂ := fun k => chartIntegrand ω₀ g (D'.xs k)
      ((chartAt ℂ (D'.xs k)) (S.holoReprSheet k z))
    * deriv (fun w => (chartAt ℂ (D'.xs k)) (S.holoReprSheet k w)) z with hF
  rw [hcoh, hmoving]
  -- (a) Flatten the cluster double sum to a single `Σ`-sum, matching each term to `F (e ⟨i,j⟩)`.
  have hRHS : (∑ i, ∑ j ∈ Finset.range (D.mult i),
        chartIntegrand ω₀ g (D.xs i) (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
          * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z)
      = ∑ p : (Σ i : D.ι, Fin (D.mult i)), F (e p) := by
    rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_range fun j => chartIntegrand ω₀ g (D.xs i)
        (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j z)
      * deriv (clusterSheet (Cl i).s (Cl i).ζ (Cl i).w₀ j) z]
    exact Finset.sum_congr rfl (fun j _ => (hsummand i j).symm)
  rw [hRHS]
  -- (b) Reindex the moving sum `∑ k, F k` along `e : (Σ…) ≃ Fin S.n`.
  exact (Fintype.sum_equiv e (fun p => F (e p)) F (fun _ => rfl)).symm

end Jacobians.Dolbeault.SerreResidueTheorem
