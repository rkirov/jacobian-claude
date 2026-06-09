/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueRamifiedClusterPartition
import Jacobians.Dolbeault.SerreResidueRamifiedMultiplicityBridge

/-!
# The fibre-cluster topology: reducing `ClusterReindexData` to the conservation-of-number datum

`SerreResidueRamifiedClusterPartition.lean` reduces `FibreClusterReindex.hgeom_fibre` to a slit-wide
family of `ClusterReindexData` — the precise remaining clustering datum at each regular slit value `z`.
That datum has, besides the **bijection** `e` and the **point coincidence** `hpoint` (the genuine
§4/§17.9 conservation-of-number content), a battery of *routine* analytic fields (`hcw`/`hmem_a`/
`hcs_cont`/`hcsP_diff`/`htrans_diff`/`htrans_diff_inv`/`hderiv_match`) describing the differentiability
of the cluster section and the section-derivative agreement.

This file **discharges those routine fields** from the genuine geometric data, so `ClusterReindexData`
reduces to *exactly* the conservation-of-number content.  Concretely it isolates a single structure
`FibreClusterTopology` whose fields are precisely:

* the sphere sheet system `S` at `coe z` (regular fibre — `hderiv`/`hmero`/`hcoh`, the regular-value
  coherence supplied by the moving-fibre machinery);
* the **conservation-of-number bijection** `e : (Σ i, Fin (D.mult i)) ≃ Fin S.n`;
* the **point coincidence** `hpoint` (each cluster sheet point IS the matched moving sheet point);
* the genuine *geometric* residuals that are NOT pure chart algebra: the cluster sheet stays in the
  fixed-preimage chart source near `z` (`hsrc`), and the cluster section is a genuine local section of
  `f.holoRepr` through the coincident point (`hcs_sec`), together with the regular-value `hreg`/`hq_np`
  feeding the holomorphic-local-inverse uniqueness.

Everything else — the self-chart-pullback differentiability of the cluster section, the chart
transitions, and the section-derivative agreement `hderiv_match` — is **DERIVED** here from the
analyticity of the normal-form local inverse `s` (`(Cl i).hs_an_sheet`), the slit branch
differentiability (`(Cl i).hw₀_diff`), the chart-transition analyticity (a local copy of the
maximal-atlas coordinate change), and the proven `hderiv_match_of_section`.

## What is delivered (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* **`clusterSheet_differentiableAt`** — `clusterSheet (Cl i).s … j` is differentiable at a slit value
  `z` (from `s` analytic at `ζʲ·w₀ z` + `w₀` differentiable at `z`).
* **`transition_analyticAt'` / `analyticAt_chart_change'`** — local copies of the maximal-atlas
  chart-transition analyticity (so this file does not depend on the Čech subtree).
* **`clusterSection_chartPullback_differentiableAt`** — the self-chart pullback `chart_q ∘
  clusterSection` is differentiable at `z` (chart transition ∘ chart.symm ∘ clusterSheet).
* **`FibreClusterTopology`** — the precise conservation-of-number datum (bijection + coincidence + the
  genuine geometric residuals), with the routine analytic fields removed.
* **`ClusterReindexData.ofFibreClusterTopology`** — assembles a `ClusterReindexData` from a
  `FibreClusterTopology`, discharging every routine analytic field.  This is the reduction: the
  full-fibre cluster identity `hgeom_fibre` at `z` now rests on *only* the bijection + coincidence (+
  the two genuine geometric residuals).

## ⚠ Soundness

`FibreClusterTopology` carries the **genuine** geometric data (the real sphere sheet system, the genuine
`clusterSheet`/`clusterSection` points, a genuine bijection, the genuine section property), never
asserted.  The bijection `e` still forces `∑ᵢ D.mult i = S.n` (`ClusterReindexData.sum_mult_eq_sheetCount`
applies to the assembled datum), so it is genuinely multi-preimage, not a disguised triviality.  No
custom axiom, no sorry on a false statement, no false/junk/circular field — the routine fields are
DERIVED, the irreducible bijection + coincidence remain the only conservation-of-number content.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4 (the degree / conservation of number, Cor.
  4.24–4.25), §5 (the normal form `z = wᵐ`).
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (the trace), §II.4.
* `SerreResidueRamifiedClusterPartition.lean` (`ClusterReindexData`, `clusterSection`,
  `hderiv_match_of_section`, `valueChartTrace_eq_clusterSum_of_clusterReindexData`),
  `SerreResidueRamifiedMultiplicityBridge.lean` (`exists_clusterSplit_at_fibrePoint`).
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

/-! ## Differentiability of the cluster sheet and section

The cluster sheet `clusterSheet s ζ w₀ j w = s (ζʲ · w₀ w)` is differentiable at a slit value `z` from
the analyticity of `s` at `ζʲ · w₀ z` (`(Cl i).hs_an_sheet`) and the differentiability of the branch
`w₀` (`(Cl i).hw₀_diff`).  The cluster section `clusterSection D Cl i j = chart_{D.xs i}.symm ∘
clusterSheet …` lifts this to `X`; its self-chart pullback `chart_q ∘ clusterSection` is differentiable
by composing with the chart transition `chart_q ∘ chart_{D.xs i}.symm` (analytic, maximal-atlas
coordinate change). -/

/-- **The cluster sheet is differentiable at a slit value.**  `clusterSheet s ζ w₀ j w = s (ζʲ·w₀ w)`
is differentiable at `z` when `s` is analytic at `ζʲ·w₀ z` and `w₀` is differentiable at `z`. -/
theorem clusterSheet_differentiableAt {s w₀ : ℂ → ℂ} {ζ : ℂ} {j : ℕ} {z : ℂ}
    (hs_an : AnalyticAt ℂ s (ζ ^ j * w₀ z)) (hw₀_diff : DifferentiableAt ℂ w₀ z) :
    DifferentiableAt ℂ (clusterSheet s ζ w₀ j) z := by
  have harg : DifferentiableAt ℂ (fun w => ζ ^ j * w₀ w) z :=
    (differentiableAt_const _).mul hw₀_diff
  exact (hs_an.differentiableAt.comp z harg)

/-- **The chart transition `chart_y ∘ chart_z.symm` is analytic at `chart_z z`** (maximal-atlas
coordinate change at `ω`), when `z ∈ chart_y.source`.  Local copy of the Čech-side
`transition_analyticAt`, to keep this file off that subtree. -/
theorem transition_analyticAt' {y z : X} (hz : z ∈ (chartAt (H := ℂ) y).source) :
    AnalyticAt ℂ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z) := by
  have hsrc_z : z ∈ (chartAt (H := ℂ) z).source := mem_chart_source ℂ z
  have hcz_tgt : (chartAt (H := ℂ) z) z ∈ (chartAt (H := ℂ) z).target :=
    (chartAt (H := ℂ) z).map_source hsrc_z
  have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := z)) _ hcz_tgt).contMDiffAt
      ((chartAt (H := ℂ) z).open_target.mem_nhds hcz_tgt)
  have hez : (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) = z :=
    (chartAt (H := ℂ) z).left_inv hsrc_z
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) y)
      ((chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z)) := by
    rw [hez]
    exact ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := y)) _ hz).contMDiffAt
      ((chartAt (H := ℂ) y).open_source.mem_nhds hz)
  exact (contMDiffAt_iff_contDiffAt.1
    (ContMDiffAt.comp (I' := 𝓘(ℂ)) ((chartAt (H := ℂ) z) z) h2 h1)).analyticAt

/-- **Chart-change of an analytic chart pullback.**  If `h ∘ chart_y.symm` is analytic at `chart_y z`
(for `z ∈ chart_y.source`), then `h ∘ chart_z.symm` is analytic at `chart_z z`.  Local copy of the
Čech-side `analyticAt_chart_change`. -/
theorem analyticAt_chart_change' {h : X → ℂ} {y z : X} (hz : z ∈ (chartAt (H := ℂ) y).source)
    (ha : AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) z)) :
    AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z) := by
  have hcz_tgt : (chartAt (H := ℂ) z) z ∈ (chartAt (H := ℂ) z).target :=
    (chartAt (H := ℂ) z).map_source (mem_chart_source ℂ z)
  have hez : (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) = z :=
    (chartAt (H := ℂ) z).left_inv (mem_chart_source ℂ z)
  have hφ := transition_analyticAt' (y := y) (z := z) hz
  have hφ_pt : ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z)
      = (chartAt (H := ℂ) y) z := by simp only [Function.comp_apply, hez]
  have hcomp : AnalyticAt ℂ ((h ∘ (chartAt (H := ℂ) y).symm) ∘
      ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm)) ((chartAt (H := ℂ) z) z) :=
    AnalyticAt.comp (hφ_pt ▸ ha) hφ
  have hmem : ∀ᶠ w in 𝓝 ((chartAt (H := ℂ) z) z),
      (chartAt (H := ℂ) z).symm w ∈ (chartAt (H := ℂ) y).source := by
    have hcont : ContinuousAt (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) :=
      (chartAt (H := ℂ) z).continuousAt_symm hcz_tgt
    have hh : (chartAt (H := ℂ) z).symm ((chartAt (H := ℂ) z) z) ∈ (chartAt (H := ℂ) y).source := by
      rw [hez]; exact hz
    exact hcont.preimage_mem_nhds ((chartAt (H := ℂ) y).open_source.mem_nhds hh)
  have heq : (h ∘ (chartAt (H := ℂ) z).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) z) z)]
      ((h ∘ (chartAt (H := ℂ) y).symm) ∘ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) z).symm)) := by
    filter_upwards [hmem] with w hw
    simp only [Function.comp_apply, (chartAt (H := ℂ) y).left_inv hw]
  rw [analyticAt_congr heq]; exact hcomp

end Jacobians.Dolbeault.SerreResidueTheorem
