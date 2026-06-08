/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceSheetCovector

/-!
# The fibre-sum bridge: bundle trace ↔ planar fibre trace (Gate A step 2/3)

Building on the per-sheet covector linchpin (`FormTraceSheetCovector`) and the `localRep`
frame-transition law, this file proves the **single-sheet bridge**: the bundle pushforward summand
`sheetPullback ω₀ s y (1)` (read in the value chart) equals the *planar* `FormTraceFibre.fibreTrace`
summand `coeffAt ω₀ (xs) (sh w)·deriv(sh) w` for the `g ≡ 1` frame, where `sh` is the section read in
the **fixed** source chart at a base fibre point `xs`.

The reconciliation is the `dz`-Jacobian cancellation: the bundle summand is read in the *moving*
fibre point's own chart, the planar summand in the *fixed* `xs`-chart; the `localRep` frame-transition
law (`localRep_eq_transition_mul_self`) supplies the ratio, which the chain rule for `deriv` cancels
against the section-derivative ratio.  This is the source-chart-independence of the value-chart
`dz`-coefficient — the heart of Miranda §VIII.3's "the trace is a well-defined form".

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceSheet

open Jacobians Jacobians.Dolbeault Jacobians.Montel

set_option linter.unusedSectionVars false

variable {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- **Single-sheet bridge (source-chart independence of the `dz`-coefficient).**  For a bundle
section `s : Y → X` `MDifferentiable` at `y`, with the fibre point `s y` lying in the chart source of
a *fixed* base point `xs`, the bundle per-sheet covector (value chart, affine unit tangent) equals the
planar `coeffAt·deriv` summand read in the fixed `xs`-chart:

> `sheetPullback ω₀ s y 1 = coeffAt ω₀ xs (sh (chart_y y)) · deriv sh (chart_y y)`,

where `sh := chart_xs ∘ s ∘ chart_y.symm` is the section in the fixed source chart.  The proof reads
the LHS via the linchpin (`sheetPullback_one_eq_coeffAt_mul_deriv`, in the *moving* `s y`-chart), then
applies the `localRep` frame-transition law + the chain rule for `deriv` to convert to the fixed
`xs`-chart. -/
theorem sheetPullback_one_eq_fixedChart_coeffAt_mul_deriv (ω₀ : HolomorphicOneForms X) (s : Y → X)
    {y : Y} (xs : X) (hs : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) s y)
    (hmem : s y ∈ (chartAt ℂ xs).source)
    (hsh_diff : DifferentiableAt ℂ (fun z => (chartAt ℂ xs) (s ((chartAt ℂ y).symm z)))
      ((chartAt ℂ y) y))
    (htrans_diff : DifferentiableAt ℂ
      (fun w => (chartAt ℂ (s y)) ((chartAt ℂ xs).symm w)) ((chartAt ℂ xs) (s y))) :
    sheetPullback ω₀ s y (1 : ℂ)
      = coeffAt ω₀ xs ((fun z => (chartAt ℂ xs) (s ((chartAt ℂ y).symm z))) ((chartAt ℂ y) y))
        * deriv (fun z => (chartAt ℂ xs) (s ((chartAt ℂ y).symm z))) ((chartAt ℂ y) y) := by
  -- Abbreviations: `P := s y` the moving fibre point; `b' := chart_y y` the base value-coord.
  set P : X := s y with hP
  set b' : ℂ := (chartAt ℂ y) y with hb'
  -- The inner planar section `sh := chart_xs ∘ s ∘ chart_y.symm`, with `sh b' = chart_xs P`.
  set sh : ℂ → ℂ := fun z => (chartAt ℂ xs) (s ((chartAt ℂ y).symm z)) with hsh
  have hshb' : sh b' = (chartAt ℂ xs) P := by
    simp only [hsh, hb', hP]; rw [(chartAt ℂ y).left_inv (mem_chart_source ℂ y)]
  -- The outer chart-transition `tr := chart_P ∘ chart_xs.symm`.
  set tr : ℂ → ℂ := fun w => (chartAt ℂ P) ((chartAt ℂ xs).symm w) with htr
  -- LHS via the linchpin (read in the *moving* `P`-chart).
  rw [sheetPullback_one_eq_coeffAt_mul_deriv ω₀ s hs, coeffAt_chartCenter]
  -- RHS coefficient: `coeffAt ω₀ xs (chart_xs P) = localRep ω₀ xs P`, then the frame-transition.
  have hRHScoeff : coeffAt ω₀ xs ((chartAt ℂ xs) P) = Jacobians.Montel.localRep ω₀ xs P := by
    rw [coeffAt]; congr 1; exact (chartAt ℂ xs).left_inv hmem
  rw [hshb', hRHScoeff, localRep_eq_transition_mul_self ω₀ xs P hmem]
  -- The chain-rule identity: `chart_P ∘ s ∘ chart_y.symm =ᶠ[𝓝 b'] tr ∘ sh` near `b'`
  -- (since `chart_xs.symm ∘ chart_xs = id` near `P`, `s` continuous), so its `deriv` factors.
  have hsymm_b' : (chartAt ℂ y).symm b' = y := by
    rw [hb']; exact (chartAt ℂ y).left_inv (mem_chart_source ℂ y)
  have hcomp_eq : (fun z => (chartAt ℂ (s y)) (s ((chartAt ℂ y).symm z))) =ᶠ[𝓝 b'] tr ∘ sh := by
    -- `s ∘ chart_y.symm` is continuous at `b'` and maps `b' ↦ P ∈ chart_xs.source`.
    have hsymm_cont : ContinuousAt (chartAt ℂ y).symm b' := by
      have hb'_tgt : b' ∈ (chartAt ℂ y).target := by
        rw [hb']; exact (chartAt ℂ y).map_source (mem_chart_source ℂ y)
      exact ((chartAt ℂ y).continuousOn_symm).continuousAt
        ((chartAt ℂ y).open_target.mem_nhds hb'_tgt)
    have hcont : ContinuousAt (fun z => s ((chartAt ℂ y).symm z)) b' := by
      refine ContinuousAt.comp ?_ hsymm_cont
      rw [hsymm_b']; exact hs.continuousAt
    have hval : (fun z => s ((chartAt ℂ y).symm z)) b' = P := by
      simp only [hP]; rw [hsymm_b']
    have hpre : ∀ᶠ z in 𝓝 b', s ((chartAt ℂ y).symm z) ∈ (chartAt ℂ xs).source :=
      hcont.eventually_mem (by simp only [hval]; exact (chartAt ℂ xs).open_source.mem_nhds hmem)
    filter_upwards [hpre] with z hz
    show (chartAt ℂ (s y)) (s ((chartAt ℂ y).symm z))
        = (chartAt ℂ P) ((chartAt ℂ xs).symm ((chartAt ℂ xs) (s ((chartAt ℂ y).symm z))))
    rw [(chartAt ℂ xs).left_inv hz]
  rw [hcomp_eq.deriv_eq]
  -- Chain rule for `tr ∘ sh` at `b'`, with `sh b' = chart_xs P`.
  rw [deriv_comp b' (by rw [hshb']; exact htrans_diff) hsh_diff, hshb']
  ring

end Jacobians.Dolbeault.FormTraceSheet
