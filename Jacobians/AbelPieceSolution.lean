/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Abel engine C-2 (manifold layer): the per-piece weak solution (Forster 20.5(a))

Lifts the planar piece solution (`PlanarPieceSolution`, `AbelPlanarPiece`) to a genuine
`WeakSolution` of the two-point divisor `(γ(t_{k+1})) − (γ(t_k))` on the surface:

* `exists_chartCompare_unit` — the chart-comparison unit: for `p` in the source of the chart
  at `x₀`, the centred coordinate of the `x₀`-chart factors through the canonical centred
  coordinate `chartCoord p` by a smooth nonvanishing unit (`dslope` of the chart transition;
  nonvanishing from `deriv_chart_transition_of_isManifold_ne_zero`).  This is what lets a
  divisor-normal-form in the *piece* chart be re-read in the *canonical* chart that
  `WeakSolution` fixes.
* `exists_pieceWeakSolution` — the per-piece weak solution: glue `F = W·(z−β)/(z−α)` (read
  through the piece chart) with the constant `1` off the compact `5ρ`-ball preimage; its
  local units at the pole `Pa` / zero `Pb` are the planar cofactor times the
  chart-comparison units.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.5 proof part (a),
pp. 162–163; plan `docs/walls_bc_plan_2026-06-10.md`, phase C-2 (E2).
-/
import Jacobians.AbelPlanarPiece
import Jacobians.AbelWeakSolutions
import Jacobians.Discharge.Manifold.MeromorphicAt

noncomputable section

-- ℝ/ℂ-module diamond discipline (as in `AbelChains`/`AbelWeakSolutions`).
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Set Metric Filter Jacobians.AbelPlanar

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The chart-comparison unit -/

/-- **The chart-comparison unit.**  For `p` in the source of the chart at `x₀`, the centred
`x₀`-chart coordinate of `p` factors as a smooth nonvanishing unit times the canonical
centred coordinate `chartCoord p`:

  `chartAt x₀ x − chartAt x₀ p = u x · chartCoord p x`   near `p`.

`u` is `dslope` of the chart transition read through the chart at `p`; its value at `p` is
the transition derivative, nonzero on a complex manifold. -/
theorem exists_chartCompare_unit {x₀ p : X} (hp : p ∈ (chartAt (H := ℂ) x₀).source) :
    ∃ (V : Set X) (u : X → ℂ), IsOpen V ∧ p ∈ V ∧
      V ⊆ (chartAt (H := ℂ) x₀).source ∩ (chartAt (H := ℂ) p).source ∧
      (∀ x ∈ V, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) u x) ∧ (∀ x ∈ V, u x ≠ 0) ∧
      ∀ x ∈ V, (chartAt (H := ℂ) x₀) x - (chartAt (H := ℂ) x₀) p
        = u x * chartCoord p x := by
  set e : OpenPartialHomeomorph X ℂ := chartAt (H := ℂ) x₀ with he
  set ep : OpenPartialHomeomorph X ℂ := chartAt (H := ℂ) p with hep
  set w₀ : ℂ := ep p with hw₀
  set T : ℂ → ℂ := e ∘ ep.symm with hT
  -- the transition is analytic at the centre with nonzero derivative
  have hTanal : AnalyticAt ℂ T w₀ := Dolbeault.transition_analyticAt hp
  have hT'ne : deriv T w₀ ≠ 0 :=
    Jacobians.Discharge.deriv_chart_transition_of_isManifold_ne_zero
      (chart_mem_atlas ℂ p) (chart_mem_atlas ℂ x₀) (mem_chart_source ℂ p) hp
  -- `q := dslope T w₀` is analytic at `w₀` with nonzero value there
  obtain ⟨pser, hpser⟩ := hTanal
  have hq : AnalyticAt ℂ (dslope T w₀) w₀ := ⟨_, hpser.has_fpower_series_dslope_fslope⟩
  have hq0 : dslope T w₀ w₀ ≠ 0 := by
    rw [dslope_same]
    exact hT'ne
  -- an open planar neighbourhood where `q` is analytic and nonvanishing
  have hev : ∀ᶠ w in 𝓝 w₀, AnalyticAt ℂ (dslope T w₀) w ∧ dslope T w₀ w ≠ 0 :=
    hq.eventually_analyticAt.and (hq.continuousAt.eventually_ne hq0)
  obtain ⟨O, hOsub, hOopen, hw₀O⟩ := _root_.eventually_nhds_iff.mp hev
  -- the manifold neighbourhood and the unit
  refine ⟨(ep.source ∩ ep ⁻¹' O) ∩ e.source, fun x => dslope T w₀ (ep x),
    ((ep.isOpen_inter_preimage hOopen).inter e.open_source),
    ⟨⟨mem_chart_source ℂ p, hw₀O⟩, hp⟩, fun x hx => ⟨hx.2, hx.1.1⟩, ?_, ?_, ?_⟩
  · -- smoothness: `q ∘ (chart at p)` is chart-analytic at every point of the set
    rintro x ⟨⟨hxs, hxO⟩, _⟩
    refine Dolbeault.contMDiffAt_real_of_chart_analyticAt ?_
    -- read in the self chart at `x`: `q ∘ (ep ∘ (chartAt x).symm)`
    have htrans : AnalyticAt ℂ ((ep : X → ℂ) ∘ (chartAt (H := ℂ) x).symm)
        ((chartAt (H := ℂ) x) x) := Dolbeault.transition_analyticAt hxs
    have hpt : ((ep : X → ℂ) ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)
        = ep x := by
      simp only [Function.comp_apply, (chartAt (H := ℂ) x).left_inv (mem_chart_source ℂ x)]
    have hqx : AnalyticAt ℂ (dslope T w₀)
        (((ep : X → ℂ) ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)) := by
      rw [hpt]
      exact (hOsub _ hxO).1
    exact hqx.comp htrans
  · -- nonvanishing
    rintro x ⟨⟨hxs, hxO⟩, _⟩
    exact (hOsub _ hxO).2
  · -- the factorization
    rintro x ⟨⟨hxs, _⟩, hxe⟩
    have hfact : (ep x - w₀) * dslope T w₀ (ep x) = T (ep x) - T w₀ := by
      have h := sub_smul_dslope T w₀ (ep x)
      simpa [smul_eq_mul] using h
    have hTx : T (ep x) = e x := by
      rw [hT]
      simp only [Function.comp_apply, ep.left_inv hxs]
    have hTw₀ : T w₀ = e p := by
      rw [hT, hw₀]
      simp only [Function.comp_apply, ep.left_inv (mem_chart_source ℂ p)]
    have hcc : chartCoord p x = ep x - w₀ := rfl
    rw [hcc, ← hTx, ← hTw₀, ← hfact]
    ring

end Jacobians
