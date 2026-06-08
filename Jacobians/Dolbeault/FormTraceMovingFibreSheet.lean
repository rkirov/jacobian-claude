/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceCoherentFromMoving

/-!
# The moving-fibre coherence datum from a sheet system (Gate A, §VIII.3 — global index bijection)

`Jacobians.Dolbeault.FormTraceMovingFibre` proved the §VIII.3 monodromy heart: a `MovingCoherenceDatum`
yields the local self-coherence of the geometric trace, and is constructible from a
*continuously-varying index bijection* alone (`MovingCoherenceDatum.ofBijection`).  All germ /
`dz`-Jacobian content is discharged there; the residual is the **index bijection + section
identification + chart-pullback differentiability**.

This file discharges the *mechanical* half of that residual — the differentiability side-conditions —
by feeding the proved branched-cover sheet machinery (`Jacobians.LocalSheetSystem`, Forster §4.22) into
`MovingCoherenceDatum.ofBijection`.  The continuously-varying sections are the sheets `S.sheet i` of a
`LocalSheetSystem` for `f.holoRepr` off the critical set, which are `C^ω` two-sided local inverses; the
chart-transition differentiability is the analytic chart change of the `C^ω` atlas (proved inline,
`transition_analyticAt_overlap`); and the section identification (planar sheet ≈ manifold-section
chart-pullback) is the proved `FormTraceSheet.fibreTrace_sheet_eventuallyEq`.

What remains, after this file, is the *geometric* half: that the global selection `Φ` actually
**re-selects the moving fibre** — near each base value, `(Φ b').xs` enumerates the sheet values
`S.sheet · b'` via an index bijection `e : (Φ b').ι ≃ D.ι`.  That is the genuine §VIII.3 index
bijection (the branched cover's sheets permute continuously) and is carried as the single hypothesis
`hsel` of the constructor.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `transition_analyticAt_overlap` — the chart transition `chartAt z ∘ (chartAt y).symm` is analytic at
  any overlap point (inline, no heavy Čech import).
* `MovingCoherenceDatum.ofSheetSystem` — build a `MovingCoherenceDatum` at a base value `b₀` from a
  `LocalSheetSystem` for `f.holoRepr`, a reference fibre `D` enumerated by the sheets, and the diagonal
  re-selection agreement `hsel`.  Discharges every differentiability side-condition of
  `MovingCoherenceDatum.ofBijection` from the sheet smoothness + the analytic chart change.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22 (local sheet systems), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceMovingFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceGlobal
  Jacobians.Dolbeault.FormTraceSheet

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}

/-! ### The analytic chart change at an overlap point (inline)

The chart transition `chartAt z ∘ (chartAt y).symm` is analytic at `chartAt y x` for any `x` in the
overlap of the two chart sources — the `C^ω`-atlas chart change.  This is the same statement as
`Jacobians.Dolbeault.transition_analyticAt_of_mem`, reproved inline to avoid importing the heavy Čech
machinery.  It supplies the chart-transition differentiability fields of `hbij`. -/

/-- **Chart transition analytic at an overlap point.**  For `x` in both chart sources `chartAt y` and
`chartAt z`, the transition `chartAt z ∘ (chartAt y).symm` is `AnalyticAt ℂ` at `chartAt y x`.  Chart
and inverse-chart are `C^ω` (`contMDiffOn_chart`/`contMDiffOn_chart_symm`); the composition is `C^ω`,
and `C^ω` ⇒ analytic. -/
theorem transition_analyticAt_overlap {y z x : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxz : x ∈ (chartAt (H := ℂ) z).source) :
    AnalyticAt ℂ ((chartAt (H := ℂ) z) ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) x) := by
  have hw_tgt : (chartAt (H := ℂ) y) x ∈ (chartAt (H := ℂ) y).target :=
    (chartAt (H := ℂ) y).map_source hxy
  have h1 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x) :=
    ((contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := y)) _ hw_tgt).contMDiffAt
      ((chartAt (H := ℂ) y).open_target.mem_nhds hw_tgt)
  have hey : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x) = x :=
    (chartAt (H := ℂ) y).left_inv hxy
  have h2 : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt (H := ℂ) z)
      ((chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) x)) := by
    rw [hey]
    exact ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := z)) _ hxz).contMDiffAt
      ((chartAt (H := ℂ) z).open_source.mem_nhds hxz)
  exact (contMDiffAt_iff_contDiffAt.1
    (ContMDiffAt.comp (I' := 𝓘(ℂ)) ((chartAt (H := ℂ) y) x) h2 h1)).analyticAt

/-- **Chart transition differentiable at an overlap point.**  The `DifferentiableAt ℂ` corollary of
`transition_analyticAt_overlap`. -/
theorem transition_differentiableAt_overlap {y z x : X}
    (hxy : x ∈ (chartAt (H := ℂ) y).source) (hxz : x ∈ (chartAt (H := ℂ) z).source) :
    DifferentiableAt ℂ (fun w => (chartAt (H := ℂ) z) ((chartAt (H := ℂ) y).symm w))
      ((chartAt (H := ℂ) y) x) :=
  (transition_analyticAt_overlap hxy hxz).differentiableAt

/-! ### The own-chart pullback of a smooth section is differentiable

A section `s : ℂ → X` that is `MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) ω` at `b'`, read in its *own* canonical
chart at `s b'`, gives a `DifferentiableAt ℂ` planar function `z ↦ chartAt (s b') (s z)`.  This is the
`writtenInExtChartAt`-unfolding for the trivial complex model (`extChartAt 𝓘(ℂ) p = chartAt ℂ p`, source
chart `= id`).  It supplies the `hsP_diff` field of `hbij` from sheet smoothness. -/

/-- **The own-chart pullback of a `ContMDiffAt` section is `DifferentiableAt ℂ`.**  If `s : ℂ → X` is
`ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` at `b'`, then `z ↦ (chartAt ℂ (s b')) (s z)` is `DifferentiableAt ℂ` at `b'`.
The canonical chart `chartAt ℂ (s b')` is `C^ω` at `s b'` (`contMDiffOn_chart`), so the composite
`chartAt (s b') ∘ s` is `C^ω` at `b'`; for `ℂ → ℂ` maps `C^ω = ContDiffAt ℂ ω` (`contMDiffAt_iff_contDiffAt`),
which is `DifferentiableAt`.  Supplies the `hsP_diff` field of `hbij` from sheet smoothness. -/
theorem differentiableAt_chart_pullback_section {s : ℂ → X} {b' : ℂ}
    (hs : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω s b') :
    DifferentiableAt ℂ (fun z => (chartAt ℂ (s b')) (s z)) b' := by
  -- The chart at `s b'` is `C^ω` at `s b'` (its own source).
  have hchart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ (s b')) (s b') :=
    ((contMDiffOn_chart (I := 𝓘(ℂ)) (n := ω) (x := s b')) _ (mem_chart_source ℂ (s b'))).contMDiffAt
      ((chartAt ℂ (s b')).open_source.mem_nhds (mem_chart_source ℂ (s b')))
  -- Compose: `chartAt (s b') ∘ s` is `C^ω` at `b'`, a `ℂ → ℂ` map, hence `ContDiffAt ℂ ω`.
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun z => (chartAt ℂ (s b')) (s z)) b' :=
    hchart.comp b' hs
  exact (contMDiffAt_iff_contDiffAt.1 hcomp).differentiableAt (by decide)

/-! ### The moving-fibre coherence datum from continuously-varying smooth sections

We now assemble `MovingCoherenceDatum.ofBijection` from continuously-varying *manifold* sections `sec :
D.ι → ℂ → X` of `f.holoRepr` (the sheets of a branched cover), discharging every differentiability
side-condition of `hbij` from section smoothness + the analytic chart change.  The single remaining
hypothesis is the genuine §VIII.3 index bijection: near `b₀`, the re-selected fibre `Φ b'` is enumerated
by the moving sections via a bijection `e : (Φ b').ι ≃ D.ι` with `(Φ b').xs i' = sec (e i') b'`.

The section-derivative match (the `hsheet_deriv` field) is *derived* here: by
`FormTraceSheet.fibreTrace_sheet_eventuallyEq`, the planar sheet of `fibreTrace ω₀ f (Φ b')` germ-equals
the chart-pullback `chart_{sec (e i') b'} ∘ sec (e i')` (both are right-inverses of the chart-pullback of
`f.holoRepr` through `(Φ b').xs i' = sec (e i') b'`), so their derivatives agree. -/

/-- **A moving-fibre coherence datum from continuously-varying smooth sections.**  Let `D :
FibreRegularData g f b₀`, and `sec : D.ι → ℂ → X` a family of manifold sections of `f.holoRepr` through
`D`'s fibre points: `sec i b₀ = D.xs i`, each `sec i` is `C^ω` at `b₀`, and `f.holoRepr (sec i b') = b'`
on a neighbourhood of `b₀`.  Assume the **§VIII.3 index bijection**: for `b'` near `b₀`, the re-selected
fibre `Φ b'` is enumerated by the moving sections — there is `e : (Φ b').ι ≃ D.ι` with `(Φ b').xs i' =
sec (e i') b'` for all `i'`, and each `sec i b'` lies in `chart_{D.xs i}.source` (the moving sections
stay near the fibre points).  Then `Φ` has a `MovingCoherenceDatum` at `b₀` with fixed fibre `D`.

*All* the germ / `dz`-Jacobian / differentiability content is discharged: the section-derivative match
via `fibreTrace_sheet_eventuallyEq`, the chart-pullback differentiability via
`differentiableAt_chart_pullback_section`, and the chart transitions via `transition_analyticAt_overlap`.
The caller supplies only the geometric re-selection bijection. -/
noncomputable def MovingCoherenceDatum.ofSheetSections
    {Φ : (b : ℂ) → FibreRegularData g f b} {b₀ : ℂ}
    (D : FibreRegularData g f b₀) (sec : D.ι → ℂ → X)
    (hbase : ∀ i, sec i b₀ = D.xs i)
    (hsmooth : ∀ i, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (sec i) b₀)
    (hsec : ∀ i, ∀ᶠ b' in 𝓝 b₀, f.holoRepr (sec i b') = b')
    (hsel : ∀ᶠ b' in 𝓝 b₀, ∃ e : (Φ b').ι ≃ D.ι,
      (∀ i', (Φ b').xs i' = sec (e i') b') ∧
      (∀ i, sec i b' ∈ (chartAt ℂ (D.xs i)).source)) :
    MovingCoherenceDatum ω₀ g f Φ b₀ := by
  refine MovingCoherenceDatum.ofBijection D sec hbase
    (fun i => (hsmooth i).continuousAt) hsec ?_
  -- The moving sections are `C^ω` (`ContMDiffAt` is an open condition) and are sections of `f.holoRepr`
  -- on a neighbourhood of `b₀`.  Bundle these per-`i` eventual facts with the re-selection `hsel`.
  have hsmooth_nhds : ∀ᶠ b' in 𝓝 b₀, ∀ i, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (sec i) b' :=
    eventually_all.mpr (fun i =>
      (contMDiffAt_iff_contMDiffAt_nhds (by decide : (ω : WithTop ℕ∞) ≠ ∞)).mp (hsmooth i))
  -- The section property holds eventually-eventually: near each `b'` close to `b₀`, `sec i` is a
  -- section of `f.holoRepr` on a neighbourhood of `b'` (the section set is open around `b₀`).
  have hsec_evev : ∀ᶠ b' in 𝓝 b₀, ∀ i, ∀ᶠ w in 𝓝 b', f.holoRepr (sec i w) = w :=
    eventually_all.mpr (fun i => eventually_eventually_nhds.mpr (hsec i))
  filter_upwards [hsel, hsmooth_nhds, hsec_evev] with b' hb'sel hb'smooth hb'sec
  obtain ⟨e, hxs, hmem⟩ := hb'sel
  -- For each fixed-frame index `i`, the chart-pullback `chart_{sec i b'} ∘ sec i` is the planar
  -- right-inverse of `φ_i = f.holoRepr ∘ chart_{D.xs i}.symm`... but we work in the chart at `sec i b'`.
  refine ⟨e, hxs, ?_, fun i => (hb'smooth i).continuousAt,
    fun i => differentiableAt_chart_pullback_section (hb'smooth i), hmem, ?_, ?_⟩
  · -- **The section-derivative match** (the `hsheet_deriv` field).  The planar sheet of `fibreTrace
    -- ω₀ f (Φ b')` germ-equals the chart-pullback `chart_{sec (e i') b'} ∘ sec (e i')`, so their
    -- derivatives at `b'` agree.
    intro i'
    -- The chart-pullback `s := chart_{sec (e i') b'} ∘ sec (e i')` is the right-inverse of the
    -- chart-pullback of `f.holoRepr` through `(Φ b').xs i' = sec (e i') b'`.
    obtain ⟨hrinv_base, hrinv_cont, hrinv_rinv⟩ :=
      chartPullback_section_rinv f (sec := sec (e i')) (b₀ := b') (x := sec (e i') b') rfl
        (hb'smooth (e i')).continuousAt (hb'sec (e i'))
    -- Apply `fibreTrace_sheet_eventuallyEq` with `D' = Φ b'`, sheet `i'`, section `s`; rewrite the
    -- fibre point `(Φ b').xs i' = sec (e i') b'` (`hxs i'`) so the right-inverse data matches.
    have hsheet := FormTraceSheet.fibreTrace_sheet_eventuallyEq ω₀ f (Φ b') i'
      (s := fun z => (chartAt ℂ (sec (e i') b')) (sec (e i') z))
      (by rw [hxs i']) hrinv_cont
      (by rw [hxs i']; exact hrinv_rinv)
    exact hsheet.deriv_eq
  · -- chart transition `chart_{D.xs i} ∘ chart_{sec i b'}.symm` differentiable at `chart_{sec i b'} (sec i b')`.
    intro i
    exact transition_differentiableAt_overlap (mem_chart_source ℂ (sec i b')) (hmem i)
  · -- chart transition `chart_{sec i b'} ∘ chart_{D.xs i}.symm` differentiable at `chart_{D.xs i} (sec i b')`.
    intro i
    exact transition_differentiableAt_overlap (hmem i) (mem_chart_source ℂ (sec i b'))

end Jacobians.Dolbeault.FormTraceMovingFibre
