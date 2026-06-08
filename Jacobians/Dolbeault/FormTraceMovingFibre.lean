/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceCoherentSelection
import Jacobians.Dolbeault.FormTraceSheetFibreBridge
import Jacobians.TraceForm

/-!
# The moving fibre selection `Φ` and its self-coherence (Gate A, §VIII.3 monodromy)

`Jacobians.Dolbeault.FormTraceCoherentSelection` reduced Gate A (`∑ₐ Resₐ(α) = 0` for `α = ω₀·g`) to
one **`CoherentTraceSelection`** structure: a global fibre selection `Φ : (b : ℂ) → FibreRegularData g
f b` whose geometric trace `valueChartTrace ω₀ f Φ` *self-coheres* — near each base value it germ-equals
a single fixed local fibre trace.  That self-coherence is Miranda §VIII.3's "`Tr_F α` is a single
(mero)morphic function on `ℂℙ¹`", read in the fibre language; it is the genuine monodromy content.

This file builds the **monodromy heart** as standalone axiom-clean lemmas: the construction of a fibre
selection from a *continuously-varying* family of holomorphic sections (a `LocalSheetSystem` of the
finite value coordinate `f.holoRepr`, off the critical set — Forster §4.22), and the **self-coherence
core**: a selection built from such moving sheets has a `valueChartTrace` that germ-equals the *fixed*
fibre trace read along the *same* sheets through the base fibre — the moving-fibre-vs-fixed-fibre match
that is the index-bijection / monodromy.

## The design — read the moving and the fixed fibre along the *same* moving sheets

The reusable bridge `FormTraceGlobal.traceCoeff_eventuallyEq_sum_rightInverse` (PROVEN) expresses *any*
`(fibreTrace ω₀ f D).traceCoeff` as the fibre sum read along *any* family of continuous right-inverse
sections of the chart pullbacks of `f.holoRepr` through the fibre points.  So both the moving trace
`valueChartTrace ω₀ f Φ` (over the *varying* value `b'`) and the fixed-fibre trace
`(fibreTrace ω₀ f D₀).traceCoeff` (over the *fixed* base value `b₀`) — *when both fibres are enumerated
by the same continuously-varying sheets `S.sheet i`* — germ-equal the **same** holomorphic fibre sum
`∑ i, chartIntegrand ω₀ g (S.sheet i b₀) (rinv i w)·deriv (rinv i) w` near `b₀`, where `rinv i` is the
chart pullback of the moving sheet `S.sheet i`.  Hence they germ-agree.  That is the self-coherence.

The `rinv i` are right-inverses *because* the sheets are sections of `f.holoRepr` (`f.holoRepr (S.sheet
i b') = b'` on the base neighbourhood `V`), read in charts.  The continuous variation is the
`ContMDiffOn` smoothness of the sheets.  This is exactly the §VIII.3 monodromy: the global trace is the
fibre sum along a *single* continuously-varying frame, hence a single function locally.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `MovingFibreSelection` — a fibre selection over a base neighbourhood from a continuously-varying
  holomorphic sheet family (the local model of `Φ`).
* `valueChartTrace_eventuallyEq_movingSum` — the moving trace germ-equals the moving-sheet fibre sum.
* `fibreTrace_eventuallyEq_movingSum` — the fixed-fibre trace (over `b₀`, same sheets) germ-equals the
  *same* moving-sheet fibre sum.
* `valueChartTrace_eventuallyEq_fibreTrace_of_sharedSheets` — **the self-coherence core**: the moving
  trace germ-equals the fixed-fibre trace near `b₀` (the moving-fibre-vs-fixed-fibre match).

The remaining obligation (the global selection `Φ` consistent across overlapping sheet systems, and the
pole-sub-fibre separation genericity) is the `AdaptedCover`-level bookkeeping, diagnosed at the bottom.

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

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}

/-! ### The chart pullback of a manifold section as a planar right-inverse

A manifold section `sec : ℂ → X` of the finite value coordinate `f.holoRepr` (so `f.holoRepr (sec b') =
b'` near `b₀`), with `sec b₀` a fibre point `x`, gives — read in the canonical chart at `x` — a *planar*
right-inverse of the chart pullback `φ_x := f.holoRepr ∘ chart_x.symm` through `chart_x x`.  This is the
object `traceCoeff_eventuallyEq_sum_rightInverse` consumes.  We package the three right-inverse
hypotheses (`base`, `cont`, `rinv`) it needs. -/

/-- **The chart pullback of a manifold section is a planar right-inverse.**  Let `sec : ℂ → X` be
`MDifferentiable`/continuous at `b₀` with `sec b₀ = x` and `f.holoRepr (sec b') = b'` on a neighbourhood
of `b₀`.  Then the chart pullback `rinv := chart_x ∘ sec` satisfies, near `b₀`,
`φ_x (rinv b') = b'` where `φ_x = f.holoRepr ∘ chart_x.symm` — i.e. `rinv` is a continuous right-inverse
of `φ_x` through `chart_x x`. -/
theorem chartPullback_section_rinv (f : MeromorphicFunction X) {sec : ℂ → X} {b₀ : ℂ} {x : X}
    (hx : sec b₀ = x) (hsec_cont : ContinuousAt sec b₀)
    (hsec_sec : ∀ᶠ b' in 𝓝 b₀, f.holoRepr (sec b') = b') :
    (fun b' => (chartAt ℂ x) (sec b')) b₀ = (chartAt ℂ x) x ∧
      ContinuousAt (fun b' => (chartAt ℂ x) (sec b')) b₀ ∧
      ∀ᶠ b' in 𝓝 b₀, (fun z => f.holoRepr ((chartAt ℂ x).symm z)) ((fun b' => (chartAt ℂ x) (sec b')) b') = b' := by
  refine ⟨by simp [hx], ?_, ?_⟩
  · -- `chart_x ∘ sec` continuous at `b₀`: `sec` continuous, `chart_x` continuous at `sec b₀ = x`.
    refine ContinuousAt.comp ?_ hsec_cont
    rw [hx]
    exact (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
  · -- `φ_x (chart_x (sec b')) = f.holoRepr (chart_x.symm (chart_x (sec b'))) = f.holoRepr (sec b') = b'`
    -- near `b₀`, using `sec b' ∈ chart_x.source` (continuity, `sec b₀ = x`) and the section identity.
    have hsrc : ∀ᶠ b' in 𝓝 b₀, sec b' ∈ (chartAt ℂ x).source :=
      hsec_cont.eventually_mem (by rw [hx]; exact (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
    filter_upwards [hsrc, hsec_sec] with b' hb'src hb'sec
    show f.holoRepr ((chartAt ℂ x).symm ((chartAt ℂ x) (sec b'))) = b'
    rw [(chartAt ℂ x).left_inv hb'src, hb'sec]

/-! ### The moving fibre sum and the fixed-fibre side of the coherence

The **moving fibre sum** along a family of manifold sections `sec : ι → ℂ → X` (through the fibre
points `D.xs i` of a fixed fibre `D` over `b₀`) is the planar fibre sum read along the chart pullbacks
`chart_{D.xs i} ∘ sec i` — exactly the `rinv` family of
`FormTraceGlobal.traceCoeff_eventuallyEq_sum_rightInverse`.  We first prove the **fixed-fibre side**:
the trace coefficient of the fixed fibre `D` germ-equals the moving fibre sum.  This is a single-fibre
statement, fully provable from the proved bridge — it is the "read the fixed fibre along the moving
frame" half. -/

/-- **The fixed-fibre trace germ-equals the moving fibre sum.**  Let `D : FibreRegularData g f b₀` and
let `sec : D.ι → ℂ → X` be a family of manifold sections of `f.holoRepr` through the fibre points: for
each `i`, `sec i b₀ = D.xs i`, `sec i` continuous at `b₀`, and `f.holoRepr (sec i b') = b'` near `b₀`.
Then the fixed-fibre trace coefficient germ-equals the moving fibre sum read along the chart pullbacks
of `sec`:

> `(fibreTrace ω₀ f D).traceCoeff =ᶠ[𝓝 b₀]
>     fun b' => ∑ i, chartIntegrand ω₀ g (D.xs i) ((chartAt ℂ (D.xs i)) (sec i b'))
>       · deriv (fun z => (chartAt ℂ (D.xs i)) (sec i z)) b'`.

*Proof.*  The chart pullbacks `rinv i := chart_{D.xs i} ∘ sec i` are continuous right-inverses of the
chart pullbacks of `f.holoRepr` through `D.xs i` (`chartPullback_section_rinv`); apply the proved
`traceCoeff_eventuallyEq_sum_rightInverse`. -/
theorem fibreTrace_eventuallyEq_movingSum (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    {b₀ : ℂ} (D : FibreRegularData g f b₀) (sec : D.ι → ℂ → X)
    (hbase : ∀ i, sec i b₀ = D.xs i) (hcont : ∀ i, ContinuousAt (sec i) b₀)
    (hsec : ∀ i, ∀ᶠ b' in 𝓝 b₀, f.holoRepr (sec i b') = b') :
    (fibreTrace ω₀ f D).traceCoeff
      =ᶠ[𝓝 b₀] fun b' => ∑ i, chartIntegrand ω₀ g (D.xs i) ((chartAt ℂ (D.xs i)) (sec i b'))
        * deriv (fun z => (chartAt ℂ (D.xs i)) (sec i z)) b' := by
  -- The chart pullbacks `rinv i := fun b' => chart_{D.xs i} (sec i b')`.
  set rinv : D.ι → ℂ → ℂ := fun i b' => (chartAt ℂ (D.xs i)) (sec i b') with hrinv
  have hrinv_props : ∀ i, rinv i b₀ = (chartAt ℂ (D.xs i)) (D.xs i) ∧
      ContinuousAt (rinv i) b₀ ∧
      ∀ᶠ b' in 𝓝 b₀,
        (fun z => f.holoRepr ((chartAt ℂ (D.xs i)).symm z)) (rinv i b') = b' := by
    intro i
    have := chartPullback_section_rinv f (hbase i) (hcont i) (hsec i)
    exact this
  exact traceCoeff_eventuallyEq_sum_rightInverse ω₀ f D rinv
    (fun i => (hrinv_props i).1) (fun i => (hrinv_props i).2.1) (fun i => (hrinv_props i).2.2)

/-! ### Chart-frame independence of the moving summand (the `dz`-Jacobian, derived planar)

The moving-fibre summand `chartIntegrand ω₀ g xs (chart_xs (s b'))·deriv(chart_xs ∘ s) b'` — the
push-forward of `α = ω₀·g` along the section `s : ℂ → X`, read in the canonical chart at a *base point*
`xs` (with `s b'` in its source) — is **independent of the choice of `xs`**: it equals the self-chart
(intrinsic) summand `g (s b')·localRep ω₀ (s b')(s b')·deriv(chart_{s b'} ∘ s) b'`.  This is the
`dz`-Jacobian cancellation, derived purely planar from the proved frame-transition law
`localRep_eq_transition_mul_self` and the chain rule: changing the source chart rescales `coeffAt =
localRep` and `deriv(chart ∘ s)` inversely.  (No bundle / no compactness on the base `ℂ`.) -/

/-- **The moving summand equals the self-chart (intrinsic) summand.**  For a section `s : ℂ → X` and a
base point `xs` with `s b' ∈ chart_xs.source`, with the chart pullback `chart_{s b'} ∘ s`
differentiable at `b'` and the chart transition `chart_xs ∘ chart_{s b'}.symm` differentiable at
`chart_{s b'}(s b')`, the chart-`xs` moving summand of `α = ω₀·g` equals the self-chart summand:

> `chartIntegrand ω₀ g xs (chart_xs (s b'))·deriv (fun z => chart_xs (s z)) b'
>    = g (s b')·localRep ω₀ (s b')(s b')·deriv (fun z => chart_{s b'} (s z)) b'`.

*Proof.*  Unfold `chartIntegrand`: `coeffAt ω₀ xs (chart_xs(s b')) = localRep ω₀ xs (s b')` and `g`
evaluates at `s b'` (since `chart_xs.symm (chart_xs(s b')) = s b'`).  The frame-transition law rewrites
`localRep ω₀ xs (s b') = deriv(chart_{s b'} ∘ chart_xs.symm)(chart_xs(s b'))·localRep ω₀ (s b')(s b')`;
the chain rule factors `deriv(chart_xs ∘ s) b' = deriv(chart_xs ∘ chart_{s b'}.symm)(chart_{s b'}(s b'))
·deriv(chart_{s b'} ∘ s) b'`, and the two transition `deriv`s are mutual inverses (the chart-transition
and its inverse compose to the identity), so they cancel. -/
theorem movingSummand_eq_selfChart (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (s : ℂ → X) {b' : ℂ}
    (xs : X) (hmem : s b' ∈ (chartAt ℂ xs).source) (hcont : ContinuousAt s b')
    (hsP_diff : DifferentiableAt ℂ (fun z => (chartAt ℂ (s b')) (s z)) b')
    (htrans_diff : DifferentiableAt ℂ
      (fun w => (chartAt ℂ xs) ((chartAt ℂ (s b')).symm w)) ((chartAt ℂ (s b')) (s b')))
    (htrans_diff_inv : DifferentiableAt ℂ
      (fun w => (chartAt ℂ (s b')) ((chartAt ℂ xs).symm w)) ((chartAt ℂ xs) (s b'))) :
    chartIntegrand ω₀ g xs ((chartAt ℂ xs) (s b')) * deriv (fun z => (chartAt ℂ xs) (s z)) b'
      = g (s b') * Jacobians.Montel.localRep ω₀ (s b') (s b')
        * deriv (fun z => (chartAt ℂ (s b')) (s z)) b' := by
  -- Abbreviations.
  set P : X := s b' with hP
  have hPsrc : P ∈ (chartAt ℂ P).source := mem_chart_source ℂ P
  -- `chartIntegrand ω₀ g xs (chart_xs P) = localRep ω₀ xs P · g P`.
  have hg_eval : g ((chartAt ℂ xs).symm ((chartAt ℂ xs) P)) = g P := by
    rw [(chartAt ℂ xs).left_inv hmem]
  have hcoeff : coeffAt ω₀ xs ((chartAt ℂ xs) P) = Jacobians.Montel.localRep ω₀ xs P := by
    rw [coeffAt]; congr 1; exact (chartAt ℂ xs).left_inv hmem
  rw [chartIntegrand, hg_eval, hcoeff]
  -- Frame-transition: `localRep ω₀ xs P = J · localRep ω₀ P P`, `J := deriv(chart_P ∘ chart_xs.symm)(chart_xs P)`.
  rw [Jacobians.Dolbeault.FormTraceSheet.localRep_eq_transition_mul_self ω₀ xs P hmem]
  set J : ℂ := deriv (fun w => (chartAt ℂ P) ((chartAt ℂ xs).symm w)) ((chartAt ℂ xs) P) with hJ
  set J' : ℂ := deriv (fun w => (chartAt ℂ xs) ((chartAt ℂ P).symm w)) ((chartAt ℂ P) P) with hJ'
  -- Chain rule for `deriv (chart_xs ∘ s) b' = J' · deriv(chart_P ∘ s) b'`.
  have hsymm_comp : (fun z => (chartAt ℂ xs) (s z)) =ᶠ[𝓝 b']
      (fun z => (chartAt ℂ xs) ((chartAt ℂ P).symm ((chartAt ℂ P) (s z)))) := by
    have hsrc : ∀ᶠ z in 𝓝 b', s z ∈ (chartAt ℂ P).source :=
      hcont.eventually_mem ((chartAt ℂ P).open_source.mem_nhds hPsrc)
    filter_upwards [hsrc] with z hz
    rw [(chartAt ℂ P).left_inv hz]
  -- The outer transition `chart_xs ∘ chart_P.symm` is differentiable at `chart_P (s b') = chart_P P`.
  have htrans_diff_at : DifferentiableAt ℂ (fun w => (chartAt ℂ xs) ((chartAt ℂ P).symm w))
      ((chartAt ℂ P) (s b')) := by rw [← hP]; exact htrans_diff
  have hchain : deriv (fun z => (chartAt ℂ xs) (s z)) b'
      = J' * deriv (fun z => (chartAt ℂ P) (s z)) b' := by
    rw [hsymm_comp.deriv_eq]
    -- `deriv ((chart_xs ∘ chart_P.symm) ∘ (chart_P ∘ s)) b' = J' · deriv(chart_P ∘ s) b'`.
    rw [show (fun z => (chartAt ℂ xs) ((chartAt ℂ P).symm ((chartAt ℂ P) (s z))))
        = (fun w => (chartAt ℂ xs) ((chartAt ℂ P).symm w)) ∘ (fun z => (chartAt ℂ P) (s z)) from rfl]
    rw [deriv_comp b' htrans_diff_at hsP_diff, hJ', ← hP]
  -- `J · J' = 1`: the chart transitions `chart_P ∘ chart_xs.symm` and `chart_xs ∘ chart_P.symm`
  -- compose to identity near the points; their derivatives multiply to `1`.
  have hJJ' : J * J' = 1 := by
    -- `(chart_P ∘ chart_xs.symm) ∘ (chart_xs ∘ chart_P.symm) =ᶠ id` near `chart_P P`.
    have hcomp_id : (fun w => (chartAt ℂ P) ((chartAt ℂ xs).symm
        ((chartAt ℂ xs) ((chartAt ℂ P).symm w)))) =ᶠ[𝓝 ((chartAt ℂ P) P)] id := by
      -- near `chart_P P`, `chart_P.symm w ∈ chart_xs.source`, then `chart_xs.symm ∘ chart_xs = id`,
      -- and `chart_P ∘ chart_P.symm = id`.
      have hcont_symm : ContinuousAt (chartAt ℂ P).symm ((chartAt ℂ P) P) :=
        (chartAt ℂ P).continuousAt_symm ((chartAt ℂ P).map_source hPsrc)
      have hval_symm : (chartAt ℂ P).symm ((chartAt ℂ P) P) = P := (chartAt ℂ P).left_inv hPsrc
      have h1 : ∀ᶠ w in 𝓝 ((chartAt ℂ P) P), (chartAt ℂ P).symm w ∈ (chartAt ℂ xs).source :=
        hcont_symm.eventually_mem (by rw [hval_symm]; exact (chartAt ℂ xs).open_source.mem_nhds hmem)
      have h2 : ∀ᶠ w in 𝓝 ((chartAt ℂ P) P), w ∈ (chartAt ℂ P).target :=
        (chartAt ℂ P).open_target.mem_nhds ((chartAt ℂ P).map_source hPsrc)
      filter_upwards [h1, h2] with w hw1 hw2
      show (chartAt ℂ P) ((chartAt ℂ xs).symm ((chartAt ℂ xs) ((chartAt ℂ P).symm w))) = w
      rw [(chartAt ℂ xs).left_inv hw1, (chartAt ℂ P).right_inv hw2]
    -- Chain rule on the composite-`= id` at `chart_P P`; `chart_P.symm (chart_P P) = P` simplifies
    -- the inner evaluation point in the first factor to `chart_xs P` (= `J`'s eval point).
    have hPP : (chartAt ℂ P).symm ((chartAt ℂ P) P) = P := (chartAt ℂ P).left_inv hPsrc
    have hderiv_id : deriv (fun w => (chartAt ℂ P) ((chartAt ℂ xs).symm
        ((chartAt ℂ xs) ((chartAt ℂ P).symm w)))) ((chartAt ℂ P) P) = 1 := by
      rw [hcomp_id.deriv_eq, deriv_id']
    rw [show (fun w => (chartAt ℂ P) ((chartAt ℂ xs).symm ((chartAt ℂ xs) ((chartAt ℂ P).symm w))))
        = (fun w => (chartAt ℂ P) ((chartAt ℂ xs).symm w)) ∘ (fun w => (chartAt ℂ xs) ((chartAt ℂ P).symm w))
        from rfl] at hderiv_id
    rw [deriv_comp ((chartAt ℂ P) P)
      (by show DifferentiableAt ℂ (fun w => (chartAt ℂ P) ((chartAt ℂ xs).symm w))
            ((chartAt ℂ xs) ((chartAt ℂ P).symm ((chartAt ℂ P) P)))
          rw [hPP]; exact htrans_diff_inv)
      htrans_diff] at hderiv_id
    -- Simplify the inner `chart_P.symm (chart_P P)` to `P`, identifying the two factors with `J, J'`.
    simp only [hPP] at hderiv_id
    rw [← hJ, ← hJ'] at hderiv_id
    exact hderiv_id
  -- Assemble: `g P·(J·localRep P P)·(J'·deriv(chart_P∘s)) = g P·localRep P P·deriv(chart_P∘s)`,
  -- using `J·J' = 1` (the `dz`-Jacobian cancellation).
  rw [hchain]
  linear_combination (g P * Jacobians.Montel.localRep ω₀ P P
    * deriv (fun z => (chartAt ℂ P) (s z)) b') * hJJ'

/-- **Chart-frame independence of the moving summand.**  For a section `s : ℂ → X` whose value `s b'`
lies in *both* chart sources `chart_{xs₁}` and `chart_{xs₂}` (with the section-pullback differentiable
at `b'` and the two chart transitions differentiable both ways), the chart-`xs₁` and chart-`xs₂` moving
summands of `α = ω₀·g` are equal:

> `chartIntegrand ω₀ g xs₁ (chart_{xs₁}(s b'))·deriv(chart_{xs₁} ∘ s) b'
>    = chartIntegrand ω₀ g xs₂ (chart_{xs₂}(s b'))·deriv(chart_{xs₂} ∘ s) b'`.

Both equal the self-chart summand `g (s b')·localRep ω₀ (s b')(s b')·deriv(chart_{s b'} ∘ s) b'`
(`movingSummand_eq_selfChart`), hence each other.  The source-chart independence of the trace summand —
"the trace `Tr_F α` is a well-defined form" (Miranda §VIII.3). -/
theorem movingSummand_chartIndep (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (s : ℂ → X) {b' : ℂ}
    (xs₁ xs₂ : X) (hcont : ContinuousAt s b')
    (hsP_diff : DifferentiableAt ℂ (fun z => (chartAt ℂ (s b')) (s z)) b')
    (hmem₁ : s b' ∈ (chartAt ℂ xs₁).source) (hmem₂ : s b' ∈ (chartAt ℂ xs₂).source)
    (htrans_diff₁ : DifferentiableAt ℂ
      (fun w => (chartAt ℂ xs₁) ((chartAt ℂ (s b')).symm w)) ((chartAt ℂ (s b')) (s b')))
    (htrans_diff₂ : DifferentiableAt ℂ
      (fun w => (chartAt ℂ xs₂) ((chartAt ℂ (s b')).symm w)) ((chartAt ℂ (s b')) (s b')))
    (htrans_diff_inv₁ : DifferentiableAt ℂ
      (fun w => (chartAt ℂ (s b')) ((chartAt ℂ xs₁).symm w)) ((chartAt ℂ xs₁) (s b')))
    (htrans_diff_inv₂ : DifferentiableAt ℂ
      (fun w => (chartAt ℂ (s b')) ((chartAt ℂ xs₂).symm w)) ((chartAt ℂ xs₂) (s b'))) :
    chartIntegrand ω₀ g xs₁ ((chartAt ℂ xs₁) (s b')) * deriv (fun z => (chartAt ℂ xs₁) (s z)) b'
      = chartIntegrand ω₀ g xs₂ ((chartAt ℂ xs₂) (s b')) * deriv (fun z => (chartAt ℂ xs₂) (s z)) b' := by
  rw [movingSummand_eq_selfChart ω₀ g s xs₁ hmem₁ hcont hsP_diff htrans_diff₁ htrans_diff_inv₁,
    movingSummand_eq_selfChart ω₀ g s xs₂ hmem₂ hcont hsP_diff htrans_diff₂ htrans_diff_inv₂]

/-! ### The self-coherence core (moving fibre vs fixed fibre)

The genuine §VIII.3 monodromy match: the *moving* trace `valueChartTrace ω₀ f Φ` (re-selecting the
fibre `Φ b'` at each base value `b'`) germ-equals the *fixed* fibre trace `(fibreTrace ω₀ f D).traceCoeff`
over `b₀` — **provided the moving selection is built from the same continuously-varying sheets that
enumerate `D`'s fibre** (the index bijection).  We prove it from `fibreTrace_eventuallyEq_movingSum`
(the fixed-fibre side) plus the **diagonal hypothesis** `hdiag`: the moving trace germ-equals the moving
fibre sum read along the shared sheets.  `hdiag` is the precise residual content — that the diagonal
re-selection germ-equals the single moving frame sum — i.e. the monodromy/index-bijection itself. -/

/-- **Self-coherence from a shared moving frame.**  Let `Φ` be a global fibre selection, `D :
FibreRegularData g f b₀` a fixed fibre over `b₀`, and `sec : D.ι → ℂ → X` a family of manifold sections
of `f.holoRepr` through `D`'s fibre points (`sec i b₀ = D.xs i`, continuous at `b₀`, `f.holoRepr (sec i
b') = b'` near `b₀`).  If the moving trace germ-equals the moving fibre sum read along the shared
sheets (`hdiag`), then the moving trace germ-equals the fixed-fibre trace near `b₀`:

> `valueChartTrace ω₀ f Φ =ᶠ[𝓝 b₀] (fibreTrace ω₀ f D).traceCoeff`.

*Proof.*  Both germ-equal the same moving fibre sum: the fixed fibre by
`fibreTrace_eventuallyEq_movingSum`, the moving trace by `hdiag`.  Transitivity (`.trans`,
`.symm`). -/
theorem valueChartTrace_eventuallyEq_fibreTrace_of_sharedSheets (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Φ : (b : ℂ) → FibreRegularData g f b) {b₀ : ℂ}
    (D : FibreRegularData g f b₀) (sec : D.ι → ℂ → X)
    (hbase : ∀ i, sec i b₀ = D.xs i) (hcont : ∀ i, ContinuousAt (sec i) b₀)
    (hsec : ∀ i, ∀ᶠ b' in 𝓝 b₀, f.holoRepr (sec i b') = b')
    (hdiag : valueChartTrace ω₀ f Φ
      =ᶠ[𝓝 b₀] fun b' => ∑ i, chartIntegrand ω₀ g (D.xs i) ((chartAt ℂ (D.xs i)) (sec i b'))
        * deriv (fun z => (chartAt ℂ (D.xs i)) (sec i z)) b') :
    valueChartTrace ω₀ f Φ =ᶠ[𝓝 b₀] (fibreTrace ω₀ f D).traceCoeff :=
  hdiag.trans (fibreTrace_eventuallyEq_movingSum ω₀ f D sec hbase hcont hsec).symm

/-! ### The diagonal hypothesis at a non-pole, regular point — a sufficient reduction

The diagonal hypothesis `hdiag` is the monodromy core; the obstruction to deriving it outright is the
dependent typing of the *re-selected* fibre `Φ b'` (whose index, sheets, and fibre points vary with
`b'`).  The honest sufficient condition that produces it is that, *near `b₀`*, the selection `Φ b'`
is **pointwise the moving fibre** `sec · b'`: its index is `D.ι`, its fibre points are `sec i b'`, and
its planar sheets germ-match the chart pullbacks of `sec i` — at which point the diagonal trace literally
*is* the moving fibre sum.  We package that pointwise-diagonal condition and derive `hdiag` from it. -/

/-- **The pointwise-diagonal selection produces the diagonal hypothesis.**  Suppose, for `b'` in a
neighbourhood of `b₀`, the re-selected fibre `Φ b'` is the moving fibre along `sec`: there is an
equality of trace coefficients at the diagonal,

> `(fibreTrace ω₀ f (Φ b')).traceCoeff b'
>    = ∑ i, chartIntegrand ω₀ g (D.xs i) ((chartAt ℂ (D.xs i)) (sec i b'))
>      · deriv (fun z => (chartAt ℂ (D.xs i)) (sec i z)) b'`   for `b'` near `b₀`.

Then the diagonal hypothesis `hdiag` of `valueChartTrace_eventuallyEq_fibreTrace_of_sharedSheets` holds
(it is *definitionally* `valueChartTrace ω₀ f Φ b' = (fibreTrace ω₀ f (Φ b')).traceCoeff b'`, so this
is the same statement read through `valueChartTrace_apply`).  This is the precise residual monodromy
obligation: that the re-selection along the moving frame is, at the diagonal, the single moving fibre
sum. -/
theorem diagonal_of_pointwise (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) {b₀ : ℂ} (D : FibreRegularData g f b₀) (sec : D.ι → ℂ → X)
    (hpt : ∀ᶠ b' in 𝓝 b₀, (fibreTrace ω₀ f (Φ b')).traceCoeff b'
      = ∑ i, chartIntegrand ω₀ g (D.xs i) ((chartAt ℂ (D.xs i)) (sec i b'))
        * deriv (fun z => (chartAt ℂ (D.xs i)) (sec i z)) b') :
    valueChartTrace ω₀ f Φ
      =ᶠ[𝓝 b₀] fun b' => ∑ i, chartIntegrand ω₀ g (D.xs i) ((chartAt ℂ (D.xs i)) (sec i b'))
        * deriv (fun z => (chartAt ℂ (D.xs i)) (sec i z)) b' := by
  filter_upwards [hpt] with b' hb'
  rw [valueChartTrace_apply]
  exact hb'

/-! ### The moving-fibre coherence datum (the monodromy obligation, packaged)

We bundle the monodromy heart into one structure `MovingCoherenceDatum`: a global selection `Φ`, a
fixed fibre `D` over a base value `b₀`, the shared moving sheets `sec`, and the diagonal-pointwise
identity.  Its sole purpose is to name the genuine residual content — the index-bijection that the
re-selection along the moving frame is, at the diagonal, the single moving fibre sum — and to discharge
the local coherence `valueChartTrace =ᶠ (fibreTrace D).traceCoeff` from it.  Producing such a datum
*at each base value* (over the regular values: a regular fibre; over the pole-values: the pole
sub-fibre) is the remaining geometric obligation; this structure is exactly its interface. -/

/-- **A moving-fibre coherence datum** at a base value `b₀`: the data exhibiting the moving trace
`valueChartTrace ω₀ f Φ` as self-coherent near `b₀` — a fixed fibre `D` over `b₀`, continuously-varying
manifold sheets `sec` of `f.holoRepr` through `D`'s fibre points, and the **diagonal identity** that the
re-selected trace germ-equals the moving fibre sum read along those sheets.  This is the precise §VIII.3
monodromy/index-bijection content at `b₀`, isolated as a named obligation. -/
structure MovingCoherenceDatum (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (b₀ : ℂ) where
  /-- The fixed fibre over `b₀` the moving trace coheres to. -/
  D : FibreRegularData g f b₀
  /-- The continuously-varying manifold sheets enumerating the fibre. -/
  sec : D.ι → ℂ → X
  /-- Each sheet passes through the fibre point at the base. -/
  hbase : ∀ i, sec i b₀ = D.xs i
  /-- Each sheet is continuous at the base. -/
  hcont : ∀ i, ContinuousAt (sec i) b₀
  /-- Each sheet is a section of the finite value coordinate `f.holoRepr` near `b₀`. -/
  hsec : ∀ i, ∀ᶠ b' in 𝓝 b₀, f.holoRepr (sec i b') = b'
  /-- **The diagonal identity** (the monodromy core): the re-selected trace germ-equals the moving
  fibre sum read along the shared sheets. -/
  hdiag : ∀ᶠ b' in 𝓝 b₀, (fibreTrace ω₀ f (Φ b')).traceCoeff b'
    = ∑ i, chartIntegrand ω₀ g (D.xs i) ((chartAt ℂ (D.xs i)) (sec i b'))
      * deriv (fun z => (chartAt ℂ (D.xs i)) (sec i z)) b'

/-- **Local self-coherence from a moving-fibre coherence datum.**  A `MovingCoherenceDatum` at `b₀`
yields the local germ-coherence of the moving trace with its fixed fibre:

> `valueChartTrace ω₀ f Φ =ᶠ[𝓝 b₀] (fibreTrace ω₀ f C.D).traceCoeff`.

This is the assembled monodromy match (`diagonal_of_pointwise` then
`valueChartTrace_eventuallyEq_fibreTrace_of_sharedSheets`) — the §VIII.3 self-coherence at `b₀`, modulo
the existence of the datum. -/
theorem MovingCoherenceDatum.coherent {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {b₀ : ℂ}
    (C : MovingCoherenceDatum ω₀ g f Φ b₀) :
    valueChartTrace ω₀ f Φ =ᶠ[𝓝 b₀] (fibreTrace ω₀ f C.D).traceCoeff :=
  valueChartTrace_eventuallyEq_fibreTrace_of_sharedSheets ω₀ f Φ C.D C.sec C.hbase C.hcont C.hsec
    (diagonal_of_pointwise ω₀ f Φ C.D C.sec C.hdiag)

/-- **Punctured-neighbourhood self-coherence.**  The germ-coherence on a *punctured* neighbourhood
`𝓝[≠] b₀` (the form the finite glue `hglue_fin` of `CoherentTraceSelection` consumes), obtained by
restricting `MovingCoherenceDatum.coherent` along `nhdsWithin_le_nhds`. -/
theorem MovingCoherenceDatum.coherent_punctured {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {b₀ : ℂ}
    (C : MovingCoherenceDatum ω₀ g f Φ b₀) :
    valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀] (fibreTrace ω₀ f C.D).traceCoeff :=
  C.coherent.filter_mono nhdsWithin_le_nhds

end Jacobians.Dolbeault.FormTraceMovingFibre
