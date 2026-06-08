/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceBranchExtension

/-!
# Reducing branch-value continuity to limit existence + value-matching (Gate A, §VIII.3)

The capstone `BranchAwareTraceSelection` (`FormTraceBranchAwareSelection`) reduces Gate A's
`∑Res = 0` to, among other fields, the **branch-value continuity**

> `hbranch : ∀ z ∈ br, z ∉ centres → ContinuousAt (valueChartTrace ω₀ f Φ) z`,

the §VIII.3 single-valuedness/boundedness input for the removable-singularity extension across the
finitely-many branch values.

This file isolates *exactly* what `hbranch` demands, splitting it into the two genuine analytic
sub-obligations and recording the **structural subtlety** that distinguishes the meromorphic trace
`valueChartTrace ω₀ f Φ` from a freely-extendable function.

## The structural subtlety (the honest content of `hbranch`)

`valueChartTrace ω₀ f Φ z := (fibreTrace ω₀ f (Φ z)).traceCoeff z` is, at *every* value `z` — branch
values included — the **finite fibre-sum**
`∑ i, (chartIntegrand ω₀ g (Φ z).xs i)(sheetᵢ z) · sheetᵢ'(z)` over the fibre data `Φ z`, whose sheets
are *unramified* holomorphic sections (`FibreRegularData.hg_deriv ≠ 0`).  Continuity at a branch value
`z` therefore requires **two** things simultaneously:

1. **the punctured limit exists** — `valueChartTrace ω₀ f Φ` tends to some `L` as `w → z` (`w ≠ z`); this
   is the genuine §VIII.3 boundedness (the symmetric functions of the colliding sheets stay bounded;
   the roots-of-unity cancellation of the `wᵉ`-normal-form blow-up — the *proven*
   `Jacobians.traceLocalCoeff_mul_sub_tendsto_zero` technique for holomorphic forms); **and**

2. **the value at `z` matches the limit** — `valueChartTrace ω₀ f Φ z = L`, i.e. the fibre data `Φ z`
   chosen *at* the branch value reproduces the limiting trace value.

Sub-obligation (2) is the structural subtlety: because `Φ z` may only enumerate **unramified** fibre
points (`hg_deriv ≠ 0`), if the fibre over `z` contains a genuinely ramified point then the naive
"canonical fibre" choice (the unramified preimages of `z`) gives a *partial* sum that misses the
ramified points' nonzero contribution to `L`.  The branch-value `Φ z` must instead be chosen so its
fibre-sum equals `L` — the trace's *removable-extension value*, not a literal sub-fibre sum.  This is
the precise reason a real-cover `BranchAwareTraceSelection` cannot take `Φ` to be the canonical fibre at
branch values unmodified; it must carry the extension value there.

This file makes both sub-obligations explicit, so a global-`Φ` builder discharges `hbranch` by supplying
(1) the limit (via the proven boundedness technique) and (2) a branch-value fibre datum realising it.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `continuousAt_valueChartTrace_of_tendsto` — `hbranch` at `z` from a punctured limit `L`
  (`Tendsto … (𝓝[≠] z) (𝓝 L)`) together with the value-matching `valueChartTrace ω₀ f Φ z = L`.
* `continuousAt_valueChartTrace_of_tendsto_self` — the special case where the value already equals the
  limit phrased via `Tendsto … (𝓝[≠] z) (𝓝 (valueChartTrace ω₀ f Φ z))`.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr` extends across branch
  points; Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22–4.25 (local normal form `wᵉ`), §10 (the
  trace).  The boundedness technique is `Jacobians.traceLocalCoeff_mul_sub_tendsto_zero`
  (`Jacobians/TraceForm.lean`, proven axiom-clean for holomorphic forms).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}

/-! ### Branch-value continuity from a punctured limit + value-matching

`ContinuousAt h z` for any `h : ℂ → ℂ` is exactly `Tendsto h (𝓝 z) (𝓝 (h z))`.  Splitting `𝓝 z` into
the point `z` and the punctured filter `𝓝[≠] z` (`nhds_eq_nhdsWithin_sup_pure` style), continuity at `z`
follows from the punctured limit being `h z`.  We package this for `valueChartTrace`: a punctured limit
`L` plus value-matching `valueChartTrace … z = L` gives `hbranch` at `z`. -/

/-- **Branch-value continuity from a punctured limit + value-matching.**  If `valueChartTrace ω₀ f Φ`
tends to `L` along the punctured neighbourhood filter `𝓝[≠] z` (the §VIII.3 boundedness: the limiting
trace value exists) and the value at `z` matches the limit (`valueChartTrace ω₀ f Φ z = L`, the
branch-value fibre datum `Φ z` realising the extension value), then `valueChartTrace ω₀ f Φ` is
**continuous at `z`** — exactly the `hbranch` input of `BranchAwareTraceSelection`.

The proof reconstitutes `𝓝 z` from its punctured part and the point `z`: the punctured limit gives the
limit `L = valueChartTrace … z` on `𝓝[≠] z`, and the value at `z` is `L` by `hval`, so the full
`𝓝 z`-limit is `valueChartTrace … z`, i.e. `ContinuousAt`. -/
theorem continuousAt_valueChartTrace_of_tendsto
    (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) {z L : ℂ}
    (hlim : Tendsto (valueChartTrace ω₀ f Φ) (𝓝[≠] z) (𝓝 L))
    (hval : valueChartTrace ω₀ f Φ z = L) :
    ContinuousAt (valueChartTrace ω₀ f Φ) z := by
  -- `ContinuousAt h z ↔ Tendsto h (𝓝 z) (𝓝 (h z))`.  Rewrite the target value via `hval`.
  rw [ContinuousAt, hval]
  -- `𝓝 z = 𝓝[≠] z ⊔ pure z`; the punctured part tends to `L` (`hlim`), the pure part to `h z = L`.
  rw [← nhdsNE_sup_pure z, tendsto_sup]
  refine ⟨hlim, ?_⟩
  -- The `pure z` part: `Tendsto h (pure z) (𝓝 L)` reduces to `h z = L` (via `tendsto_pure_left`).
  rw [tendsto_pure_left]
  intro s hs
  rw [hval]
  exact mem_of_mem_nhds hs

/-- **Branch-value continuity from a self-matching punctured limit.**  The packaging where the limit is
phrased directly as the value at `z`: if `valueChartTrace ω₀ f Φ` tends to `valueChartTrace ω₀ f Φ z`
along `𝓝[≠] z`, it is continuous at `z`.  (Special case `L := valueChartTrace ω₀ f Φ z` of
`continuousAt_valueChartTrace_of_tendsto`.) -/
theorem continuousAt_valueChartTrace_of_tendsto_self
    (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) {z : ℂ}
    (hlim : Tendsto (valueChartTrace ω₀ f Φ) (𝓝[≠] z) (𝓝 (valueChartTrace ω₀ f Φ z))) :
    ContinuousAt (valueChartTrace ω₀ f Φ) z :=
  continuousAt_valueChartTrace_of_tendsto ω₀ f Φ hlim rfl

end Jacobians.Dolbeault.FormTraceGlobal
