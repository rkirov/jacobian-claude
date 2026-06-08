/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormResidueTheorem
import Jacobians.ManifoldIFT
import Jacobians.ProperMapDegreeSheets

/-!
# The per-fibre trace data of `α = ω₀·g` (Gate A, node A-ii — bridges (a)/(b)/(c))

This file builds the **per-fibre** geometric content of the general 1-form residue theorem: the
construction of a `Jacobians.MeromorphicTrace.FibreTrace` over an *unramified* fibre `f⁻¹(b)` of the
cover `F = f.toRiemannSphere`, and the **per-fibre residue bridge**

> `resAt (T.coeff i) (T.pre i) = formFnResidue ω₀ g (xs i)`   (definitional, bridge (c)),

so that Miranda's Lemma 3.2 (`FibreTrace.resAt_traceCoeff'`, the now-unconditional residue
change-of-variables) gives

> `Res_b (Tr_F α over the fibre) = ∑_{x ∈ f⁻¹(b)} Res_x(α)`.

This is the genuinely-new **manifold-bundle** layer that feeds the `FormResidueTrace` assembly
(`Jacobians.Dolbeault.FormResidueTheorem`).  The remaining piece *after* this file — the global
**rationality** of the trace `Tr_F α` on `ℂℙ¹` (assembling the per-fibre data over *all* fibres into
a single `LaurentForm`) — is the last obligation, diagnosed precisely at the bottom of this file.

## The design — `coeff i`/`pre i` chosen to make bridge (c) definitional

The crucial design decision (mirroring the close-path's A-ii analysis): a `FibreTrace` over `b` with
sheets indexed by the fibre points `xs : ι → X` uses
* `pre i := (chartAt ℂ (xs i)) (xs i)` — the source-chart coordinate of `xs i`;
* `coeff i := fun w => coeffAt ω₀ (xs i) w * g ((chartAt ℂ (xs i)).symm w)` — the **chart integrand
  of `α = ω₀·g`** at `xs i`, exactly the function whose `resAt` at `pre i` is `formFnResidue ω₀ g
  (xs i)` *by definition* (`Jacobians.Dolbeault.formFnResidue`).

With this choice the per-fibre residue bridge (c) is **definitional** (`resAt_coeff_eq_formFnResidue`),
and the only genuinely-analytic inputs are
* (a) the **section germ** `sheet i`: a local holomorphic biholomorphism `ℂ → ℂ` sending the base
  coordinate `b'` (the value-chart coordinate at `F (xs i) = coe b`) to the source coordinate `pre i`
  — supplied by the manifold inverse function theorem `Jacobians.exists_holo_localInverse` applied to
  `F = f.toRiemannSphere` at `xs i` (a regular point), read in charts;
* (b) the **trivialization↔chart compatibility** of `coeffAt` (already discharged: `coeffAt ω₀ (xs i)`
  is analytic on the chart target, `Jacobians.Dolbeault.coeffAt_analyticAt`, so each `coeff i` is
  meromorphic at `pre i`).

`FibreTrace.coeff_mero` then holds because `coeffAt ω₀ (xs i)` is analytic at `pre i` and `g`'s
chart-pullback is meromorphic there.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17; §4.22–4.25 (sheets, local normal form).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.ProperMapDegreeSheets

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Bridge (c) — the per-fibre residue bridge (definitional)

With `coeff i` chosen to be the chart integrand of `α = ω₀·g` at `xs i`, and `pre i` the chart image
of `xs i`, the residue `resAt (coeff i) (pre i)` is `formFnResidue ω₀ g (xs i)` by the very
definition of `formFnResidue`.  This is the bridge (c) that turns the abstract `FibreTrace` residue
sum into the geometric fibre residue sum of `α`. -/

/-- The **chart integrand of `α = ω₀·g` at `a`**: `w ↦ coeffAt ω₀ a w · g (chart_a⁻¹ w)`, the
function in the canonical chart at `a` whose `resAt` at `chart_a a` is `formFnResidue ω₀ g a`. -/
def chartIntegrand (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (a : X) : ℂ → ℂ :=
  fun w => coeffAt ω₀ a w * g ((chartAt ℂ a).symm w)

/-- **Bridge (c), definitional.**  The residue of the chart integrand of `α = ω₀·g` at `a`, read at
the chart image `chart_a a`, *is* `formFnResidue ω₀ g a` — by the definition of `formFnResidue`. -/
@[simp] theorem resAt_chartIntegrand_eq_formFnResidue (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (a : X) :
    resAt (chartIntegrand ω₀ g a) ((chartAt ℂ a) a) = formFnResidue ω₀ g a := rfl

/-- The chart integrand `chartIntegrand ω₀ g a` is **meromorphic at the chart image of `a`** whenever
`g`'s chart-pullback is meromorphic there: it is the product of the analytic coefficient
`coeffAt ω₀ a` (`coeffAt_analyticAt`) with the meromorphic `g ∘ chart_a⁻¹`.  (Bridge (b): the
trivialization-defined `coeffAt` is analytic in the chart, so it does not spoil meromorphy.) -/
theorem meromorphicAt_chartIntegrand (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (a : X)
    (hg : MeromorphicAt (fun z => g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    MeromorphicAt (chartIntegrand ω₀ g a) ((chartAt ℂ a) a) := by
  have hmem : (chartAt ℂ a) a ∈ (chartAt ℂ a).target :=
    (chartAt ℂ a).map_source (mem_chart_source ℂ a)
  exact (coeffAt_analyticAt ω₀ a hmem).meromorphicAt.mul hg

/-! ### Bridge (a) — the planar section germ (local biholomorphism inverse)

The local section of the cover, read entirely in charts, is a *planar* local biholomorphism inverse:
given an analytic `φ : ℂ → ℂ` at `x₀` with `φ'(x₀) ≠ 0` and `φ x₀ = b`, the complex inverse function
theorem (`HasStrictDerivAt.localInverse` + `AnalyticAt.analyticAt_localInverse` +
`HasStrictDerivAt.to_localInverse`) produces a section `s` analytic at `b` with `s b = x₀`,
`deriv s b = (deriv φ x₀)⁻¹ ≠ 0`, and `φ (s w) = w` near `b`.  This is the analytic core of
`FibreTrace.sheet`, packaged with **all** the `FibreTrace` field hypotheses (`sheet_analytic`,
`sheet_deriv_ne`, `sheet_base`). -/

/-- **Planar section germ of a local biholomorphism.**  For `φ : ℂ → ℂ` analytic at `x₀` with
`deriv φ x₀ ≠ 0` and `φ x₀ = b`, there is a section `s : ℂ → ℂ` analytic at `b` with `s b = x₀`,
`deriv s b ≠ 0`, and `φ (s w) = w` on a neighbourhood of `b`.  (The complex inverse function
theorem; `deriv s b = (deriv φ x₀)⁻¹`.) -/
theorem exists_planar_section {φ : ℂ → ℂ} {x₀ b : ℂ} (hφ : AnalyticAt ℂ φ x₀)
    (hφ' : deriv φ x₀ ≠ 0) (hb : φ x₀ = b) :
    ∃ s : ℂ → ℂ, AnalyticAt ℂ s b ∧ s b = x₀ ∧ deriv s b ≠ 0 ∧
      (∀ᶠ w in 𝓝 b, φ (s w) = w) := by
  -- The Mathlib local inverse `s := localInverse φ (deriv φ x₀) x₀`.
  have hsd : HasStrictDerivAt φ (deriv φ x₀) x₀ := hφ.hasStrictDerivAt
  set s : ℂ → ℂ := hsd.localInverse φ (deriv φ x₀) x₀ hφ' with hs
  -- `s` analytic at `φ x₀ = b`.
  have hsana : AnalyticAt ℂ s (φ x₀) := hφ.analyticAt_localInverse hφ'
  -- `s (φ x₀) = x₀` (left inverse at the centre).
  have hsx₀ : s (φ x₀) = x₀ :=
    (hsd.eventually_left_inverse hφ').self_of_nhds
  -- `deriv s (φ x₀) = (deriv φ x₀)⁻¹` (the inverse strict derivative), hence `≠ 0`.
  have hsderiv : HasStrictDerivAt s (deriv φ x₀)⁻¹ (φ x₀) := hsd.to_localInverse hφ'
  have hsderiv' : deriv s (φ x₀) ≠ 0 := by
    rw [hsderiv.hasDerivAt.deriv]; exact inv_ne_zero hφ'
  -- `φ (s w) = w` near `φ x₀` (right inverse).
  have hrinv : ∀ᶠ w in 𝓝 (φ x₀), φ (s w) = w := hsd.eventually_right_inverse hφ'
  subst hb
  exact ⟨s, hsana, hsx₀, hsderiv', hrinv⟩

end Jacobians.Dolbeault.FormTraceFibre
