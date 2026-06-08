/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceBundleBranchBound
import Jacobians.Dolbeault.FormTraceSheetFibreBridge
import Jacobians.Dolbeault.FormTraceCoherentSelection

/-!
# The bundle-trace germ bridge `hbridgeBr` (Gate A close, Miranda §VIII.3)

This file discharges the **single core analytic input** of `patchedTraceSelection_ofBundleBranch`
(`Jacobians.Dolbeault.FormTraceBundleBranchBound`): the **bundle-trace germ bridge**

> `hbridgeBr` — at a regular-near-branch value `b₀`, `valueChartTrace ω₀ f Φ` germ-equals, on the
> punctured neighbourhood `𝓝[≠] b₀`, the value-chart local coefficient of the bundle trace SUM
> `traceLocalCoeff (traceFun F (αBr b₀)) (coe b₀) (coe z)`, where `αBr b₀ = ω₀·g` near the fibre.

This is the planar↔bundle identification at *regular* values `z` near `b₀`, term-by-term over the
finite regular fibre — the §VIII.3 "the trace is single-valued by symmetry".  The proof reduces to
the proven per-sheet linchpin `FormTraceSheet.g_weighted_sheetPullback_eq_chartIntegrand_mul_deriv`
and the bundle additivity `TraceForm.traceLocalCoeff_traceFun_eq_finsum`.

## The clean affine-chart reading (the key simplification — no base monodromy)

On `RiemannSphere = OnePoint ℂ` every finite chart is the single global affine chart `chartCoe`
(`RiemannSphere.chartAt_coe`, definitionally).  Hence the tangent trivializations at `coe b₀` and
`coe z` are *the same trivialization* (`trivializationAt … x` depends on `x` only through
`chartAt H x`, which is `chartCoe` for every finite point).  Therefore the fixed-`coe b₀`-frame local
coefficient `traceLocalCoeff (…) (coe b₀) (coe z)` equals the *self-frame* local coefficient
`traceLocalCoeff (…) (coe z) (coe z)` — **no genuine frame transition on the base**.  This is the
sphere-specific dissolution of the base monodromy: the only nontrivial transition is per-sheet on the
*total* space (handled by the proven `localRep_eq_transition_mul_self` inside the per-sheet bridge),
never on the sphere base.

The self-frame coefficient `traceLocalCoeff (traceFun F α) (coe z) (coe z)` is, by
`traceLocalCoeff_traceFun_eq_finsum` + `traceSummand_inCoordinates_apply_one_eq_ref`, exactly the
planar fibre-sum `∑ chartIntegrand·deriv` — the same object `valueChartTrace` is built from.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3, pp. 252–253 (the trace is single-valued
  by symmetry; the SUM extends across branch points; Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §10, §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open OnePoint

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.RiemannSphere
  Jacobians.Dolbeault.FormTraceMovingFibre

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The sphere base-frame swap (the key simplification)

On `RiemannSphere` the tangent trivialization at any finite point `coe b₀` agrees with the one at
`coe z`, because both are built from the single global chart `chartCoe`.  Hence the local coefficient
read in the *fixed* `coe b₀`-frame equals the one read in the *self* `coe z`-frame. -/

/-- **Sphere finite-base trivialization agreement.**  The tangent-bundle trivializations at two finite
points `coe a` and `coe b` of `RiemannSphere` are equal (both are the trivialization built from the
single global affine chart `chartCoe = chartAt ℂ (coe ·)`). -/
theorem trivializationAt_coe_eq (a b : ℂ) :
    trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := RiemannSphere)) ((a : ℂ) : RiemannSphere)
      = trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := RiemannSphere)) ((b : ℂ) : RiemannSphere) :=
  rfl

/-- **Sphere base-frame swap for `localCoeffLin`.**  On `RiemannSphere`, the local-coefficient
functional read in the *fixed* `coe a`-frame equals the one read in the *self* `coe b`-frame, for any
covector `φ` at `coe b`: the two trivializations coincide (`trivializationAt_coe_eq`).  This dissolves
the base "monodromy" — there is no genuine frame transition on the sphere base. -/
theorem localCoeffLin_coe_base_swap (a b : ℂ) (φ : ℂ →L[ℂ] ℂ) :
    localCoeffLin (((a : ℂ) : RiemannSphere)) (((b : ℂ) : RiemannSphere)) φ
      = localCoeffLin (((b : ℂ) : RiemannSphere)) (((b : ℂ) : RiemannSphere)) φ :=
  rfl

end Jacobians.Dolbeault.FormTraceGlobal
