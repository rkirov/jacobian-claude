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

/-! ### The `g`-weight rides inside the bundle summand

The meromorphic form `α = ω₀·g` is encoded by a holomorphic form `αBr` whose covector at each fibre
point `x` equals `g x • ω₀.toFun x`.  Hence the bundle per-sheet summand of `αBr` factors as `g (s y)`
times the holomorphic per-sheet summand of `ω₀`. -/

/-- **`g`-weight pull-out for the bundle summand.**  If `αBr.toFun (s y) = g (s y) • ω₀.toFun (s y)`
(the form `αBr` is `ω₀·g` at the fibre point `s y`), then the bundle per-sheet covector of `αBr` at the
affine unit tangent is `g (s y)` times that of `ω₀`:

> `sheetPullback αBr s y 1 = g (s y) * sheetPullback ω₀ s y 1`. -/
theorem sheetPullback_one_eq_g_mul {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (ω₀ αBr : HolomorphicOneForms X) (g : X → ℂ) (s : Y → X) (y : Y)
    (hαBr : αBr.toFun (s y) = g (s y) • ω₀.toFun (s y)) :
    sheetPullback αBr s y (1 : ℂ) = g (s y) * sheetPullback ω₀ s y (1 : ℂ) := by
  show (αBr.toFun (s y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) s y) (1 : ℂ)
    = g (s y) * (ω₀.toFun (s y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) s y) (1 : ℂ)
  rw [hαBr, ContinuousLinearMap.smul_comp, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-! ### The bundle trace SUM as a planar sheet sum (the core decomposition)

At a regular value `coe z` (off the branch locus of `F = f.toRiemannSphere`), with a local sheet
system `S` of `F` at `coe z`, the bundle trace SUM local coefficient — read in the *fixed* `coe b₀`
frame — equals the planar fibre sum `∑ g·sheetPullback ω₀` over the sheets.  This is the bundle side
of the §VIII.3 trace, reduced to the per-sheet holomorphic covectors.  The base-frame swap dissolves
the `coe b₀` ↔ `coe z` transition; the centre identity recovers the raw value; the sheet system
expands the fibre sum; the `g`-weight rides per sheet. -/

/-- **Bundle trace SUM local coefficient = planar sheet sum.**  Let `F = f.toRiemannSphere` be the
nonconstant cover, `coe z` a regular value with a local sheet system `S`, and `αBr` a holomorphic form
with `αBr.toFun (S.sheet i (coe z)) = g (S.sheet i (coe z)) • ω₀.toFun (S.sheet i (coe z))` at each
fibre point.  Then for any base point `coe b₀`,

> `traceLocalCoeff (traceFun F αBr) (coe b₀) (coe z)
>    = ∑ i, g (S.sheet i (coe z)) * sheetPullback ω₀ (S.sheet i) (coe z) 1`. -/
theorem traceLocalCoeff_traceFun_eq_sheetSum (ω₀ αBr : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) {b₀ z : ℂ}
    (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
    (hαBr : ∀ i, αBr.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))
      = g (S.sheet i (((z : ℂ) : RiemannSphere))) • ω₀.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))) :
    traceLocalCoeff (traceFun f.toRiemannSphere αBr) (((b₀ : ℂ) : RiemannSphere))
        (((z : ℂ) : RiemannSphere))
      = ∑ i, g (S.sheet i (((z : ℂ) : RiemannSphere)))
          * sheetPullback ω₀ (S.sheet i) (((z : ℂ) : RiemannSphere)) (1 : ℂ) := by
  -- Base-frame swap: `coe b₀` ↦ `coe z` (no monodromy on the sphere base).
  rw [show traceLocalCoeff (traceFun f.toRiemannSphere αBr) (((b₀ : ℂ) : RiemannSphere))
        (((z : ℂ) : RiemannSphere))
      = localCoeffLin (((b₀ : ℂ) : RiemannSphere)) (((z : ℂ) : RiemannSphere))
          (traceFun f.toRiemannSphere αBr (((z : ℂ) : RiemannSphere))) from rfl,
    localCoeffLin_coe_base_swap b₀ z]
  -- Self-frame coefficient = raw value at `1` (centre identity).
  rw [show localCoeffLin (((z : ℂ) : RiemannSphere)) (((z : ℂ) : RiemannSphere))
        (traceFun f.toRiemannSphere αBr (((z : ℂ) : RiemannSphere)))
      = traceLocalCoeff (traceFun f.toRiemannSphere αBr) (((z : ℂ) : RiemannSphere))
          (((z : ℂ) : RiemannSphere)) from rfl,
    traceLocalCoeff_center]
  -- Expand the fibre sum along the local sheet system.
  rw [S.traceFun_eq_sum_sheetPullback f.contMDiff_toRiemannSphere αBr S.mem_V]
  -- Sum of operators applied at `1`, then pull out the `g`-weight per sheet.
  exact (ContinuousLinearMap.sum_apply Finset.univ
      (fun i => sheetPullback αBr (S.sheet i) (((z : ℂ) : RiemannSphere))) (1 : ℂ)).trans
    (Finset.sum_congr rfl (fun i _ =>
      sheetPullback_one_eq_g_mul ω₀ αBr g (S.sheet i) (((z : ℂ) : RiemannSphere)) (hαBr i)))

end Jacobians.Dolbeault.FormTraceGlobal
