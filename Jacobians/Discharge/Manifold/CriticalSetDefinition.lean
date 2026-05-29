/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.Discharge.Manifold.CriticalSetDiscrete
import Jacobians.Discharge.Manifold.MeromorphicExtension
import Jacobians.Discharge.Divisor.PrincipalDivisor

set_option autoImplicit true


/-! # Critical set and critical values of `MeromorphicNonzero.toRiemannSphere`

For `f : MeromorphicNonzero X` on a compact connected complex 1-manifold
`X`, the pole-extension `f̃ := f.toRiemannSphere : X → RiemannSphere = OnePoint ℂ`
is the natural map carrying the branched-cover structure. Its **critical set**
is the set of points where `f̃` fails to be a local biholomorphism — equivalently,
the points where some chart-pullback derivative vanishes. The **critical values**
are the `f̃`-images of those points.

Downstream (regular-value existence, branched-cover degree well-definedness),
finiteness of the critical values is the key input.

## What this file does

* Defines `MeromorphicNonzero.criticalSet f : Set X` as the set of points where
  `f̃` is **not locally injective** (the topological proxy for "not a local
  biholomorphism"; for a non-constant analytic map between complex 1-manifolds
  these coincide via the local branched-cover normal form).

* Defines `MeromorphicNonzero.criticalValues f : Set RiemannSphere` as
  `f.toRiemannSphere '' f.criticalSet`.

* Proves the **reduction** `criticalValues_finite_of_criticalSet_finite`:
  `f.criticalSet.Finite → f.criticalValues.Finite` (literally `Finite.image`).

* Proves `criticalSet_finite_of_witness`: given the chart-pullback witness
  package from `CriticalSetDiscrete` (ZZ44 — `CriticalChartPullbackData`
  per critical point + closedness) for `f̃`, we obtain `f.criticalSet.Finite`.

## Residual

The unconditional construction of the per-point `CriticalChartPullbackData`
witnesses for the *specific* function `f̃ = f.toRiemannSphere` is left to a
separate supplier chip: it requires (i) bridging `ContMDiff … ω` to
`AnalyticAt` for the chart pullback of `f̃` (already partly available via
`ContMDiffOmegaAnalytic`), (ii) showing the chart-pullback derivative is
not eventually zero (consequence of non-constancy), and (iii) closedness of
`criticalSet` in `X`. The present file ships the headline definitions and
the unconditional reduction `criticalSet_finite ⇒ criticalValues_finite`.

No `sorry`. No `axiom`. -/

@[expose] public section

noncomputable section

open Set OnePoint
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge

namespace MeromorphicNonzero

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- **Critical set of the pole extension `f̃ = f.toRiemannSphere`.**

Defined as the set of points `x : X` where `f̃` is **not locally injective**:
no neighbourhood `U` of `x` satisfies `Set.InjOn f̃ U`. For a non-constant
analytic map between complex 1-manifolds, this coincides with the classical
notion of a critical point (a point where the chart-pullback derivative
vanishes), via the local branched-cover normal form `z ↦ z^k` with `k ≥ 2`. -/
def criticalSet (f : MeromorphicNonzero X) : Set X :=
  { x : X | ¬ ∃ U ∈ 𝓝 x, Set.InjOn f.toRiemannSphere U }

/-- **Critical values of the pole extension `f̃`.** The image of the critical
set under `f̃`. -/
def criticalValues (f : MeromorphicNonzero X) : Set RiemannSphere :=
  f.toRiemannSphere '' f.criticalSet

/-- **Unconditional reduction.** Finiteness of the critical values follows
from finiteness of the critical set via `Set.Finite.image`. -/
theorem criticalValues_finite_of_criticalSet_finite
    (f : MeromorphicNonzero X) (h : f.criticalSet.Finite) :
    f.criticalValues.Finite :=
  h.image _

/-- **Witness package for finiteness of the critical set.**

Bundles the data required by ZZ44's
`criticalSet_finite_of_chart_pullback`:

* `closed` — the critical set is closed in `X`,
* `chart_data` — at every critical point, a
  `CriticalChartPullbackData` witness for the map `f.toRiemannSphere`. -/
structure CriticalSetWitness (f : MeromorphicNonzero X) where
  closed : IsClosed f.criticalSet
  chart_data :
    ∀ x ∈ f.criticalSet,
      ContMDiff.Degree.CriticalChartPullbackData
        f.toRiemannSphere f.criticalSet x

/-- **Finiteness of the critical set, given the chart-pullback witness
package.** Direct application of ZZ44's
`criticalSet_finite_of_chart_pullback`. -/
theorem criticalSet_finite_of_witness
    (f : MeromorphicNonzero X) (w : CriticalSetWitness f) :
    f.criticalSet.Finite :=
  ContMDiff.Degree.criticalSet_finite_of_chart_pullback
    f.toRiemannSphere f.criticalSet w.closed w.chart_data

/-- **Finiteness of the critical values, given the chart-pullback witness
package.** Composes `criticalSet_finite_of_witness` with
`criticalValues_finite_of_criticalSet_finite`. -/
theorem criticalValues_finite_of_witness
    (f : MeromorphicNonzero X) (w : CriticalSetWitness f) :
    f.criticalValues.Finite :=
  criticalValues_finite_of_criticalSet_finite f
    (criticalSet_finite_of_witness f w)

end MeromorphicNonzero

end Jacobians.Discharge

end

end
