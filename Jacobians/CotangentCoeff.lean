/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.TraceForm

/-!
# Cotangent-bundle coefficient continuity (the *local* coefficient is the right object)

A `HolomorphicOneForms X` is a `ContMDiffSection` of the cotangent hom-bundle
`x ↦ TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ`. To integrate a form along a path one needs control of
its coefficient. The naive "global coefficient" `x ↦ α.toFun x (1 : TangentSpace 𝓘(ℂ) x)`
is **discontinuous** in general: `1 : TangentSpace 𝓘(ℂ) x` is the `∂/∂z` of the *preferred
chart at `x`*, and since the chart varies with `x` and chart transitions are general
biholomorphisms (derivatives ≠ 1), the constant-`1` tangent section is not continuous (it is
continuous iff the tangent bundle is trivialized by the atlas, i.e. parallelizable — false for
genus ≥ 2). Pairing it with a form nonzero at a point gives a discontinuous map. The
obstruction is isolated below (`const_one_section_continuous_of_coordChange_fixes_one`,
`target_eq_inCoordinates_of_w`).

The **correct, provable** object is the coefficient read in a *fixed* chart/trivialization
(`continuousAt_inCoordinates`, `continuousAt_localCoeff`). This is the tool a chart-patchwork
needs to integrate `α.toFun (γ s) (pathSpeed γ s)` along a (chart-pointwise-differentiable)
path: on a segment where `γ` stays in one chart, the integrand is the (continuous, bounded)
fixed-chart coefficient times the (integrable) fixed-chart velocity. It is also the
continuity input that `traceForm_comp` needs.

Derived via `contMDiffAt_hom_bundle` (Mathlib): the section's smoothness gives that its
`ContinuousLinearMap.inCoordinates` representation is continuous *into the fixed normed space*
`ℂ →L[ℂ] ℂ`. (Found 2026-05-30; corrects the earlier false "global coefficient" target.)
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology
open Filter Set

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The continuous local object.** Near `x₀`, the coordinate of the section `α` in the FIXED
hom-bundle trivialization at `x₀` is continuous (indeed it is `ContMDiffAt`) as a map into the
fixed normed space `ℂ →L[ℂ] ℂ`. This is `inCoordinates (α x)`. -/
theorem continuousAt_inCoordinates (α : HolomorphicOneForms X) (x₀ : X) :
    ContinuousAt (fun x : X => ContinuousLinearMap.inCoordinates ℂ
      (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ) x₀ x x₀ x (α.toFun x)) x₀ := by
  have hα := α.contMDiff_toFun x₀
  rw [contMDiffAt_hom_bundle] at hα
  exact hα.2.continuousAt

/-- **The local coefficient is continuous.** `x ↦ inCoordinates (α x) 1` (the coefficient of
`α` read in the FIXED chart at `x₀`, i.e. `α` paired with the *coordinate vector field of the
chart at `x₀`*) is continuous at `x₀`. NOTE this is `inCoordinates (α x) 1`, **not** the
discontinuous `α x 1`. -/
theorem continuousAt_localCoeff (α : HolomorphicOneForms X) (x₀ : X) :
    ContinuousAt (fun x : X => ContinuousLinearMap.inCoordinates ℂ
      (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ) x₀ x x₀ x (α.toFun x) (1 : ℂ)) x₀ :=
  (continuousAt_inCoordinates α x₀).clm_apply continuousAt_const

/-- **The obstruction, isolated.** Continuity of the constant-`1` tangent section is implied by
(in fact equivalent to, via `FiberBundleCore.continuous_const_section`) the constant `1 : ℂ`
being invariant under EVERY chart-transition derivative, `coordChange i j x 1 = 1`. That
hypothesis is false for a complex 1-manifold with non-trivial tangent bundle (genus ≥ 2):
chart transitions are general biholomorphisms whose derivatives do not fix `1`. Hence the
constant-`1` section is discontinuous, and `x ↦ α x (1 : TangentSpace x)` is discontinuous. -/
theorem const_one_section_continuous_of_coordChange_fixes_one
    (h : ∀ (i j : atlas ℂ X) (x : X),
        x ∈ (tangentBundleCore 𝓘(ℂ) X).toFiberBundleCore.baseSet i ∩
            (tangentBundleCore 𝓘(ℂ) X).toFiberBundleCore.baseSet j →
        (tangentBundleCore 𝓘(ℂ) X).toFiberBundleCore.coordChange i j x 1 = 1) :
    Continuous (fun x : X => (Bundle.TotalSpace.mk' ℂ
        (E := fun (x : X) => TangentSpace 𝓘(ℂ) x) x ((1 : ℂ) : TangentSpace 𝓘(ℂ) x))) :=
  (tangentBundleCore 𝓘(ℂ) X).toFiberBundleCore.continuous_const_section 1 h

/-- **Why the global target differs from the continuous local coefficient.** Near `x₀`,
`α x (1 : TangentSpace x)` equals `inCoordinates (α x)` applied to the input
`continuousLinearMapAt (triv x₀) x 1`. The operator `inCoordinates (α x)` is continuous
(`continuousAt_inCoordinates`), but the INPUT is the constant-`1` tangent-section coordinate,
which is discontinuous (see the obstruction). So the global target is a continuous operator
times a discontinuous input — discontinuous. -/
theorem target_eq_inCoordinates_of_w (α : HolomorphicOneForms X) (x₀ x : X)
    (hx : x ∈ (chartAt ℂ x₀).source) :
    α.toFun x ((1 : ℂ) : TangentSpace 𝓘(ℂ) x) =
      ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ)
        x₀ x x₀ x (α.toFun x)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).continuousLinearMapAt ℂ x (1 : ℂ)) := by
  have hxbase : x ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hxbase]

end Jacobians
