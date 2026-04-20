import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Montel path to finite-dimensionality of `HolomorphicOneForms`

**Goal**: prove `FiniteDimensional ℂ (HolomorphicOneForms X)` for X a
compact connected complex 1-manifold via the classical Montel /
compactness route.

See `docs/MONTEL_PATH.md` for the overall plan.

## Strategy

1. Assign a sup-norm to smooth sections (via bundle trivializations +
   compactness of base).
2. Show holomorphic sections form a closed subspace (preserved under
   uniform limits).
3. Cauchy estimates on charts give equicontinuity of bounded
   holomorphic section families.
4. Arzelà–Ascoli ⇒ bounded closed sets in the sup-norm are compact.
5. Riesz ⇒ the space is finite-dimensional.

This file provides the skeleton — concrete machinery is built up
incrementally.

## Current status

Step 1 (norm on `ContMDiffSection` via a finite atlas): **in progress**.

Key technical hurdle identified: `TangentSpace 𝓘(ℂ) x` does not carry
a `NormedAddCommGroup` instance by default (deliberately, to avoid
incorrect instance resolution — see the comment in
`Mathlib.Geometry.Manifold.IsManifold.Basic` near the `TangentSpace`
definition). The concrete norm on `HolomorphicOneForms X` will be
constructed via a specific trivialization choice of the cotangent
bundle over a finite atlas, producing a chart-local representative as
a holomorphic `ℂ → ℂ` function whose sup gives the section norm.

## Roadmap (ordered sub-tasks)

- [x] `docs/MONTEL_PATH.md` — decision + plan recorded.
- [ ] `Bundle.holoChartNorm` — in a fixed chart, norm of a bundle
      section as sup of the chart-local holomorphic function.
- [ ] `HolomorphicOneForms.norm_def` — max over a finite atlas of
      chart-local norms.
- [ ] `NormedAddCommGroup (HolomorphicOneForms X)` instance (compact X).
- [ ] `NormedSpace ℂ (HolomorphicOneForms X)`.
- [ ] `Cauchy` — derivative bound on chart-local representatives via
      uniform norm + disc-distance.
- [ ] `Equicontinuous` — a norm-bounded family of holomorphic sections
      is equicontinuous (in some chart metric).
- [ ] Adapt Arzelà–Ascoli from `Mathlib.Topology.UniformSpace.Ascoli`.
- [ ] Conclude `IsCompact (closedBall 0 1)` in `HOF X`.
- [ ] Apply `FiniteDimensional.of_isCompact_closedBall₀`.
-/

namespace Jacobians.Montel

open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Step 1a: evaluate a cotangent section at a tangent vector

The cotangent section `α x : TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ` can be applied
to any tangent vector. Since `TangentSpace 𝓘(ℂ, ℂ) x` is definitionally
`ℂ`, we can use `1 : ℂ` (via `NormedSpace.fromTangentSpace`) as a
canonical "unit tangent" at x — not canonical in a chart-independent
sense, but concrete enough to define a scalar `ℂ`-valued function on X.

Mathematically: this is the local coordinate `a(z)` when the 1-form is
written as `α = a(z) dz` in a chart. -/

/-- The model-space "unit tangent" vector at x. Since
`TangentSpace 𝓘(ℂ, ℂ) x` is definitionally `ℂ`, we can use `1 : ℂ`
directly. -/
def tangentOne {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) : TangentSpace 𝓘(ℂ, ℂ) (M := X) x :=
  (1 : ℂ)

/-- The scalar "local value" of a holomorphic 1-form at x, obtained by
applying α to the model-space unit tangent vector. -/
noncomputable def HolomorphicOneForms.eval
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x : X) : ℂ :=
  α.toFun x (tangentOne x)

/-! ### Step 1b: continuity of `HolomorphicOneForms.eval`

The function `α.eval : X → ℂ` is continuous. Proof: `α.toFun` is
`ContMDiff` hence continuous as a bundle section; applying it to the
(chart-local) unit tangent vector gives a continuous scalar function.

This is the `ContMDiff.clm_apply_of_inCoordinates` pattern adapted to
our cotangent-bundle setup. -/
theorem HolomorphicOneForms.eval_continuous
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) :
    Continuous (HolomorphicOneForms.eval α) := by
  -- α.contMDiff_toFun says α as a map X → TotalSpace is ContMDiff.
  -- We unfold via contMDiffAt_hom_bundle to get the in-coordinates rep.
  -- Since the bundle is trivialized by charts (cotangent = Hom(TX, ℂ)),
  -- the value in chart coordinates is a holomorphic function, hence
  -- continuous. Gluing over a finite atlas gives global continuity.
  have hα : ContMDiff 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun x : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) x (α.toFun x)) := α.contMDiff_toFun
  -- TODO(Montel-step1): extract pointwise continuity of `α.eval`.
  -- Strategy: in-coordinates representation of α (via
  -- `contMDiffAt_hom_bundle` iff) is a smooth `ℂ → ℂ →L[ℂ] ℂ` function;
  -- compose with evaluation at 1 to get α.eval in coordinates, which is
  -- smooth. Patch via atlas cover.
  sorry

/-! ### Step 1c: the sup-norm `‖α‖`

By compactness of X + continuity of `α.eval`, `sSup (Set.range (‖α.eval ·‖))`
is finite. This is the norm we will put on `HolomorphicOneForms X`. -/
noncomputable def HolomorphicOneForms.supNorm
    {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) : ℝ :=
  sSup (Set.range (fun x : X => ‖HolomorphicOneForms.eval α x‖))

-- TODO: supNorm_nonneg, supNorm_eq_zero_iff, supNorm_add, supNorm_smul
-- to upgrade to a full NormedAddCommGroup / NormedSpace ℂ instance.

end Jacobians.Montel
