import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact

/-!
# Montel path to finite-dimensionality of `HolomorphicOneForms`

**Goal**: prove `FiniteDimensional ℂ (HolomorphicOneForms X)` for X a
compact connected complex 1-manifold via the classical Montel /
compactness route (Ahlfors–Sario, Rudin).

See `docs/MONTEL_PATH.md` for the overall plan.

## Classical textbook approach (Ahlfors–Sario Ch II §5)

1. **Finite atlas.** X compact ⇒ finite open cover by chart domains
   `{U_1, ..., U_n}` with charts `φ_j : U_j → V_j ⊆ ℂ`.
2. **Local representative.** In chart `(U_j, φ_j)`, a holomorphic
   1-form α restricts to `α_j = f_j(z) dz` where `f_j : V_j → ℂ` is
   holomorphic. On overlaps, `f_j = f_k · (∂φ_k/∂φ_j)` (chain rule).
3. **Sup-norm.** `‖α‖ := max_j sup_{z ∈ K_j} |f_j(z)|` where
   `K_j ⊂ V_j` is a compact sub-set chosen such that
   `⋃ φ_j⁻¹(K_j) = X`. (Refine atlas if needed.)
4. **Cauchy estimates.** For `K_j ⊂ K'_j ⊂ V_j` with
   `d = dist(K_j, ∂K'_j) > 0`, Cauchy's integral formula gives
   `|f_j'(z)| ≤ |f_j|_{∞, K'_j} / d` for z ∈ K_j. Hence a family
   `{f_j}` bounded in sup-norm on K'_j is equicontinuous on K_j.
5. **Arzelà–Ascoli.** Bounded + equicontinuous ⇒ compact in `C(K_j, ℂ)`.
   Iterating over the finite atlas: bounded sets in HOF X are compact
   in the sup-norm topology.
6. **Riesz.** Compact closed ball ⇒ `HOF X` is finite-dimensional.

## This file: step 1 — norm on HOF X via chart trivializations

Given the structural issues with the earlier `tangentOne`-based
approach (not a smooth global section), we use the textbook
chart-atlas approach directly.

**Key building block**: `Bundle.ContinuousLinearMap`'s trivialization at
a point gives a local `(fiber) → (ℂ →L[ℂ] ℂ)` representation.

**Status**: machinery setup. The actual norm + its properties are
deferred to incremental sub-tasks, each tracked below.
-/

namespace Jacobians.Montel

open scoped Manifold ContDiff
open Bundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Finite chart cover

For compact X with `ChartedSpace ℂ X`, the chart sources form an open
cover, and compactness gives a finite subcover. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- The chart source at x is open in X. -/
theorem isOpen_chartAt_source (x : X) : IsOpen (chartAt ℂ x).source :=
  (chartAt ℂ x).open_source

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Chart sources cover X. -/
theorem iUnion_chartAt_source_eq_univ : (⋃ x : X, (chartAt ℂ x).source) = Set.univ :=
  iUnion_source_chartAt ℂ X

omit [T2Space X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Compactness of X yields a FINITE set of points `{x_1, ..., x_n}`
whose chart sources cover X. -/
theorem exists_finite_chart_cover :
    ∃ (s : Finset X), (⋃ x ∈ s, (chartAt ℂ x).source) = Set.univ := by
  have hcov : Set.univ ⊆ ⋃ x : X, (chartAt ℂ x).source :=
    (iUnion_chartAt_source_eq_univ (X := X)).symm.le
  have hopen : ∀ x : X, IsOpen (chartAt ℂ x).source := fun x => (chartAt ℂ x).open_source
  obtain ⟨s, hs⟩ :=
    IsCompact.elim_finite_subcover isCompact_univ (fun x : X => (chartAt ℂ x).source)
      hopen hcov
  exact ⟨s, Set.eq_univ_of_univ_subset hs⟩

/-! ### Step 1b: local representative of α in a chart

For a chart at `x₀`, the tangent bundle trivialization gives an iso
`TangentSpace y ≃L[ℂ] ℂ` for `y` in the chart's base set. Applied to
`(1 : ℂ)` via `.symmL`, we get the "unit tangent at y in x₀'s
trivialization". Then `α.toFun y` applied to this unit tangent gives
a scalar in `ℂ` (via `Bundle.Trivial X ℂ y = ℂ`).

This is the chart-local holomorphic coefficient of α. -/

/-- The local representative of a holomorphic 1-form α at y, using the
trivialization of the tangent bundle at x₀. In the chart around x₀,
α = `localRep x₀ α y · dz` where z is the chart coordinate. -/
noncomputable def localRep
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) (y : X) : ℂ :=
  α.toFun y ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1)

/-! ### Step 1c: continuity of `localRep` on the trivialization base set

On `(trivializationAt ℂ TangentBundle x₀).baseSet`, the map
`y ↦ (triv x₀).symmL ℂ y 1` is a smooth section of the tangent bundle
(comes from the inverse trivialization applied to a constant). Composed
with α (smooth section of the cotangent bundle) via `clm_bundle_apply`,
the result is continuous.

For the sup-norm argument we only need **continuity**, but smoothness
is available as a bonus (useful for Cauchy estimates later). -/

/-- `localRep α x₀` is continuous on the chart source at x₀. -/
theorem localRep_continuousOn
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    ContinuousOn (localRep α x₀)
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet :=
  sorry

/-! ### Next

- [ ] Finite-cover-based sup-norm: `max_j sup_y (|localRep α x_j y|)`
      over y in chart closure.
- [ ] NormedAddCommGroup / NormedSpace instances.
- [ ] Cauchy estimates on chart reps (they're holomorphic functions in
      the chart).
- [ ] Arzelà–Ascoli assembly.
- [ ] Riesz conclusion.
-/

end Jacobians.Montel
