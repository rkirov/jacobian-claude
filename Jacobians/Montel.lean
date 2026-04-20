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

/-- A constant section of a vector bundle (via inverse trivialization) is
continuous on the trivialization's base set. -/
theorem continuousOn_symmL_const
    (e : Trivialization ℂ (Bundle.TotalSpace.proj (E := fun x : X =>
      TangentSpace 𝓘(ℂ, ℂ) x)))
    [MemTrivializationAtlas e] (v : ℂ) :
    ContinuousOn
      (fun y : X => TotalSpace.mk' ℂ (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x)
        y (e.symmL ℂ y v))
      e.baseSet := by
  sorry

/-- `localRep α x₀` is continuous on the trivialization's base set. -/
theorem localRep_continuousOn
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    ContinuousOn (localRep α x₀)
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
  -- CLM section α is continuous (from ContMDiff).
  have hα : ContinuousOn
      (fun y : X => TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)
        y (α.toFun y))
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet :=
    α.contMDiff_toFun.continuous.continuousOn
  -- Constant tangent section is continuous on base set.
  have hv := continuousOn_symmL_const (X := X)
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀) 1
  -- Apply: continuity of α applied to the tangent section.
  have hap := hα.clm_bundle_apply hv
  -- hap : ContinuousOn (fun y => TotalSpace.mk' ℂ y (α.toFun y ((triv x₀).symmL ℂ y 1)))
  --         baseSet
  -- Project to ℂ: for Bundle.Trivial, the total space is X × ℂ and the second
  -- projection is continuous.
  have hproj : Continuous
      (fun p : Bundle.TotalSpace ℂ (Bundle.Trivial X ℂ) => p.2) :=
    continuous_snd.comp (Bundle.Trivial.homeomorphProd X ℂ).continuous
  exact hproj.comp_continuousOn hap

/-! ### Step 1d: chart-local sup-norm

For each chart (parameterized by `x₀`), the chart-local sup-norm of α
is `sSup_{y ∈ X} ‖localRep α x₀ y‖`. By compactness of X + continuity
of `‖localRep α x₀ ·‖` on the chart base set, this is finite (though
the specific value depends on `α`'s behavior outside the base set,
which is where the formal choice matters). -/

/-- The chart-local sup-norm of α, indexed by the center x₀ of a chart. -/
noncomputable def HolomorphicOneForms.chartNorm
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) : ℝ :=
  ⨆ y : X, ‖localRep α x₀ y‖

/-! ### Step 1e: finite-cover sup-norm

The actual sup-norm on `HolomorphicOneForms X`: pick a finite chart
cover (via `exists_finite_chart_cover`), and take the `Finset.sup` of
chart-local sup-norms.

Note: the specific finite cover used is not canonical, but any choice
yields an equivalent norm (classical fact: all sup-norms coming from
finite atlas refinements are equivalent). -/

/-- The finite-cover sup-norm of α, using a given non-empty finite cover. -/
noncomputable def HolomorphicOneForms.supNormOn
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (s : Finset X) (hs : s.Nonempty) : ℝ :=
  s.sup' hs (fun x₀ => HolomorphicOneForms.chartNorm α x₀)

/-! ### Step 1f: canonical finite cover

Pick a specific non-empty finite cover via `Classical.choose`. Any such
choice yields an equivalent sup-norm (classical fact). -/

/-- The canonical finite chart cover of compact X. -/
noncomputable def chartCover : Finset X :=
  Classical.choose (exists_finite_chart_cover (X := X))

omit [T2Space X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem chartCover_cover : (⋃ x ∈ chartCover (X := X), (chartAt ℂ x).source) = Set.univ :=
  Classical.choose_spec (exists_finite_chart_cover (X := X))

omit [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
/-- The canonical finite chart cover is non-empty (X is non-empty and the
cover is a cover). -/
theorem chartCover_nonempty : (chartCover (X := X)).Nonempty := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hx : x₀ ∈ (⋃ x ∈ chartCover (X := X), (chartAt ℂ x).source) := by
    rw [chartCover_cover]; trivial
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, _⟩ := hx
  exact ⟨i, hi⟩

/-- The canonical sup-norm on `HolomorphicOneForms X`. -/
noncomputable def HolomorphicOneForms.supNorm
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) : ℝ :=
  HolomorphicOneForms.supNormOn α (chartCover (X := X)) chartCover_nonempty

/-! ### Step 1g: basic norm properties -/

/-- Chart-local sup-norm is non-negative. -/
theorem HolomorphicOneForms.chartNorm_nonneg
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    0 ≤ HolomorphicOneForms.chartNorm α x₀ := by
  unfold HolomorphicOneForms.chartNorm
  -- ⨆ y, ‖localRep α x₀ y‖ ≥ 0 since each term is ≥ 0.
  obtain ⟨y₀⟩ := (inferInstance : Nonempty X)
  exact le_ciSup_of_le (by
    -- Need BddAbove of the range. This isn't automatic; we use that
    -- `localRep α x₀` is locally continuous and X is compact, so
    -- bounded. For now this is deferred.
    sorry) y₀ (norm_nonneg _)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Chart-local sup-norm of zero is zero. -/
theorem HolomorphicOneForms.chartNorm_zero (x₀ : X) :
    HolomorphicOneForms.chartNorm (0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) x₀ = 0 := by
  unfold HolomorphicOneForms.chartNorm localRep
  change (⨆ y : X, ‖(0 : ℂ →L[ℂ] ℂ)
    ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1)‖ : ℝ) = 0
  simp

/-! ### Next

- [ ] Boundedness of `localRep α x₀` on X (via compactness).
- [ ] Prove `supNorm = 0 ↔ α = 0` (positive-definiteness).
- [ ] Prove triangle + scalar mult compat.
- [ ] NormedAddCommGroup instance.
- [ ] Cauchy estimates on `localRep` (holomorphic functions in chart).
- [ ] Equicontinuity of bounded families.
- [ ] Arzelà–Ascoli assembly.
- [ ] Riesz conclusion ⇒ FiniteDimensional.
-/

end Jacobians.Montel
