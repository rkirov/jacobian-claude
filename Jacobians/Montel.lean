import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.Normed.Group.Seminorm
import Jacobians.Genus

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

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- A constant section of a vector bundle (via inverse trivialization) is
continuous on the trivialization's base set.

Proof: the section's total-space form equals `e.toOpenPartialHomeomorph.symm`
composed with `fun y => (y, v)`, which is continuous on `e.baseSet`
since `e.symm` is continuous on its source (= `baseSet × univ` for
vector bundles). -/
theorem continuousOn_symmL_const
    (e : Trivialization ℂ (Bundle.TotalSpace.proj (E := fun x : X =>
      TangentSpace 𝓘(ℂ, ℂ) x)))
    [MemTrivializationAtlas e] (v : ℂ) :
    ContinuousOn
      (fun y : X => TotalSpace.mk' ℂ (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x)
        y (e.symmL ℂ y v))
      e.baseSet := by
  -- The section's total-space form equals `e.symm ∘ (·, v)` on baseSet.
  -- `e.symm` is continuous on its source = baseSet × univ.
  -- `(·, v)` is continuous.
  -- Composition is continuous on baseSet.
  have h1 : ContinuousOn (fun p : X × ℂ => e.toOpenPartialHomeomorph.symm p)
      (e.baseSet ×ˢ Set.univ) := by
    apply e.toOpenPartialHomeomorph.continuousOn_symm.mono
    rw [← e.target_eq]
  have h2 : ContinuousOn (fun y : X => (y, v)) e.baseSet :=
    (continuousOn_id.prodMk continuousOn_const)
  have h3 : Set.MapsTo (fun y : X => (y, v)) e.baseSet (e.baseSet ×ˢ Set.univ) := by
    intro y hy
    exact ⟨hy, Set.mem_univ _⟩
  -- Goal: show the composition on baseSet equals our target function.
  have h4 := h1.comp h2 h3
  -- h4 : ContinuousOn (fun y => e.symm (y, v)) e.baseSet.
  refine h4.congr ?_
  intro y hy
  -- `e.mk_symm hy v : TotalSpace.mk y (e.symm y v) = e.toOpenPartialHomeomorph.symm (y, v)`
  -- and `e.symmL ℂ y v = e.symm y v` definitionally (`symmL` has `toFun := e.symm b`).
  simpa using Trivialization.mk_symm e hy v

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
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
theorem chartCover_cover : (⋃ x ∈ (chartCover : Finset X), (chartAt ℂ x).source) = Set.univ :=
  Classical.choose_spec (exists_finite_chart_cover (X := X))

omit [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
/-- The canonical finite chart cover is non-empty (X is non-empty and the
cover is a cover). -/
theorem chartCover_nonempty : ((chartCover : Finset X)).Nonempty := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hx : x₀ ∈ (⋃ x ∈ (chartCover : Finset X), (chartAt ℂ x).source) := by
    rw [chartCover_cover]; trivial
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, _⟩ := hx
  exact ⟨i, hi⟩

/-- The canonical sup-norm on `HolomorphicOneForms X`. -/
noncomputable def HolomorphicOneForms.supNorm
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) : ℝ :=
  HolomorphicOneForms.supNormOn α ((chartCover : Finset X)) chartCover_nonempty

/-! ### Step 1g: basic norm properties -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- Chart-local sup-norm is non-negative. -/
theorem HolomorphicOneForms.chartNorm_nonneg
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    0 ≤ HolomorphicOneForms.chartNorm α x₀ :=
  Real.iSup_nonneg (fun _ => norm_nonneg _)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- Chart-local sup-norm of zero is zero. -/
theorem HolomorphicOneForms.chartNorm_zero (x₀ : X) :
    HolomorphicOneForms.chartNorm (0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) x₀ = 0 := by
  unfold HolomorphicOneForms.chartNorm localRep
  change (⨆ y : X, ‖(0 : ℂ →L[ℂ] ℂ)
    ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1)‖ : ℝ) = 0
  simp

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] in
/-- `supNormOn` of zero is zero. -/
theorem HolomorphicOneForms.supNormOn_zero (s : Finset X) (hs : s.Nonempty) :
    HolomorphicOneForms.supNormOn (0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) s hs = 0 := by
  unfold HolomorphicOneForms.supNormOn
  simp [HolomorphicOneForms.chartNorm_zero]

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- `supNormOn` is non-negative. -/
theorem HolomorphicOneForms.supNormOn_nonneg
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (s : Finset X) (hs : s.Nonempty) :
    0 ≤ HolomorphicOneForms.supNormOn α s hs := by
  unfold HolomorphicOneForms.supNormOn
  obtain ⟨x₀, hx₀⟩ := hs
  exact le_trans (HolomorphicOneForms.chartNorm_nonneg α x₀)
    (Finset.le_sup' _ hx₀)

omit [T2Space X] [ConnectedSpace X] in
/-- `supNorm` is non-negative. -/
theorem HolomorphicOneForms.supNorm_nonneg
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) :
    0 ≤ HolomorphicOneForms.supNorm α :=
  HolomorphicOneForms.supNormOn_nonneg α _ _

omit [T2Space X] [ConnectedSpace X] in
/-- `supNorm` of zero is zero. -/
theorem HolomorphicOneForms.supNorm_zero :
    HolomorphicOneForms.supNorm (0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) = 0 :=
  HolomorphicOneForms.supNormOn_zero ((chartCover : Finset X)) chartCover_nonempty

/-! ### Step 1h: shrunken (compact) chart cover

For each `x` in `chartCover`, we need a COMPACT subset `K_x ⊂ baseSet_x`
such that the collection `{K_x}` still covers X. Apply the shrinking
lemma (available since X is compact T2 and locally compact as a
charted space over ℂ).

Status: done — `shrunkChart` gives the compact shrinkage. -/

open Classical in
/-- Auxiliary open family for the shrinking lemma: chart source at x if
`x ∈ chartCover`, else `∅`. -/
private noncomputable def coverOpen (x : X) : Set X :=
  if x ∈ (chartCover : Finset X) then (chartAt ℂ x).source else ∅

omit [T2Space X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
private theorem coverOpen_isOpen (x : X) : IsOpen (coverOpen (X := X) x) := by
  unfold coverOpen
  by_cases hx : x ∈ (chartCover : Finset X)
  · rw [if_pos hx]; exact (chartAt ℂ x).open_source
  · rw [if_neg hx]; exact isOpen_empty

omit [T2Space X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
private theorem iUnion_coverOpen_eq :
    (⋃ x : X, coverOpen (X := X) x) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← chartCover_cover (X := X)]
  intro y hy
  simp only [Set.mem_iUnion] at hy
  obtain ⟨x₀, hx₀cover, hx₀src⟩ := hy
  refine Set.mem_iUnion.mpr ⟨x₀, ?_⟩
  unfold coverOpen
  rw [if_pos hx₀cover]
  exact hx₀src

omit [T2Space X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
private theorem coverOpen_locallyFinite (y : X) :
    {x | y ∈ coverOpen (X := X) x}.Finite := by
  apply Set.Finite.subset ((chartCover : Finset X)).finite_toSet
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  unfold coverOpen at hx
  by_contra hxmem
  rw [if_neg (by simpa [Finset.mem_coe] using hxmem)] at hx
  exact absurd hx (Set.notMem_empty y)

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Shrinking lemma applied to `coverOpen`: gives a closed family
`shrunkChart` with `shrunkChart x ⊆ coverOpen x` and still covering X. -/
private theorem exists_compact_shrink :
    ∃ K : X → Set X, (⋃ x, K x) = Set.univ ∧
      (∀ x, IsClosed (K x)) ∧ (∀ x, K x ⊆ coverOpen (X := X) x) :=
  exists_iUnion_eq_closed_subset coverOpen_isOpen coverOpen_locallyFinite
    iUnion_coverOpen_eq

/-- A specific compact shrinkage of the `coverOpen` family. -/
noncomputable def shrunkChart (x : X) : Set X :=
  Classical.choose (exists_compact_shrink (X := X)) x

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem iUnion_shrunkChart_eq : (⋃ x : X, shrunkChart (X := X) x) = Set.univ :=
  (Classical.choose_spec (exists_compact_shrink (X := X))).1

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem shrunkChart_isClosed (x : X) : IsClosed (shrunkChart (X := X) x) :=
  (Classical.choose_spec (exists_compact_shrink (X := X))).2.1 x

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem shrunkChart_isCompact (x : X) : IsCompact (shrunkChart (X := X) x) :=
  (shrunkChart_isClosed x).isCompact

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- `shrunkChart x ⊆ (chartAt ℂ x).source` when `x ∈ chartCover`. -/
theorem shrunkChart_subset_source (x : X) (hx : x ∈ (chartCover : Finset X)) :
    shrunkChart (X := X) x ⊆ (chartAt ℂ x).source := by
  have h := (Classical.choose_spec (exists_compact_shrink (X := X))).2.2 x
  intro y hy
  have hyc := h hy
  unfold coverOpen at hyc
  rw [if_pos hx] at hyc
  exact hyc

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- For x ∉ chartCover, the shrunkChart is empty. -/
theorem shrunkChart_eq_empty (x : X) (hx : x ∉ (chartCover : Finset X)) :
    shrunkChart (X := X) x = ∅ := by
  have h := (Classical.choose_spec (exists_compact_shrink (X := X))).2.2 x
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hyc := h hy
  unfold coverOpen at hyc
  rw [if_neg hx] at hyc
  exact hyc

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Restricted cover: the shrunkCharts indexed by `chartCover` still cover X. -/
theorem iUnion_shrunkChart_chartCover_eq :
    (⋃ x ∈ (chartCover : Finset X), shrunkChart (X := X) x) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← iUnion_shrunkChart_eq (X := X)]
  intro y hy
  simp only [Set.mem_iUnion] at hy ⊢
  obtain ⟨x, hxy⟩ := hy
  by_cases hxmem : x ∈ (chartCover : Finset X)
  · exact ⟨x, hxmem, hxy⟩
  · exfalso
    rw [shrunkChart_eq_empty x hxmem] at hxy
    exact hxy

/-! ### Step 1i: behavior of `localRep` under the vector space operations -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- `localRep` is additive: `localRep (α + β) = localRep α + localRep β`. -/
theorem localRep_add
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ y : X) :
    localRep (α + β) x₀ y = localRep α x₀ y + localRep β x₀ y := by
  unfold localRep
  -- (α + β).toFun y = α.toFun y + β.toFun y
  have : (α + β).toFun y = α.toFun y + β.toFun y := by
    change (⇑(α + β)) y = _
    rw [ContMDiffSection.coe_add]
    rfl
  rw [this]
  rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- `localRep` is homogeneous: `localRep (c • α) = c • localRep α`. -/
theorem localRep_smul (c : ℂ)
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ y : X) :
    localRep (c • α) x₀ y = c • localRep α x₀ y := by
  unfold localRep
  have : (c • α).toFun y = c • α.toFun y := by
    change (⇑(c • α)) y = _
    rw [ContMDiffSection.coe_smul]
    rfl
  rw [this]
  rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- `localRep` is additive in the negation: `localRep (-α) = -localRep α`. -/
theorem localRep_neg
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ y : X) :
    localRep (-α) x₀ y = -localRep α x₀ y := by
  unfold localRep
  have : (-α).toFun y = -α.toFun y := by
    change (⇑(-α)) y = _
    rw [ContMDiffSection.coe_neg]
    rfl
  rw [this]
  rfl

/-! ### Step 1j: proper (bounded) chart-local sup-norm

The earlier `chartNorm α x₀ := ⨆ y : X, ‖localRep α x₀ y‖` is unbounded
in general (the "unit tangent" `e.symmL ℂ y 1` blows up as y approaches
the boundary of baseSet in X). Consequently by Mathlib's convention
`Real.iSup_of_not_bddAbove`, unbounded iSup returns 0 — destroying the
triangle inequality.

The textbook fix: sup only over the compact `shrunkChart x₀` (we built
this above using the shrinking lemma). Since `localRep α x₀` is
continuous on baseSet ⊇ shrunkChart x₀ and shrunkChart x₀ is compact,
the image is compact in ℝ, hence bounded. -/

/-- Bounded chart-local sup-norm: sup over the compact `shrunkChart x₀`. -/
noncomputable def HolomorphicOneForms.chartNormK
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) : ℝ :=
  sSup ((fun y : X => ‖localRep α x₀ y‖) '' shrunkChart (X := X) x₀)

omit [ConnectedSpace X] [Nonempty X] in
/-- `chartNormK` is non-negative (sSup over a set of non-negative values or ∅). -/
theorem HolomorphicOneForms.chartNormK_nonneg
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) : 0 ≤ HolomorphicOneForms.chartNormK α x₀ := by
  unfold HolomorphicOneForms.chartNormK
  by_cases hne : (shrunkChart (X := X) x₀).Nonempty
  · obtain ⟨y, hy⟩ := hne
    apply le_csSup_of_le
    · -- bounded above: localRep continuous on baseSet ⊇ shrunkChart (compact),
      -- so image is bounded
      by_cases hx : x₀ ∈ (chartCover : Finset X)
      · have hsub : shrunkChart (X := X) x₀ ⊆
            (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
          rw [TangentBundle.trivializationAt_baseSet]
          exact shrunkChart_subset_source x₀ hx
        have hcompact := shrunkChart_isCompact (X := X) x₀
        have hcont : ContinuousOn (fun y : X => ‖localRep α x₀ y‖)
            (shrunkChart (X := X) x₀) := by
          have := (localRep_continuousOn α x₀).mono hsub
          exact this.norm
        have himg_compact : IsCompact
            ((fun y : X => ‖localRep α x₀ y‖) '' shrunkChart (X := X) x₀) :=
          hcompact.image_of_continuousOn hcont
        exact himg_compact.bddAbove
      · rw [shrunkChart_eq_empty x₀ hx] at hy
        exact absurd hy (Set.notMem_empty y)
    · exact ⟨y, hy, rfl⟩
    · exact norm_nonneg _
  · -- empty: image is empty, sSup ∅ = 0
    rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne]

omit [ConnectedSpace X] [Nonempty X] in
/-- The image of `‖localRep α x₀ ·‖` over `shrunkChart x₀` is bounded above. -/
theorem HolomorphicOneForms.chartNormK_bddAbove
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    BddAbove ((fun y : X => ‖localRep α x₀ y‖) '' shrunkChart (X := X) x₀) := by
  by_cases hx : x₀ ∈ (chartCover : Finset X)
  · have hsub : shrunkChart (X := X) x₀ ⊆
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
      rw [TangentBundle.trivializationAt_baseSet]
      exact shrunkChart_subset_source x₀ hx
    have hcompact := shrunkChart_isCompact (X := X) x₀
    have hcont : ContinuousOn (fun y : X => ‖localRep α x₀ y‖)
        (shrunkChart (X := X) x₀) :=
      ((localRep_continuousOn α x₀).mono hsub).norm
    exact (hcompact.image_of_continuousOn hcont).bddAbove
  · rw [shrunkChart_eq_empty x₀ hx]
    simp [BddAbove, Set.image_empty]

omit [ConnectedSpace X] [Nonempty X] in
/-- `chartNormK` of the zero section is zero. -/
theorem HolomorphicOneForms.chartNormK_zero (x₀ : X) :
    HolomorphicOneForms.chartNormK
      (0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
        (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
      x₀ = 0 := by
  unfold HolomorphicOneForms.chartNormK localRep
  -- Everything in the image is ‖0 applied to anything‖ = 0.
  have himg : (fun y : X => ‖(0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
        (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)).toFun y
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1)‖) '' shrunkChart (X := X) x₀
      ⊆ {0} := by
    intro r hr
    obtain ⟨y, _, rfl⟩ := hr
    change ‖(0 : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ) _‖ ∈ ({0} : Set ℝ)
    simp
  by_cases hne : (shrunkChart (X := X) x₀).Nonempty
  · obtain ⟨y, hy⟩ := hne
    have hmem : (0 : ℝ) ∈ (fun y : X => ‖(0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
        (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)).toFun y
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1)‖) '' shrunkChart x₀ := by
      refine ⟨y, hy, ?_⟩
      change ‖(0 : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ) _‖ = 0
      simp
    have : (fun y : X => ‖(0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
        (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)).toFun y
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).symmL ℂ y 1)‖) '' shrunkChart x₀ =
        {0} :=
      Set.eq_singleton_iff_unique_mem.mpr ⟨hmem, fun b hb => himg hb⟩
    rw [this]
    exact csSup_singleton 0
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [hne]

/-! ### Step 1k: triangle inequality and homogeneity for `chartNormK` -/

omit [ConnectedSpace X] [Nonempty X] in
/-- Triangle inequality for `chartNormK`: `chartNormK (α+β) ≤ chartNormK α + chartNormK β`. -/
theorem HolomorphicOneForms.chartNormK_add_le
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    HolomorphicOneForms.chartNormK (α + β) x₀ ≤
      HolomorphicOneForms.chartNormK α x₀ + HolomorphicOneForms.chartNormK β x₀ := by
  unfold HolomorphicOneForms.chartNormK
  by_cases hne : (shrunkChart (X := X) x₀).Nonempty
  · apply csSup_le (Set.Nonempty.image _ hne)
    rintro r ⟨y, hy, rfl⟩
    show ‖localRep (α + β) x₀ y‖ ≤ _
    rw [localRep_add]
    calc ‖localRep α x₀ y + localRep β x₀ y‖
        ≤ ‖localRep α x₀ y‖ + ‖localRep β x₀ y‖ := norm_add_le _ _
      _ ≤ sSup ((fun z : X => ‖localRep α x₀ z‖) '' shrunkChart (X := X) x₀) +
          sSup ((fun z : X => ‖localRep β x₀ z‖) '' shrunkChart (X := X) x₀) := by
        apply add_le_add
        · exact le_csSup
            (HolomorphicOneForms.chartNormK_bddAbove α x₀) ⟨y, hy, rfl⟩
        · exact le_csSup
            (HolomorphicOneForms.chartNormK_bddAbove β x₀) ⟨y, hy, rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have hα : sSup ((fun y : X => ‖localRep α x₀ y‖) '' shrunkChart (X := X) x₀) = 0 := by
      simp [hne, Real.sSup_empty]
    have hβ : sSup ((fun y : X => ‖localRep β x₀ y‖) '' shrunkChart (X := X) x₀) = 0 := by
      simp [hne, Real.sSup_empty]
    have hαβ : sSup ((fun y : X => ‖localRep (α + β) x₀ y‖) '' shrunkChart (X := X) x₀) = 0 := by
      simp [hne, Real.sSup_empty]
    rw [hα, hβ, hαβ]; ring_nf; rfl

omit [ConnectedSpace X] [Nonempty X] in
/-- Sub-homogeneity of `chartNormK`: `chartNormK (c • α) ≤ ‖c‖ * chartNormK α`. -/
theorem HolomorphicOneForms.chartNormK_smul_le (c : ℂ)
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    HolomorphicOneForms.chartNormK (c • α) x₀ ≤
      ‖c‖ * HolomorphicOneForms.chartNormK α x₀ := by
  unfold HolomorphicOneForms.chartNormK
  by_cases hne : (shrunkChart (X := X) x₀).Nonempty
  · apply csSup_le (Set.Nonempty.image _ hne)
    rintro r ⟨y, hy, rfl⟩
    show ‖localRep (c • α) x₀ y‖ ≤ _
    rw [localRep_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left
      (le_csSup (HolomorphicOneForms.chartNormK_bddAbove α x₀) ⟨y, hy, rfl⟩)
      (norm_nonneg _)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    have h1 : sSup ((fun y : X => ‖localRep (c • α) x₀ y‖) '' shrunkChart (X := X) x₀) = 0 := by
      simp [hne, Real.sSup_empty]
    have h2 : sSup ((fun y : X => ‖localRep α x₀ y‖) '' shrunkChart (X := X) x₀) = 0 := by
      simp [hne, Real.sSup_empty]
    rw [h1, h2, mul_zero]

omit [ConnectedSpace X] [Nonempty X] in
/-- Full homogeneity of `chartNormK`: `chartNormK (c • α) = ‖c‖ * chartNormK α`. -/
theorem HolomorphicOneForms.chartNormK_smul (c : ℂ)
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) :
    HolomorphicOneForms.chartNormK (c • α) x₀ =
      ‖c‖ * HolomorphicOneForms.chartNormK α x₀ := by
  refine le_antisymm (HolomorphicOneForms.chartNormK_smul_le c α x₀) ?_
  -- Reverse: ‖c‖ * chartNormK α ≤ chartNormK (c • α).
  by_cases hc : c = 0
  · subst hc
    simp
    exact HolomorphicOneForms.chartNormK_nonneg _ _
  · -- c ≠ 0: apply smul_le with c⁻¹ to (c • α).
    have hc' : c⁻¹ • (c • α) = α := by
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    have hsub := HolomorphicOneForms.chartNormK_smul_le c⁻¹ (c • α) x₀
    rw [hc'] at hsub
    -- hsub : chartNormK α x₀ ≤ ‖c⁻¹‖ * chartNormK (c • α) x₀
    rw [norm_inv] at hsub
    have hcpos : 0 < ‖c‖ := by
      rw [norm_pos_iff]; exact hc
    -- From: chartNormK α ≤ (1/‖c‖) * chartNormK (c•α)
    -- Multiply both sides by ‖c‖: ‖c‖ * chartNormK α ≤ chartNormK (c•α)
    calc ‖c‖ * HolomorphicOneForms.chartNormK α x₀
        ≤ ‖c‖ * (‖c‖⁻¹ * HolomorphicOneForms.chartNormK (c • α) x₀) :=
          mul_le_mul_of_nonneg_left hsub (norm_nonneg _)
      _ = HolomorphicOneForms.chartNormK (c • α) x₀ := by
          rw [← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]

/-! ### Step 1l: assembled sup-norm over the finite chart cover -/

/-- The assembled sup-norm on `HolomorphicOneForms X`: sup over `chartCover` of
per-chart `chartNormK`. -/
noncomputable def HolomorphicOneForms.supNormK
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) : ℝ :=
  (chartCover : Finset X).sup' (chartCover_nonempty)
    (fun x₀ => HolomorphicOneForms.chartNormK α x₀)

omit [ConnectedSpace X] in
/-- `supNormK` is non-negative. -/
theorem HolomorphicOneForms.supNormK_nonneg
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) :
    0 ≤ HolomorphicOneForms.supNormK α := by
  unfold HolomorphicOneForms.supNormK
  obtain ⟨x₀, hx₀⟩ := chartCover_nonempty (X := X)
  exact le_trans (HolomorphicOneForms.chartNormK_nonneg α x₀)
    (Finset.le_sup' _ hx₀)

omit [ConnectedSpace X] in
/-- `supNormK` of zero is zero. -/
theorem HolomorphicOneForms.supNormK_zero :
    HolomorphicOneForms.supNormK (0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) = 0 := by
  unfold HolomorphicOneForms.supNormK
  simp [HolomorphicOneForms.chartNormK_zero]

omit [ConnectedSpace X] in
/-- Triangle inequality for `supNormK`: `supNormK (α+β) ≤ supNormK α + supNormK β`. -/
theorem HolomorphicOneForms.supNormK_add_le
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) :
    HolomorphicOneForms.supNormK (α + β) ≤
      HolomorphicOneForms.supNormK α + HolomorphicOneForms.supNormK β := by
  unfold HolomorphicOneForms.supNormK
  rw [Finset.sup'_le_iff]
  intro x₀ hx₀
  calc HolomorphicOneForms.chartNormK (α + β) x₀
      ≤ HolomorphicOneForms.chartNormK α x₀ +
        HolomorphicOneForms.chartNormK β x₀ :=
        HolomorphicOneForms.chartNormK_add_le α β x₀
    _ ≤ (chartCover : Finset X).sup' chartCover_nonempty
          (fun y => HolomorphicOneForms.chartNormK α y) +
        (chartCover : Finset X).sup' chartCover_nonempty
          (fun y => HolomorphicOneForms.chartNormK β y) :=
        add_le_add (Finset.le_sup' _ hx₀) (Finset.le_sup' _ hx₀)

omit [ConnectedSpace X] in
/-- Homogeneity of `supNormK`: `supNormK (c • α) = ‖c‖ * supNormK α`. -/
theorem HolomorphicOneForms.supNormK_smul (c : ℂ)
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) :
    HolomorphicOneForms.supNormK (c • α) = ‖c‖ * HolomorphicOneForms.supNormK α := by
  unfold HolomorphicOneForms.supNormK
  have hrw : (fun x₀ : X => HolomorphicOneForms.chartNormK (c • α) x₀) =
      fun x₀ => ‖c‖ * HolomorphicOneForms.chartNormK α x₀ := by
    funext x₀; exact HolomorphicOneForms.chartNormK_smul c α x₀
  rw [hrw, ← Finset.mul₀_sup' (norm_nonneg c) _ _ chartCover_nonempty]

/-! ### Step 1m: vanishing of `localRep` from `chartNormK = 0` -/

omit [ConnectedSpace X] [Nonempty X] in
/-- If `chartNormK α x₀ = 0` then `localRep α x₀ y = 0` for all y ∈ `shrunkChart x₀`. -/
theorem HolomorphicOneForms.localRep_eq_zero_of_chartNormK_eq_zero
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) (h : HolomorphicOneForms.chartNormK α x₀ = 0)
    (y : X) (hy : y ∈ shrunkChart (X := X) x₀) :
    localRep α x₀ y = 0 := by
  -- `‖localRep α x₀ y‖ ≤ chartNormK α x₀ = 0` via `le_csSup`.
  have hbd := HolomorphicOneForms.chartNormK_bddAbove α x₀
  have hle : ‖localRep α x₀ y‖ ≤ HolomorphicOneForms.chartNormK α x₀ := by
    unfold HolomorphicOneForms.chartNormK
    exact le_csSup hbd ⟨y, hy, rfl⟩
  rw [h] at hle
  -- `‖localRep α x₀ y‖ ≤ 0` + norm nonneg ⇒ `‖localRep α x₀ y‖ = 0` ⇒ `localRep α x₀ y = 0`.
  have : ‖localRep α x₀ y‖ = 0 := le_antisymm hle (norm_nonneg _)
  exact norm_eq_zero.mp this

omit [ConnectedSpace X] in
/-- If `supNormK α = 0` then `chartNormK α x = 0` for every `x ∈ chartCover`. -/
theorem HolomorphicOneForms.chartNormK_eq_zero_of_supNormK_eq_zero
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h : HolomorphicOneForms.supNormK α = 0)
    (x : X) (hx : x ∈ (chartCover : Finset X)) :
    HolomorphicOneForms.chartNormK α x = 0 := by
  -- chartNormK α x ≤ supNormK α = 0 via `Finset.le_sup'`.
  have hle : HolomorphicOneForms.chartNormK α x ≤ HolomorphicOneForms.supNormK α := by
    unfold HolomorphicOneForms.supNormK
    exact Finset.le_sup' _ hx
  rw [h] at hle
  exact le_antisymm hle (HolomorphicOneForms.chartNormK_nonneg α x)

omit [ConnectedSpace X] in
/-- Consequence: `supNormK α = 0` forces `localRep α x₀ y = 0` for every
`x₀ ∈ chartCover` and `y ∈ shrunkChart x₀`. -/
theorem HolomorphicOneForms.localRep_eq_zero_of_supNormK_eq_zero
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h : HolomorphicOneForms.supNormK α = 0)
    (x₀ : X) (hx₀ : x₀ ∈ (chartCover : Finset X))
    (y : X) (hy : y ∈ shrunkChart (X := X) x₀) :
    localRep α x₀ y = 0 :=
  HolomorphicOneForms.localRep_eq_zero_of_chartNormK_eq_zero α x₀
    (HolomorphicOneForms.chartNormK_eq_zero_of_supNormK_eq_zero α h x₀ hx₀) y hy

/-! ### Step 1n: `localRep α x₀ y = 0` at `y ∈ baseSet` forces `α.toFun y = 0`

The tangent space `T_y X` is 1-dim over ℂ (as `X` is charted over ℂ). The
trivialization `e` at `x₀` gives a continuous linear EQUIVALENCE
`T_y X ≃L[ℂ] ℂ` for `y ∈ e.baseSet`, and `e.symmL ℂ y 1` is the image
of `1 ∈ ℂ` under the inverse — hence a spanning vector of `T_y X`.

`α.toFun y : T_y X →L[ℂ] ℂ` vanishing on this spanning vector ⇒ zero as a CLM. -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] in
/-- If the local representative of α vanishes at y ∈ baseSet of the trivialization
at x₀, then `α.toFun y = 0` as a continuous linear map. -/
theorem alpha_toFun_eq_zero_of_localRep_eq_zero
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ y : X)
    (hy : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet)
    (h : localRep α x₀ y = 0) :
    α.toFun y = 0 := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀ with he_def
  set φ := e.continuousLinearEquivAt ℂ y hy with hφ_def
  -- `φ.symm` (as a CLM) equals `e.symmL ℂ y`.
  have hφsymm : (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) = e.symmL ℂ y :=
    Trivialization.symm_continuousLinearEquivAt_eq' e hy
  -- Compose α.toFun y with φ.symm on the right; the result is a CLM ℂ →L[ℂ] ℂ.
  have hcomp : (α.toFun y : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ).comp
      (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) = 0 := by
    apply ContinuousLinearMap.ext_ring
    show α.toFun y ((φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) 1) = 0
    rw [hφsymm]
    exact h
  -- Post-compose with φ to recover α.toFun y.
  have hext : (α.toFun y : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ) =
      ((α.toFun y).comp (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y)).comp
        (φ : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ) := by
    apply ContinuousLinearMap.ext
    intro w
    change α.toFun y w = α.toFun y (φ.symm (φ w))
    rw [φ.symm_apply_apply]
  rw [hext, hcomp, ContinuousLinearMap.zero_comp]

omit [ConnectedSpace X] in
/-- Negation invariance: `supNormK (-α) = supNormK α`. -/
theorem HolomorphicOneForms.supNormK_neg
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)) :
    HolomorphicOneForms.supNormK (-α) = HolomorphicOneForms.supNormK α := by
  have h : -α = (-1 : ℂ) • α := (neg_one_smul ℂ α).symm
  rw [h, HolomorphicOneForms.supNormK_smul]
  simp

/-! ### Step 1o: positive-definiteness of supNormK -/

omit [ConnectedSpace X] in
/-- Positive-definiteness: `supNormK α = 0 → α = 0`. -/
theorem HolomorphicOneForms.eq_zero_of_supNormK_eq_zero
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h : HolomorphicOneForms.supNormK α = 0) :
    α = 0 := by
  -- It suffices to show α.toFun y = 0 for every y ∈ X.
  apply ContMDiffSection.ext
  intro y
  -- y is in some shrunkChart x₀ for x₀ ∈ chartCover (by coverage).
  have hmem : y ∈ (Set.univ : Set X) := Set.mem_univ _
  rw [← iUnion_shrunkChart_chartCover_eq (X := X)] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨x₀, hx₀mem, hyx₀⟩ := hmem
  -- `localRep α x₀ y = 0` by localRep_eq_zero_of_supNormK_eq_zero.
  have hlocal := HolomorphicOneForms.localRep_eq_zero_of_supNormK_eq_zero α h x₀ hx₀mem y hyx₀
  -- `y ∈ baseSet` (via shrunkChart ⊆ source + TangentBundle.trivializationAt_baseSet).
  have hy_baseSet :
      y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact shrunkChart_subset_source x₀ hx₀mem hyx₀
  -- α.toFun y = 0 (as a CLM) by alpha_toFun_eq_zero_of_localRep_eq_zero.
  have htofun := alpha_toFun_eq_zero_of_localRep_eq_zero α x₀ y hy_baseSet hlocal
  -- Reconcile with the zero section.
  change α.toFun y = (0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
    (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)).toFun y
  rw [htofun]
  -- ⇑(0 : ContMDiffSection ...) y = 0; uses coe_zero.
  have : (⇑(0 : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))) = 0 :=
    ContMDiffSection.coe_zero
  exact (congrFun this y).symm

/-! ### Step 1p: `NormedAddCommGroup` instance on `HolomorphicOneForms X`

`HolomorphicOneForms X` is a `def` alias for `ContMDiffSection` (see
`Jacobians/Genus.lean`). We can therefore add an `AddGroupNorm` on it
and use Mathlib's `AddGroupNorm.toNormedAddCommGroup`.

`supNormK` taking a `ContMDiffSection ...` argument unifies with
`HolomorphicOneForms X` by definitional equality. -/

omit [ConnectedSpace X] in
/-- The `AddGroupNorm` structure on `HolomorphicOneForms X`. -/
noncomputable def HolomorphicOneForms.supNormKAsAddGroupNorm :
    AddGroupNorm (Jacobians.HolomorphicOneForms X) where
  toFun := fun α => HolomorphicOneForms.supNormK α
  map_zero' := HolomorphicOneForms.supNormK_zero
  add_le' := fun α β => HolomorphicOneForms.supNormK_add_le α β
  neg' := fun α => HolomorphicOneForms.supNormK_neg α
  eq_zero_of_map_eq_zero' := fun α h => HolomorphicOneForms.eq_zero_of_supNormK_eq_zero α h

omit [ConnectedSpace X] in
/-- `HolomorphicOneForms X` as a `NormedAddCommGroup`.

Non-instance: to avoid conflict with potential other normed-group
instances upstream or competing choices. Consumers can locally
`letI := HolomorphicOneForms.normedAddCommGroup` to enable. -/
@[reducible] noncomputable def HolomorphicOneForms.normedAddCommGroup :
    NormedAddCommGroup (Jacobians.HolomorphicOneForms X) :=
  AddGroupNorm.toNormedAddCommGroup HolomorphicOneForms.supNormKAsAddGroupNorm

/-! ### Step 1q: `NormedSpace ℂ` instance

With the `NormedAddCommGroup` established, upgrading to `NormedSpace ℂ`
requires `‖c • α‖ ≤ ‖c‖ * ‖α‖` — which we already have as equality via
`supNormK_smul`. -/

omit [ConnectedSpace X] in
/-- `HolomorphicOneForms X` as a `NormedSpace ℂ`.

Non-instance: companion to `normedAddCommGroup`. -/
@[reducible] noncomputable def HolomorphicOneForms.normedSpace :
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    NormedSpace ℂ (Jacobians.HolomorphicOneForms X) :=
  letI : NormedAddCommGroup (Jacobians.HolomorphicOneForms X) :=
    HolomorphicOneForms.normedAddCommGroup
  NormedSpace.mk (fun c α => le_of_eq (HolomorphicOneForms.supNormK_smul c α))

/-! ### Next
- [ ] Completeness (Banach): uniform limits of holomorphic sections are holomorphic.
- [ ] Cauchy estimates on `localRep` (holomorphic functions in chart).
- [ ] Equicontinuity of bounded families.
- [ ] Arzelà–Ascoli assembly.
- [ ] Riesz conclusion ⇒ FiniteDimensional.
-/

end Jacobians.Montel
