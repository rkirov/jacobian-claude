import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Analysis.Complex.Basic

/-!
# Montel path — finite chart cover + compact shrinking

Foundational pieces for the Montel/Ahlfors-Sario construction:

- `exists_finite_chart_cover` — X compact + `ChartedSpace ℂ X` gives a
  finite subcover of the chart sources.
- `chartCover : Finset X` — a canonical choice, via `Classical.choose`.
- `shrunkChart : X → Set X` — a COMPACT refinement, each ⊆ the chart
  source, still covering X. Built via Mathlib's
  `exists_iUnion_eq_closed_subset` (shrinking lemma on normal spaces;
  NormalSpace is auto from compact T2).

This file is intentionally light on imports — no vector-bundle machinery
— so it compiles quickly and independently. -/

namespace Jacobians.Montel

open scoped Manifold ContDiff

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Finite chart cover -/

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- The chart source at x is open in X. -/
theorem isOpen_chartAt_source (x : X) : IsOpen (chartAt ℂ x).source :=
  (chartAt ℂ x).open_source

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Chart sources cover X. -/
theorem iUnion_chartAt_source_eq_univ : (⋃ x : X, (chartAt ℂ x).source) = Set.univ :=
  iUnion_source_chartAt ℂ X

omit [T2Space X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
/-- Compactness of X yields a FINITE set of points whose chart sources cover X. -/
theorem exists_finite_chart_cover :
    ∃ (s : Finset X), (⋃ x ∈ s, (chartAt ℂ x).source) = Set.univ := by
  have hcov : Set.univ ⊆ ⋃ x : X, (chartAt ℂ x).source :=
    (iUnion_chartAt_source_eq_univ (X := X)).symm.le
  have hopen : ∀ x : X, IsOpen (chartAt ℂ x).source := fun x => (chartAt ℂ x).open_source
  obtain ⟨s, hs⟩ :=
    IsCompact.elim_finite_subcover isCompact_univ (fun x : X => (chartAt ℂ x).source)
      hopen hcov
  exact ⟨s, Set.eq_univ_of_univ_subset hs⟩

/-! ### Canonical chart cover + shrinking -/

/-- The canonical finite chart cover of compact X. -/
noncomputable def chartCover : Finset X :=
  Classical.choose (exists_finite_chart_cover (X := X))

omit [T2Space X] [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem chartCover_cover :
    (⋃ x ∈ (chartCover : Finset X), (chartAt ℂ x).source) = Set.univ :=
  Classical.choose_spec (exists_finite_chart_cover (X := X))

omit [T2Space X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] in
/-- The canonical finite chart cover is non-empty. -/
theorem chartCover_nonempty : ((chartCover : Finset X)).Nonempty := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hx : x₀ ∈ (⋃ x ∈ (chartCover : Finset X), (chartAt ℂ x).source) := by
    rw [chartCover_cover]; trivial
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, _⟩ := hx
  exact ⟨i, hi⟩

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
/-- Shrinking lemma: gives a closed family `shrunkChart` with
`shrunkChart x ⊆ coverOpen x` and still covering X. -/
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

end Jacobians.Montel
