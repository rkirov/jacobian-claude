/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.SmoothPathCore
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Canonical dissection and the period real basis (#7 scaffold)

This file scaffolds the discharge of `exists_periodLattice_realBasis` (the period lattice is a
full-rank ℝ-lattice — the Riemann bilinear relations). It decomposes the goal into **two pillars**:

* **Topology (isolated).** `exists_canonicalDissection`: a compact connected Riemann surface admits
  a canonical dissection — a symplectic homology basis of `2g` closed loops whose periods generate
  the period lattice. This bundles `H₁(X;ℤ) ≅ ℤ^{2g}`, the `4g`-gon dissection, and period
  homology-invariance — none of which Mathlib has for surfaces, so it is the isolated input.

* **Analysis (the build).** `periodVec_linearIndependent`: the `2g` periods of a dissection are
  ℝ-linearly independent. This is the Riemann bilinear relations + positivity
  `−i∑(A_k B̄_k − B_k Ā_k) = ∬_X ω∧ω̄ > 0`, provable via Riemann's cut-surface + Green's-theorem
  argument (Mathlib has rectangle Green; *no* Hodge/de Rham). See `docs/period_realbasis_plan.md`.

The **assembly** `realBasis_of_canonicalDissection` (PROVEN here) combines the two: `2g`
ℝ-independent vectors in `ℂ^g ≅ ℝ^{2g}` form an ℝ-basis, and generation gives the `ℤ`-span equality.
`exists_periodLattice_realBasis` (in `PeriodLattice.lean`) is then a two-line consequence.

References: Forster §§20–21; Miranda Ch. V §§1–3; Griffiths–Harris Ch. 2 pp. 231–232; Chai §1.4.
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Canonical dissection of a compact Riemann surface.** A symplectic homology basis of `2g`
closed smooth loops whose periods `ℤ`-generate the period lattice.

(Pass-1 scaffold: carries the loops + closedness + generation, which is all the *assembly* needs.
The cut-surface 2-cell data — a polygon-gluing map + boundary word + intersection numbers — needed
to *prove* `periodVec_linearIndependent` via Green's theorem will be added as further fields when
that proof is built; see `docs/period_realbasis_plan.md`.) -/
structure CanonicalDissection (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] where
  /-- The `2g` symplectic homology-basis loops `a₁,…,a_g,b₁,…,b_g`. -/
  loop : Fin (2 * genus X) → (ℝ → X)
  /-- Each is a closed smooth loop. -/
  loop_closed : ∀ k, IsClosedSmoothLoop (loop k)
  /-- **Generation.** Every closed-loop period is a `ℤ`-combination of the basis loops' periods.
  (Encodes `H₁`-generation together with period homology-invariance, at the period level.) -/
  generates : closedLoopPeriods X ⊆
    Submodule.span ℤ (Set.range (fun k => periodVec (loop k)))

/-- **[ISOLATED TOPOLOGICAL INPUT]** Every compact connected Riemann surface admits a canonical
dissection. This is the surface-topology content (`H₁(X;ℤ) ≅ ℤ^{2g}`, the canonical `4g`-gon
dissection, period homology-invariance), which Mathlib has no path to for surfaces; it is therefore
isolated here rather than discharged. (Forster §§20–21; Miranda Ch. V.) -/
theorem exists_canonicalDissection (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Nonempty (CanonicalDissection X) :=
  sorry

/-- **[ANALYTIC CONTENT — Riemann bilinear relations, deferred to the Green build]** The `2g`
periods of a canonical dissection are ℝ-linearly independent in `ℂ^g ≅ ℝ^{2g}`. The classical proof
(Riemann; cut-surface + Green's theorem, NOT Hodge/de Rham) establishes the positivity of the
Riemann form `−i∑_k (A_k B̄_k − B_k Ā_k) = ∬_X ω∧ω̄ > 0`, which is exactly this independence. See
`docs/period_realbasis_plan.md` for the dependency sub-tree (`greenOnPolygon`,
`exists_primitive_simplyConnected`, `riemann_relation_I`, `riemann_relation_positivity`). -/
theorem periodVec_linearIndependent (D : CanonicalDissection X) :
    LinearIndependent ℝ (fun k => (periodVec (D.loop k) : Fin (genus X) → ℂ)) :=
  sorry

/-- The real dimension of `ℂ^g` is `2g`. -/
theorem finrank_real_pi_complex :
    Module.finrank ℝ (Fin (genus X) → ℂ) = 2 * genus X := by
  rw [Module.finrank_pi_fintype ℝ]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul]
  ring

/-- **Assembly (PROVEN).** From a canonical dissection, the period lattice
`span ℤ (closedLoopPeriods X)` is the `ℤ`-span of an ℝ-basis of `ℂ^g`. The `2g` periods are
ℝ-independent (`periodVec_linearIndependent`) and number `2g = finrank ℝ (ℂ^g)`, hence form a basis
`b`; generation (`D.generates`) plus membership of each basis period in `closedLoopPeriods` give
`span ℤ (closedLoopPeriods X) = span ℤ (range b)`. -/
theorem realBasis_of_canonicalDissection (D : CanonicalDissection X) :
    ∃ b : Module.Basis (Fin (2 * genus X)) ℝ (Fin (genus X) → ℂ),
      Submodule.span ℤ (closedLoopPeriods X) = Submodule.span ℤ (Set.range ⇑b) := by
  classical
  have hli : LinearIndependent ℝ (fun k => (periodVec (D.loop k) : Fin (genus X) → ℂ)) :=
    periodVec_linearIndependent D
  -- The `2g` independent vectors span (finrank of their span `= 2g = finrank ℝ (ℂ^g)`).
  have hsp : Submodule.span ℝ (Set.range (fun k => (periodVec (D.loop k) : Fin (genus X) → ℂ)))
      = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by
      rw [finrank_span_eq_card hli, Fintype.card_fin, finrank_real_pi_complex])
  set b : Module.Basis (Fin (2 * genus X)) ℝ (Fin (genus X) → ℂ) :=
    Module.Basis.mk hli hsp.ge with hb
  have hbcoe : ⇑b = fun k => (periodVec (D.loop k) : Fin (genus X) → ℂ) := by
    rw [hb]; exact Module.Basis.coe_mk hli hsp.ge
  refine ⟨b, ?_⟩
  rw [hbcoe]
  -- `span ℤ (closedLoopPeriods) = span ℤ (range (periodVec ∘ loop))`.
  apply le_antisymm
  · -- `⊆`: generation.
    exact Submodule.span_le.mpr D.generates
  · -- `⊇`: each basis period is a closed-loop period.
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    exact Submodule.subset_span ⟨D.loop k, D.loop_closed k, rfl⟩

end Jacobians
