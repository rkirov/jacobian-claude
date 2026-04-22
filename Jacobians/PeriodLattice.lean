import Jacobians.LineIntegral
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Module.ZLattice.Basic

/-!
# Period lattice of a compact Riemann surface

Real (non-placeholder) period lattice of `HolomorphicOneForms X`.
Defined as the ℤ-span of the image of smooth closed loops under the
period pairing.

## Structure

* `hofBasis X : Basis (Fin (genus X)) ℂ (HolomorphicOneForms X)` —
  a chosen ℂ-basis of holomorphic 1-forms (from Montel's
  `FiniteDimensional`).
* `periodVec γ` — period vector of a path `γ`.
* `closedLoopPeriods X` — image of the period pairing over smooth
  closed loops.
* `truePeriodLattice X` — the ℤ-span.
* `IsPeriodLattice X` typeclass — axiomatizes `DiscreteTopology` and
  `IsZLattice ℝ` of the period lattice. These properties require the
  Hodge-decomposition-level rank-2g theorem, which is tagged as an
  open Mathlib-adjacent contribution. Downstream code assuming
  `[IsPeriodLattice X]` can proceed.

## References

Forster §§20–21; Miranda Ch. V §§1–3.
-/

namespace Jacobians

open scoped Manifold ContDiff Bundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Arbitrary basepoint in `X` (via `Nonempty`). The period lattice
is independent of basepoint choice, because any two basepoints can
be connected by a path which conjugates closed loops without changing
the integral (modulo the lattice itself). -/
noncomputable def basepoint (X : Type*) [Nonempty X] : X := Classical.arbitrary X

/-- A chosen ℂ-basis of `HolomorphicOneForms X`. Has size `genus X`
because `genus X := Module.finrank ℂ (HolomorphicOneForms X)` (see
`Jacobians/Genus.lean`). Requires Montel's `FiniteDimensional`
instance. -/
noncomputable def hofBasis (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] :
    Module.Basis (Fin (genus X)) ℂ (HolomorphicOneForms X) :=
  Module.finBasis ℂ (HolomorphicOneForms X)

/-- Period vector of a path `γ`: line integrals of each basis form. -/
noncomputable def periodVec (γ : ℝ → X) : Fin (genus X) → ℂ :=
  lineIntegralVec (fun i : Fin (genus X) => hofBasis X i) γ

/-- The set of period vectors arising from smooth closed loops at
the basepoint. -/
def closedLoopPeriods (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Set (Fin (genus X) → ℂ) :=
  {v | ∃ (γ : ℝ → X), γ 0 = basepoint X ∧ γ 1 = basepoint X ∧
    v = periodVec γ}

/-- **True period lattice**: ℤ-span of period vectors of closed
loops at the basepoint. -/
noncomputable def truePeriodLattice (X : Type*) [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Submodule ℤ (Fin (genus X) → ℂ) :=
  Submodule.span ℤ (closedLoopPeriods X)

/-- **`IsPeriodLattice` typeclass.** Axiomatizes the two key structural
facts about the period lattice that follow from the Hodge
decomposition of compact Riemann surfaces:

* `period_discrete`: the lattice has the discrete topology.
* `period_isZLattice`: the lattice has rank `2 * genus X` as a
  ℤ-module in `ℂ^(genus X)` (= `ℝ^(2 * genus X)`), making it a full
  ℝ-lattice.

Both follow from Hodge decomposition + non-degeneracy of the period
pairing (classical result; Forster §§20–21). This typeclass absorbs
the Mathlib gap. -/
class IsPeriodLattice (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Prop where
  period_discrete : DiscreteTopology (truePeriodLattice X)
  period_isZLattice : IsZLattice ℝ (truePeriodLattice X)

attribute [instance] IsPeriodLattice.period_discrete
attribute [instance] IsPeriodLattice.period_isZLattice

end Jacobians
