import Jacobians.ZLatticeQuotient
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Validation: ZLattice-quotient architecture works for the Jacobian target

Confirms that the structural instances needed for `Jacobian X`
(`AddCommGroup`, `TopologicalSpace`, `T2Space`, `CompactSpace`,
`ChartedSpace (Fin g → ℂ)`) actually fire on the target ambient space
`Fin g → ℂ` used by the challenge, via `Jacobians.ZLatticeQuotient`.

The key bridge: `FiniteDimensional.complexToReal` in
`Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean` turns
`FiniteDimensional ℂ (Fin g → ℂ)` into `FiniteDimensional ℝ (Fin g → ℂ)`
automatically. `NormedSpace ℝ (Fin g → ℂ)` comes from
`NormedSpace.restrictScalars` via the usual scalar tower.
-/

namespace Jacobians.Validate

noncomputable section

variable (g : ℕ)

/-! ### Instance-chain sanity checks. -/

example : FiniteDimensional ℝ ℂ := inferInstance
example : FiniteDimensional ℂ (Fin g → ℂ) := inferInstance
example : FiniteDimensional ℝ (Fin g → ℂ) := inferInstance
example : NormedSpace ℝ (Fin g → ℂ) := inferInstance

/-! ### Jacobian-shaped quotient picks up all structural instances. -/

variable (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]

example : AddCommGroup ((Fin g → ℂ) ⧸ Λ.toAddSubgroup) := inferInstance
example : TopologicalSpace ((Fin g → ℂ) ⧸ Λ.toAddSubgroup) := inferInstance
example : T2Space ((Fin g → ℂ) ⧸ Λ.toAddSubgroup) := inferInstance
example : CompactSpace ((Fin g → ℂ) ⧸ Λ.toAddSubgroup) := inferInstance
example : ChartedSpace (Fin g → ℂ) ((Fin g → ℂ) ⧸ Λ.toAddSubgroup) := inferInstance

end

end Jacobians.Validate
