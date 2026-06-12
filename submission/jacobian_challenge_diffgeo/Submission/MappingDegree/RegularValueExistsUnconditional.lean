/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Submission.MappingDegree.ClopennessOfLocallyConstDischarge



/-! # Unconditional discharge of `Degree.regular_value_exists_statement`

`Manifold/Degree.lean` reduced `regular_value_exists_statement` to
`fibres_finite_statement` via `regular_value_exists_of_fibres_finite`:
given that *every* fibre is finite, non-emptiness of `Y` (from
`ConnectedSpace Y`) suffices to package any `y : Y` as a
`RegularValueWitness`.

`Manifold/ClopennessOfLocallyConstDischarge.lean` proved
`ClopennessOfLocallyConstHypothesis X Y` unconditionally. Composing with
`fibres_finite_statement_holds_of_clopennessOfLocallyConst` yields
`fibres_finite_statement X Y`, hence `regular_value_exists_statement X Y`,
unconditionally.  The composition is the entire content of this file. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge
namespace ContMDiff
namespace Degree

universe u v

/-- **Existence of a regular-value witness**
(`regular_value_exists_statement`, with no remaining hypotheses). For
compact connected complex 1-manifolds `X`, `Y`, every non-constant `C^ω`
map `f : X → Y` admits a regular value witness.

The proof composes:

* `clopennessOfLocallyConst_holds`: the locally-constant locus of any
  `C^ω` map onto a fixed value is closed (chart-local identity theorem).
* `fibres_finite_statement_holds_of_clopennessOfLocallyConst`:
  fibres-finite reduces to clopen-ness of the locally-constant locus.
* `regular_value_exists_of_fibres_finite`: regular-value-exists
  reduces to fibres-finite via "pick any `y : Y`". -/
theorem exists_regularValueWitness
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] :
    ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
      ¬ Jacobians.Discharge.IsConstantMap f → Nonempty (RegularValueWitness f) := by
  -- Fibres-finite with no remaining hypotheses.
  have h_fib :
      ∀ (f : X → Y), ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f →
        ¬ Jacobians.Discharge.IsConstantMap f → ∀ y : Y, (f ⁻¹' {y}).Finite :=
    fibres_finite_statement_holds_of_clopennessOfLocallyConst
      clopennessOfLocallyConst_holds
  -- Reduce regular-value-exists to fibres-finite.
  exact regular_value_exists_of_fibres_finite h_fib

end Degree
end ContMDiff
end Jacobians.Discharge
