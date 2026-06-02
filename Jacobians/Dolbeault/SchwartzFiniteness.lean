/-
  The abstract Schwartz / Riesz–Schauder finiteness lemma (Forster *Lectures on Riemann Surfaces*
  Lemma 14.8) — the functional-analysis core of the `H¹(X, 𝒪_D)` finiteness theorem (14.9).

  Standalone (Banach-space functional analysis; no manifold / Čech dependency). Mathlib has the
  spectral Fredholm alternative (`IsCompactOperator.hasEigenvalue_or_mem_resolventSet`) and Riesz's
  lemma but NOT this packaged "compact perturbation of a surjection has finite-codimensional image".
-/
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.FredholmAlternative
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

namespace Jacobians.SchwartzFiniteness

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- **Schwartz finiteness (Forster 14.8).** A compact perturbation of a surjection between Banach
spaces has finite-codimensional image: if `A : E →L[ℂ] F` is surjective and `K : E →L[ℂ] F` is a
compact operator, then `F ⧸ range (A + K)` is finite-dimensional. (`K = 0` ⟹ codim 0; `A = id` ⟹
Riesz–Schauder for `1 + K`.) This is the functional-analysis core of Forster 14.9. -/
theorem finiteDimensional_quotient_range_add_compact
    (A : E →L[ℂ] F) (hA : Function.Surjective A)
    (K : E →L[ℂ] F) (hK : IsCompactOperator K) :
    FiniteDimensional ℂ (F ⧸ LinearMap.range (A + K).toLinearMap) := by
  sorry

end Jacobians.SchwartzFiniteness
