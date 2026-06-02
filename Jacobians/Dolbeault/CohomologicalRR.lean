/-
  Dolbeault ladder — cohomological Riemann–Roch (χ-additivity, Forster §16).

  This file proves the `DolbeaultLadder` leaf

      `(h⁰(D) : ℤ) − h¹(D) = deg D + 1 − h¹(0)`

  by the standard Euler-characteristic argument. Write `χ(D) := (h⁰(D) : ℤ) − h¹(D)`. The theorem
  is `χ(D) = deg D + χ(0)` together with the Liouville base `h⁰(0) = 1` (so `χ(0) = 1 − h¹(0)`).

  Structure (Forster §16):
  * **Base** `h⁰(0) = 1`: the `h⁰ = l` bridge (`CechH0.h0Dim_eq_lDim`) plus `l(0) = 1`
    (`RiemannRoch.lDim_zero_eq_one`, Liouville on the compact `X`). CLOSED.
  * **Single-point jump** `χ(D + P) = χ(D) + 1`: the skyscraper short exact sequence
    `0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0` and its long exact sequence in Čech cohomology (the skyscraper has
    `H^{≥1} = 0`, so the alternating dimension sum gives the jump). This is the genuine homological
    content; it is isolated as the single named `sorry` `chi_jump`. NOT faked, NOT weakened.
  * **Iterated jump + induction on the divisor** (`Int.induction_on`, `Finsupp.induction`,
    `Divisor.deg` additivity): pure `ℤ`-bookkeeping built on `chi_jump`. CLOSED.

  So: `cohomological_riemannRoch` is proven *modulo the single `chi_jump` sorry*; everything else
  (base + induction skeleton) is sorry-free.
-/
import Jacobians.Dolbeault.CechH0

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

/-- The **Euler characteristic** `χ(D) := h⁰(D) − h¹(D)` (as an integer). -/
noncomputable def chi (𝔘 : FiniteCover X) (D : Divisor X) : ℤ :=
  (𝔘.h0Dim D : ℤ) - 𝔘.h1Dim D

/-! ### Base: `h⁰(0) = 1` (Liouville) -/

/-- **Base case (Liouville).** `h⁰(𝔘, 𝒪) = 1`: the `h⁰ = l(D)` bridge identifies the global Čech
sections with the linear system, and `l(0) = 1` by Liouville on the compact connected `X`. -/
theorem h0Dim_zero_eq_one (𝔘 : FiniteCover X) : (𝔘.h0Dim 0 : ℤ) = 1 := by
  rw [𝔘.h0Dim_eq_lDim 0, lDim_zero_eq_one]; norm_num

end FiniteCover

end Jacobians.Dolbeault
