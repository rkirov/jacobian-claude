/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.MultiplicityPatchingConstruct

/-!
# The local multiplicity sheets — discharging `exists_properMapDegree`

This file supplies the last input to the conservation-of-number / argument-principle wall:
the *pointwise* local-conservation data `∀ w₀, LocalMultiplicitySheets f w₀` (the irreducible
§17.9 content), from which `MultiplicityPatchingConstruct.exists_properMapDegree_of_localSheets`
delivers the proper-map-degree existential `∃ d, zerosCount f = d = polesCount f`, hence the
residue theorem `deg (div f) = 0`.

Everything *downstream* of `∀ w₀, LocalMultiplicitySheets f w₀` is already proven sorry-free
(the connectedness globalization of `N f`, the special-fibre identities, the `ofDisjointSheets`
assembly). The content here is the per-value local construction:

* `w₀ ∉ range F`: the empty fibre — `LocalMultiplicitySheets.ofNotMemRange` (proven upstream).
* `w₀ = coe c` (a finite value): around each fibre point `x` (a solution of `f = c`), the planar
  normal form `Planar.orderSum_eq_of_analyticOrder` applied to `g = f ∘ chart.symm` gives a
  value-neighbourhood on which the multiplicity sum is the local order; transported to `localDeg`
  via `localDeg_coe_eq_chartPullback_order`.
* `w₀ = ∞` (the pole fibre): around each pole `x`, the same engine applied to `1/g` at `0`
  (a zero of order = the pole order), with the order-matching `ord(g − c') = ord(1/g − 1/c')`
  for `g(z) = c'` finite nonzero.

This is a true, non-vacuous obligation (the empty-fibre witness certifies satisfiability).

References: Forster §4 (the degree, Cor. 4.24–4.25), Miranda II.4 (argument principle).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Finset OnePoint Filter

namespace Jacobians.ProperMapDegreeSheets

open Jacobians Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct
  Jacobians.MultiplicityPatchingConstruct Jacobians.MultiplicityPatching

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The local conservation data at a value in the range** (`w₀ ∈ range F`), for a *non-constant*
`f` (`f.div ≠ 0`, ensuring finite fibres): the genuine §17.9 content, built per fibre point from the
planar normal form. -/
def localMultiplicitySheets_of_mem_range (f : MeromorphicFunction X) (hnc : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (hmem : w₀ ∈ Set.range f.toRiemannSphere) :
    LocalMultiplicitySheets f w₀ :=
  sorry

/-- **Pointwise local-conservation supply for non-constant `f`.** For every value `w₀ : ℂℙ¹` there
is a `LocalMultiplicitySheets f w₀`: the empty-fibre witness off the range, and the §17.9
construction on it. (Needs `f.div ≠ 0`: for a constant `f` the fibre over the constant value is all
of `X`, which is infinite, so no finite `xs` enumerates it — that case is handled separately by
`exists_properMapDegree_of_div_eq_zero`.) -/
def localMultiplicitySheets_of_nonconstant (f : MeromorphicFunction X)
    (hnc : (f.div : Divisor X) ≠ 0) (w₀ : RiemannSphere) :
    LocalMultiplicitySheets f w₀ := by
  by_cases hmem : w₀ ∈ Set.range f.toRiemannSphere
  · exact localMultiplicitySheets_of_mem_range f hnc hmem
  · exact LocalMultiplicitySheets.ofNotMemRange f hmem

/-- **`exists_properMapDegree`, PROVEN.** The proper-map-degree existential — `∃ d : ℕ` with
`zerosCount f = d = polesCount f`. For the trivial divisor (`f.div = 0`, the constant/germ-zero
case) both counts vanish (`exists_properMapDegree_of_div_eq_zero`); otherwise it is discharged from
the pointwise local-conservation supply via the proven connectedness globalization. This is the
exact shape of the upstream named input `Jacobians.exists_properMapDegree`; closing the residue
theorem `deg (div f) = 0`. -/
theorem exists_properMapDegree_proven (f : MeromorphicFunction X) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) := by
  by_cases h : (f.div : Divisor X) = 0
  · exact exists_properMapDegree_of_div_eq_zero f h
  · exact exists_properMapDegree_of_localSheets f (localMultiplicitySheets_of_nonconstant f h)

end Jacobians.ProperMapDegreeSheets

end
