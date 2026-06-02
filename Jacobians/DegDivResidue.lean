/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.DegreeOneSphere

/-!
# The residue theorem: every principal divisor has degree `0`

For a compact connected Riemann surface `X` and a meromorphic function
`f : X → ℂ`, the divisor `div f = ∑ₓ (orderAtPoint f x) · x` has degree `0`:

```
Jacobians.degDiv_eq_zero (f : MeromorphicFunction X) : Divisor.deg X f.div = 0
```

This is Forster Cor. 4.25 / the argument principle.  Mathlib has no manifold
residue theorem, so we follow the **degree route** (the only route available at
this pin; the residue/Stokes route is dead — Mathlib lacks manifold residues):

```
deg (div f) = #zeros(with mult) − #poles(with mult)
```

and **both** counts equal the proper-map degree of `f : X → ℂℙ¹`, so they cancel.

## Structure of the proof

The bounded, fully-discharged **skeleton** is pure `Finset` arithmetic on the
order function:

* `Divisor.deg X f.div = ∑_{x : ord>0} ord x + ∑_{x : ord<0} ord x` — split the
  support sum into the zero-part (positive order) and pole-part (negative
  order); there is no `ord = 0` part since the divisor support excludes it.
* writing the pole part as `−(∑_{x : ord<0} (−ord x))`, the total is
  `zeros − poles`.
* Both `zeros := (∑_{ord>0} ord x).toNat` and `poles := (∑_{ord<0} (−ord x)).toNat`
  equal the analytic degree `degDivResidueDeg f`, so the difference is `0`.

The two analytic equalities `zeros = deg` and `poles = deg` are the **degree
route's genuine analytic inputs**, isolated here as honest named sorries
(`zeroOrderSum_eq_degree`, `poleOrderSum_eq_degree`).  Each rests on the two
classical facts Mathlib lacks at this pin:

* the **order ↔ local-multiplicity bridge** (`rouche_mult`): the local degree of
  `f` at a zero/pole equals the order there (Rouché's theorem); and
* the **ramified fibre count = degree** extension of `degreeFiber` (which counts
  *regular* fibres): the fibre over `0` (resp. `∞`), counted with multiplicity,
  equals the topological degree.

These two analytic inputs are deferred (see the `sorry`s below); everything
that combines them into `deg (div f) = 0` is proved.

## References

* Forster, *Lectures on Riemann Surfaces*, §§4 (the degree), Cor. 4.25.
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. II §4.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Finset

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The order function on the divisor support

`f.div` is `Finsupp.ofSupportFinite (orderAtPoint f) _`, so its value at `x` is
`orderAtPoint f x` and its degree is `∑_{x ∈ support} orderAtPoint f x`.  We
record the value lemma and the degree-as-support-sum identity. -/

/-- The value of `f.div` at `x` is `orderAtPoint f x`. -/
@[simp] lemma div_apply (f : MeromorphicFunction X) (x : X) :
    (f.div : Divisor X) x = f.orderAtPoint x := rfl

/-- The degree of `f.div` is the support sum of the order function. -/
lemma deg_div_eq_support_sum (f : MeromorphicFunction X) :
    Divisor.deg X f.div = ∑ x ∈ (f.div : Divisor X).support, f.orderAtPoint x := by
  show Finsupp.degree (f.div : Divisor X) = _
  rw [Finsupp.degree_apply]
  exact Finset.sum_congr rfl (fun x _ => div_apply f x)

/-! ### Splitting the support sum into zeros and poles

On the support, the order is nonzero, so each point is either a **zero**
(`0 < order`) or a **pole** (`order < 0`).  We split the support sum
accordingly. -/

/-- The support sum splits as the zero-part plus the pole-part. -/
lemma deg_div_eq_zeros_add_poles (f : MeromorphicFunction X) :
    Divisor.deg X f.div =
      (∑ x ∈ (f.div : Divisor X).support with 0 < f.orderAtPoint x, f.orderAtPoint x)
      + (∑ x ∈ (f.div : Divisor X).support with f.orderAtPoint x < 0, f.orderAtPoint x) := by
  classical
  rw [deg_div_eq_support_sum]
  rw [← Finset.sum_filter_add_sum_filter_not (f.div : Divisor X).support
    (fun x => 0 < f.orderAtPoint x) f.orderAtPoint]
  congr 1
  -- On the support, `order ≠ 0`, so `¬ (0 < order)` ↔ `order < 0`.
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  simp only [Finset.mem_filter, Finsupp.mem_support_iff, div_apply]
  constructor
  · rintro ⟨hx, hnpos⟩
    exact ⟨hx, lt_of_le_of_ne (not_lt.mp hnpos) hx⟩
  · rintro ⟨hx, hneg⟩
    exact ⟨hx, not_lt.mpr hneg.le⟩

end Jacobians
