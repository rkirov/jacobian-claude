/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.MeromorphicLiouville

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
* writing the pole part as `−polesCount f` where
  `polesCount f := ∑_{x : ord<0} (−ord x)`, the total is `zerosCount − polesCount`
  (`deg_div_eq_zeros_sub_poles`).

The remaining analytic content is that both counts equal a common proper-map
degree `d`, packaged as the single honest named sorry `exists_properMapDegree`
(`∃ d : ℕ, zerosCount f = d ∧ polesCount f = d`).  It rests on the two classical
facts Mathlib lacks at this pin:

* the **order ↔ local-multiplicity bridge** (`rouche_mult`): the local degree of
  `f` at a zero/pole equals the order there (Rouché's theorem); and
* the **ramified fibre count = degree** extension of `degreeFiber` (which counts
  *regular* fibres): the fibre over `0` (resp. `∞`), counted with multiplicity,
  equals the topological degree.

The trivial `f.div = 0` sub-case of `exists_properMapDegree` *is* discharged
(`exists_properMapDegree_of_div_eq_zero`), confirming the isolated statement is
genuine and true.  Everything that combines `exists_properMapDegree` into
`deg (div f) = 0` is proved.

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

/-! ### Zeros, poles, and the proper-map degree

`zerosCount f` is the number of zeros of `f` counted with multiplicity (the sum
of the *positive* orders), `polesCount f` the number of poles counted with
multiplicity (the sum of the *absolute values* of the negative orders).  Both
are `≥ 0` by construction. -/

/-- The number of **zeros** of `f`, counted with multiplicity: the sum of the
positive orders over the divisor support. -/
def zerosCount (f : MeromorphicFunction X) : ℤ :=
  ∑ x ∈ (f.div : Divisor X).support with 0 < f.orderAtPoint x, f.orderAtPoint x

/-- The number of **poles** of `f`, counted with multiplicity: the sum of the
absolute values of the negative orders over the divisor support. -/
def polesCount (f : MeromorphicFunction X) : ℤ :=
  ∑ x ∈ (f.div : Divisor X).support with f.orderAtPoint x < 0, (-f.orderAtPoint x)

/-- The pole-part of the support sum is `−polesCount`. -/
lemma poles_part_eq_neg_polesCount (f : MeromorphicFunction X) :
    (∑ x ∈ (f.div : Divisor X).support with f.orderAtPoint x < 0, f.orderAtPoint x)
      = -polesCount f := by
  rw [polesCount, ← Finset.sum_neg_distrib]
  simp

/-- `deg (div f) = zerosCount f − polesCount f`: the divisor degree is the
number of zeros minus the number of poles, each with multiplicity.  This is the
pure book-keeping identity underlying the residue theorem; it is fully proved
(no analytic input). -/
lemma deg_div_eq_zeros_sub_poles (f : MeromorphicFunction X) :
    Divisor.deg X f.div = zerosCount f - polesCount f := by
  rw [deg_div_eq_zeros_add_poles, poles_part_eq_neg_polesCount, ← sub_eq_add_neg]
  rfl

/-! ### The genuine analytic input: zeros = poles = degree (the argument principle)

The remaining mathematical content of the residue theorem is that the zero count
equals the pole count.  Via the **degree route** both equal the proper-map degree
`d` of `f : X → ℂℙ¹`:

```
zerosCount f = #f⁻¹(0)  (with mult)  =  d  =  #f⁻¹(∞)  (with mult) = polesCount f,
```

where the middle equalities are the **proper-map degree** statement (every fibre
of a non-constant holomorphic `f : X → ℂℙ¹`, counted with multiplicity, has the
same cardinality = the degree).  The two ingredients Mathlib lacks at this pin:

* **`rouche_mult`** — the order ↔ local-multiplicity bridge: for the local
  normal form `f(z) − w = (z − z₀)^k · u(z)` with `u(z₀) ≠ 0`, the local degree
  (Rouché: `#{z near z₀ : f(z) = w}` for small `w`) equals `k = orderAtPoint`.
  (Restated below as `rouche_mult`; it is the open Prop-def
  `localMultiplicity_eq_localOrder_statement` of
  `Jacobians.Discharge.Manifold.LocalNormalForm`.)
* the **ramified fibre count = degree** extension of `degreeFiber` (which counts
  only *regular* fibres) to the special fibres over `0` and `∞`.

We package the whole degree route as the single honest sorry
`exists_properMapDegree`: there is a common degree `d : ℕ` with
`zerosCount f = d` and `polesCount f = d`.  Pinning the degree to neither count
keeps both equalities genuine (the statement is *true*: in the constant /
germ-zero edge case both counts are `0`, witnessed by `d = 0`; in the
non-constant case it is Forster Cor. 4.24–4.25). -/

/-- **The order ↔ local-multiplicity bridge (Rouché).**  Restatement, in this
file, of the open Prop-def `localMultiplicity_eq_localOrder_statement`
(`Jacobians.Discharge.Manifold.LocalNormalForm`, ~line 387): for a meromorphic
function whose germ is nowhere identically zero, at a point of positive order
`k`, the topological multiplicity (cardinality of `f⁻¹{w} ∩ U` for `U` a small
neighbourhood of `x` and `w ≠ f x` close to `f x`) equals `k.natAbs`.

This is the standard Rouché-counting statement; it is **not** in Mathlib at this
pin.  It (together with the ramified fibre-count extension of `degreeFiber`) is
the analytic engine behind `exists_properMapDegree`. -/
def rouche_mult (f : MeromorphicFunction X) : Prop :=
  ∀ x : X, 0 < f.orderAtPoint x →
    ∃ (U : Set X) (V : Set ℂ), IsOpen U ∧ x ∈ U ∧ IsOpen V ∧ f.holoRepr x ∈ V ∧
      ∀ w ∈ V, w ≠ f.holoRepr x →
        ({y ∈ U | f.holoRepr y = w} : Set X).ncard = (f.orderAtPoint x).natAbs

/-! ### Nonnegativity of the two counts, and the reduction to `zerosCount = polesCount`

Both `zerosCount f` and `polesCount f` are sums of *nonnegative* integers (the
positive orders, resp. the absolute values of the negative orders), so both are
`≥ 0`.  Consequently the existential `exists_properMapDegree` (a single `d : ℕ`
with `zerosCount f = d = polesCount f`) is **equivalent** to the bare equality
`zerosCount f = polesCount f`: given the equality, both sides are a common
nonnegative integer, which is the cast of some `d : ℕ`.  This isolates the entire
analytic wall as the **argument-principle equality** `zerosCount f = polesCount f`
(Forster Cor. 4.25), stripping away the `∃ d : ℕ` packaging. -/

/-- `zerosCount f ≥ 0`: it is a sum of positive orders. -/
lemma zerosCount_nonneg (f : MeromorphicFunction X) : 0 ≤ zerosCount f := by
  rw [zerosCount]
  apply Finset.sum_nonneg
  intro x hx
  rw [Finset.mem_filter] at hx
  exact hx.2.le

/-- `polesCount f ≥ 0`: it is a sum of absolute values of negative orders. -/
lemma polesCount_nonneg (f : MeromorphicFunction X) : 0 ≤ polesCount f := by
  rw [polesCount]
  apply Finset.sum_nonneg
  intro x hx
  rw [Finset.mem_filter] at hx
  have := hx.2
  omega

/-- **Reduction of `exists_properMapDegree` to the argument-principle equality.**
Since both counts are nonnegative (`zerosCount_nonneg`, `polesCount_nonneg`), the
existence of a common natural-number degree `d` with `zerosCount f = d` and
`polesCount f = d` is exactly the equality `zerosCount f = polesCount f`.  The
common `d` is the natural number whose cast is the (nonnegative) shared value.

This is the bridge that turns the full analytic content of the residue theorem
into the single classical statement "the number of zeros equals the number of
poles" (the argument principle), with the `∃ d : ℕ` book-keeping discharged. -/
theorem exists_properMapDegree_of_zerosCount_eq_polesCount (f : MeromorphicFunction X)
    (h : zerosCount f = polesCount f) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) := by
  obtain ⟨d, hd⟩ := Int.eq_ofNat_of_zero_le (zerosCount_nonneg f)
  exact ⟨d, hd, h ▸ hd⟩

/-- **Analytic input (the argument principle): both counts equal the degree.**
There is a common proper-map degree `d : ℕ` of `f : X → ℂℙ¹` for which the
number of zeros and the number of poles (each with multiplicity) both equal `d`:

```
zerosCount f = d = polesCount f.
```

This is the residue theorem's full analytic content.  In the constant /
germ-zero edge case `f.div = 0`, both counts vanish, so `d = 0` works (this part
*is* provable, see `exists_properMapDegree_of_div_eq_zero`); the non-constant
case is Forster Cor. 4.24–4.25 via the degree route.

**Status: honest named sorry.**  By `exists_properMapDegree_of_zerosCount_eq_polesCount`
this is equivalent to the bare argument-principle equality `zerosCount f =
polesCount f`.  That equality is what Mathlib lacks at this pin: it needs
**conservation of number** — the sum of local multiplicities over *every* fibre of
a non-constant holomorphic `f : X → ℂℙ¹` is the same constant `d` (so both the
zero-fibre sum `zerosCount f` and the pole-fibre sum `polesCount f` equal `d`).
The per-point ingredient (`rouche_mult`, the order ↔ local-multiplicity bridge)
*is* available (`RoucheBridge.localMultiplicity_eq_localOrder_count_of_apply_eq_zero`),
and the *regular*-fibre degree is well-defined (`degreeFiber_eq_card_of_regularWitness`);
the missing step is the global summation identifying a *ramified* fibre's
multiplicity-sum with the regular degree.  Discharging this single statement
discharges the residue theorem. -/
theorem exists_properMapDegree (f : MeromorphicFunction X) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) := sorry

/-- The degree-route conclusion in the trivial case `f.div = 0` (constant or
germ-zero `f`): both counts vanish, witnessed by `d = 0`.  This sub-case of
`exists_properMapDegree` *is* provable with no analytic input — it shows the
isolated statement is a genuine (true) one, not vacuous. -/
theorem exists_properMapDegree_of_div_eq_zero (f : MeromorphicFunction X)
    (h : (f.div : Divisor X) = 0) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) := by
  refine ⟨0, ?_, ?_⟩
  · simp only [zerosCount, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter, h] at hx
    simp at hx
  · simp only [polesCount, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_filter, h] at hx
    simp at hx

/-! ### The residue theorem -/

/-- **The residue theorem.**  Every principal divisor on a compact connected
Riemann surface has degree `0`:

```
deg (div f) = zerosCount f − polesCount f = deg − deg = 0.
```

The book-keeping (`deg_div_eq_zeros_sub_poles`: `deg = zerosCount − polesCount`)
is fully proved; the single analytic input is `exists_properMapDegree` (the
argument principle / degree route: both counts equal a common degree `d`), so
the difference `d − d` is `0`. -/
theorem degDiv_eq_zero (f : MeromorphicFunction X) :
    Divisor.deg X f.div = 0 := by
  obtain ⟨d, hz, hp⟩ := exists_properMapDegree f
  rw [deg_div_eq_zeros_sub_poles, hz, hp, sub_self]

end Jacobians
