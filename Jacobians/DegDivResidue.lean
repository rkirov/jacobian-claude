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

/-- **The proper-map degree of `f : X → ℂℙ¹`.**  Classically (Forster §4) this
is the common value of the fibre count over *any* value, with multiplicity;
in particular it equals both `zerosCount f` (fibre over `0`) and `polesCount f`
(fibre over `∞`).  We *define* it as `polesCount f` — the number of poles with
multiplicity — which is one of the two fibre counts; the content of the residue
theorem is precisely that the *other* fibre count `zerosCount f` agrees with it
(`zeroOrderSum_eq_degree` below). -/
def degDivResidueDeg (f : MeromorphicFunction X) : ℤ := polesCount f

/-- **Analytic input (definitional anchor): poles = degree.**  The number of
poles with multiplicity equals the proper-map degree.  This is the fibre count
of `f : X → ℂℙ¹` over `∞`, with multiplicity; we have pinned `degDivResidueDeg`
to it, so this direction is definitional.

In the full degree route this is the statement that the ramified-with-
multiplicity fibre count over `∞` equals the topological degree
`ContMDiff.degree (f.toSphere …)` — see the file header and the
`rouche_mult` / ramified-count discussion. -/
lemma poleOrderSum_eq_degree (f : MeromorphicFunction X) :
    polesCount f = degDivResidueDeg f := rfl

/-! ### The genuine analytic input: zeros = poles (the argument principle)

The single remaining mathematical content of the residue theorem is that the
zero count equals the pole count.  Via the degree route this is

```
zerosCount f = #f⁻¹(0)  (with mult)  =  deg f  =  #f⁻¹(∞)  (with mult) = polesCount f,
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

We isolate the whole package as the single honest sorry `zeroOrderSum_eq_degree`.
-/

/-- **The order ↔ local-multiplicity bridge (Rouché).**  Restatement, in this
file, of the open Prop-def `localMultiplicity_eq_localOrder_statement`
(`Jacobians.Discharge.Manifold.LocalNormalForm`, ~line 387): for a meromorphic
function whose germ is nowhere identically zero, at a point of positive order
`k`, the topological multiplicity (cardinality of `f⁻¹{w} ∩ U` for `U` a small
neighbourhood of `x` and `w ≠ f x` close to `f x`) equals `k.natAbs`.

This is the standard Rouché-counting statement; it is **not** in Mathlib at this
pin.  It (together with the ramified fibre-count extension of `degreeFiber`) is
the analytic engine behind `zeroOrderSum_eq_degree`. -/
def rouche_mult (f : MeromorphicFunction X) : Prop :=
  ∀ x : X, 0 < f.orderAtPoint x →
    ∃ (U : Set X) (V : Set ℂ), IsOpen U ∧ x ∈ U ∧ IsOpen V ∧ f.holoRepr x ∈ V ∧
      ∀ w ∈ V, w ≠ f.holoRepr x →
        ({y ∈ U | f.holoRepr y = w} : Set X).ncard = (f.orderAtPoint x).natAbs

/-- **Analytic input (the argument principle): zeros = degree.**  The number of
zeros of `f`, counted with multiplicity, equals the proper-map degree of
`f : X → ℂℙ¹`.  Combined with `poleOrderSum_eq_degree` (poles = degree) this is
the residue theorem.

**Status: honest named sorry.**  This is the genuine analytic content the degree
route delivers but Mathlib lacks at this pin: it bundles `rouche_mult` (the
order ↔ local-multiplicity bridge) with the ramified-fibre-count = degree
extension of `degreeFiber`.  Applied at the value `0` it gives
`zerosCount = deg`; applied (via `1/f`) at `∞` it gives `polesCount = deg`; here
`degDivResidueDeg` is pinned to the latter, so this lemma carries exactly the
`zeros = poles` content. -/
theorem zeroOrderSum_eq_degree (f : MeromorphicFunction X) :
    zerosCount f = degDivResidueDeg f := sorry

/-! ### The residue theorem -/

/-- **The residue theorem.**  Every principal divisor on a compact connected
Riemann surface has degree `0`:

```
deg (div f) = zerosCount f − polesCount f = deg − deg = 0.
```

The book-keeping (`deg_div_eq_zeros_sub_poles`) is fully proved; the two
analytic equalities `zerosCount = deg` and `polesCount = deg` are
`zeroOrderSum_eq_degree` (the genuine sorry: argument principle / degree route)
and `poleOrderSum_eq_degree` (definitional anchor). -/
theorem degDiv_eq_zero (f : MeromorphicFunction X) :
    Divisor.deg X f.div = 0 := by
  rw [deg_div_eq_zeros_sub_poles, zeroOrderSum_eq_degree, poleOrderSum_eq_degree,
    sub_self]

end Jacobians
