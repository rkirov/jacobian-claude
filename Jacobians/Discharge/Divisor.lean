/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.Discharge.Manifold.MeromorphicAt
import Mathlib.Topology.LocallyFinsupp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.GroupTheory.QuotientGroup.Defs

set_option autoImplicit true


/-! # Divisors on a complex manifold

This file scaffolds the divisor-class construction of the Jacobian for a
compact complex manifold `X` modelled on `ℂ`. The chain
`Div → Div⁰ → Pic⁰` is in place at the *type/group* level. The principal
subgroup `PrincDiv X` is set to `⊥` as a deliberate placeholder (see its
docstring); the analytic content (chart-independence of meromorphic order,
local finiteness of the order divisor, residue theorem on a compact Riemann
surface) is deferred by `MeromorphicAt.lean` and downstream files.

## What's in this file

* `Jacobians.Discharge.Div X` — the additive group of divisors on `X`,
  defined as `Function.locallyFinsuppWithin (Set.univ : Set X) ℤ` (an
  abbreviation; the `AddCommGroup` instance is inherited).
* `Jacobians.Discharge.Div.supportFinset D` — the support as a `Finset X`,
  using `Function.locallyFinsuppWithin.finiteSupport` (which requires
  `[T2Space X] [CompactSpace X]`).
* `Jacobians.Discharge.Div.degree D` — `∑ x ∈ D.supportFinset, D x`.
* `Jacobians.Discharge.Div.degree_zero` — `degree (0 : Div X) = 0`.
* `Jacobians.Discharge.Div.degree_add` — additivity of the degree.
* `Jacobians.Discharge.Div.degreeHom : Div X →+ ℤ` — the degree as a group
  homomorphism.
* `Jacobians.Discharge.Div.degree_neg` / `Div.degree_sub` — corollaries
  (degree commutes with `-` and `-`).
* `Jacobians.Discharge.Div0 X := degreeHom.ker` — degree-zero subgroup.
* `Jacobians.Discharge.PrincDiv X : AddSubgroup (Div X)` — placeholder `⊥`
  (see its docstring for the missing analytic input).
* `Jacobians.Discharge.Pic0 X := Div0 X ⧸ (PrincDiv X).addSubgroupOf (Div0 X)`
  — the Picard group of degree-zero divisors as an `AddCommGroup`.

## Open for follow-up (not in this commit)

* The honest definition of `PrincDiv X` (= principal divisors of non-zero
  global meromorphic functions). Requires (i) chart-independence of
  `mmeromorphicOrderAt` (deferred by `MeromorphicAt.lean`), (ii) local
  finiteness of the order divisor of a meromorphic function, (iii) the
  residue theorem on a compact Riemann surface (degree-zero property).
-/

namespace Jacobians.Discharge

/-! ### Divisors -/

/-- A *divisor* on a topological space `X` is a `ℤ`-valued function on `X`
whose support is locally finite. We use the mathlib carrier
`Function.locallyFinsuppWithin (Set.univ : Set X) ℤ`. The `AddCommGroup`
instance is inherited from mathlib. -/
abbrev Div (X : Type*) [TopologicalSpace X] : Type _ :=
  Function.locallyFinsuppWithin (Set.univ : Set X) ℤ

/-- The `AddCommGroup` structure on `Div X` is the one provided by
`Function.locallyFinsuppWithin`. -/
example (X : Type*) [TopologicalSpace X] : AddCommGroup (Div X) := inferInstance

/-! ### Degree of a divisor on a compact space -/

namespace Div

variable {X : Type*} [TopologicalSpace X]

/-- On a compact Hausdorff space, the support of a divisor (as a `Set X`) is
finite, so admits a `Finset` representative. -/
noncomputable def supportFinset [T2Space X] [CompactSpace X] (D : Div X) :
    Finset X :=
  (D.finiteSupport isCompact_univ).toFinset

/-- Membership in `supportFinset` is membership in the function-support. -/
lemma mem_supportFinset [T2Space X] [CompactSpace X] {D : Div X} {x : X} :
    x ∈ D.supportFinset ↔ (D : X → ℤ) x ≠ 0 := by
  classical
  unfold supportFinset
  rw [Set.Finite.mem_toFinset]
  exact Function.mem_support

/-- If `x` is outside `D.supportFinset` then `D x = 0`. -/
lemma apply_eq_zero_of_notMem_supportFinset [T2Space X] [CompactSpace X]
    {D : Div X} {x : X} (hx : x ∉ D.supportFinset) : (D : X → ℤ) x = 0 := by
  by_contra h
  exact hx (mem_supportFinset.mpr h)

/-- The *degree* of a divisor on a compact Hausdorff space is the integer
sum of its values over its (finite) support. -/
noncomputable def degree [T2Space X] [CompactSpace X] (D : Div X) : ℤ :=
  ∑ x ∈ D.supportFinset, D x

/-- The degree can be computed by summing over any finset that contains the
support. Values outside the support are zero, so they contribute nothing. -/
lemma degree_eq_sum_of_supportFinset_subset [T2Space X] [CompactSpace X]
    {D : Div X} {S : Finset X} (hS : D.supportFinset ⊆ S) :
    degree D = ∑ x ∈ S, D x := by
  classical
  unfold degree
  refine Finset.sum_subset hS ?_
  intro x _ hxS
  exact apply_eq_zero_of_notMem_supportFinset hxS

@[simp] lemma degree_zero [T2Space X] [CompactSpace X] :
    degree (0 : Div X) = 0 := by
  classical
  -- The support of `0 : Div X` is empty, so `supportFinset` is empty,
  -- and the sum over an empty finset is `0`.
  unfold degree supportFinset
  have hsupp : ((0 : Div X) : X → ℤ).support = (∅ : Set X) := by
    ext x; simp
  have hempty : (Function.locallyFinsuppWithin.finiteSupport (0 : Div X)
                  isCompact_univ).toFinset = (∅ : Finset X) := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro x hx
    have hx' : x ∈ ((0 : Div X) : X → ℤ).support := by
      simpa using (Set.Finite.mem_toFinset _).1 hx
    have : x ∈ (∅ : Set X) := by simpa [hsupp] using hx'
    exact this.elim
  simp [hempty]

/-- Additivity of the degree. We sum each of the three divisors over the
common finset `S := supportFinset (D₁+D₂) ∪ supportFinset D₁ ∪
supportFinset D₂`, then use pointwise additivity (from
`Function.locallyFinsuppWithin.coe_add` plus `Pi.add_apply`) and
`Finset.sum_add_distrib`. -/
lemma degree_add [T2Space X] [CompactSpace X] (D₁ D₂ : Div X) :
    degree (D₁ + D₂) = degree D₁ + degree D₂ := by
  classical
  set S : Finset X :=
    (D₁ + D₂).supportFinset ∪ D₁.supportFinset ∪ D₂.supportFinset with hS_def
  have h12 : (D₁ + D₂).supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have h1 : D₁.supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have h2 : D₂.supportFinset ⊆ S := by
    intro x hx
    exact Finset.mem_union_right _ hx
  have e12 : degree (D₁ + D₂) = ∑ x ∈ S, ((D₁ + D₂ : Div X) : X → ℤ) x :=
    degree_eq_sum_of_supportFinset_subset h12
  have e1 : degree D₁ = ∑ x ∈ S, (D₁ : X → ℤ) x :=
    degree_eq_sum_of_supportFinset_subset h1
  have e2 : degree D₂ = ∑ x ∈ S, (D₂ : X → ℤ) x :=
    degree_eq_sum_of_supportFinset_subset h2
  rw [e12, e1, e2]
  have hpt : ∀ x : X, ((D₁ + D₂ : Div X) : X → ℤ) x
      = (D₁ : X → ℤ) x + (D₂ : X → ℤ) x := by
    intro x
    simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  simp_rw [hpt]
  exact Finset.sum_add_distrib

/-- The *degree* as an additive group homomorphism `Div X →+ ℤ`. -/
noncomputable def degreeHom [T2Space X] [CompactSpace X] : Div X →+ ℤ where
  toFun := degree
  map_zero' := degree_zero
  map_add' := degree_add

@[simp] lemma degreeHom_apply [T2Space X] [CompactSpace X] (D : Div X) :
    degreeHom D = degree D := rfl

/-- The degree of `-D` is `-D.degree`. Immediate consequence of
`degreeHom` being an additive group homomorphism. -/
@[simp] lemma degree_neg [T2Space X] [CompactSpace X] (D : Div X) :
    degree (-D) = - degree D := by
  have h : degree (-D) = degreeHom (X := X) (-D) := rfl
  rw [h, map_neg]
  simp [degreeHom_apply]

/-- The degree of `D₁ - D₂` is `D₁.degree - D₂.degree`. Immediate
consequence of `degreeHom` being an additive group homomorphism. -/
@[simp] lemma degree_sub [T2Space X] [CompactSpace X] (D₁ D₂ : Div X) :
    degree (D₁ - D₂) = degree D₁ - degree D₂ := by
  have h : degree (D₁ - D₂) = degreeHom (X := X) (D₁ - D₂) := rfl
  rw [h, map_sub]
  simp [degreeHom_apply]

end Div

/-! ### Degree-zero divisors and the (placeholder) Picard group -/

/-- The subgroup of *degree-zero* divisors on a compact Hausdorff space `X`,
i.e. the kernel of `Div.degreeHom`. -/
noncomputable def Div0 (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] : AddSubgroup (Div X) :=
  (Div.degreeHom (X := X)).ker

/-! ### `PrincDiv` and `Pic0` (moved to `Divisor/PrincipalDivisorRange.lean`)

ZZ256 (2026-05-11). `PrincDiv X` and `Pic0 X` are defined honestly in
`Divisor/PrincipalDivisorRange.lean`. They live there because the honest
`PrincDiv X` references `principalDivisorMap`, which would import-cycle
through this file. The signatures gain `[ChartedSpace ℂ X]
[IsManifold (𝓘(ℂ, ℂ)) ω X]` over the prior topological signatures.
-/

end Jacobians.Discharge
