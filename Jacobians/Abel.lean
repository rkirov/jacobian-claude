import Jacobians.PeriodLattice
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Data.Finsupp.Weight

/-!
# Abel's theorem on a compact Riemann surface

Abel's theorem (Abel 1826, Forster §21): a divisor `D` of degree 0 on a
compact Riemann surface is principal (i.e., `D = div f` for some
meromorphic function `f`) if and only if its Abel–Jacobi image is
zero in the Jacobian.

**Scope of this file.** Mathlib does not yet have:
* meromorphic functions on a manifold (only on a normed field),
* divisors on a manifold,
* the Picard group of a compact Riemann surface.

We lay out the types and signatures at the manifold level, state
Abel's theorem as an axiomatic class `HasAbelsTheorem`, and derive
`ofCurve_inj` from it. Filling in the class is ~thousands of lines
of Mathlib-contribution-sized work (divisor theory + residue theorem
+ Riemann–Roch).

## References

* Forster, *Lectures on Riemann Surfaces*, §§17–21.
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. V §§1–4.
-/

namespace Jacobians

open scoped Manifold ContDiff

variable (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Meromorphic functions on a compact Riemann surface

A function `f : X → ℂ` is meromorphic if it is meromorphic in every
chart. In Mathlib, `Meromorphic` is defined for `𝕜 → E`; the
manifold version below composes with chart inverses. -/

/-- A meromorphic function on `X` is a map `X → ℂ` that is
meromorphic at every chart-image point of every chart. Content sorry:
the predicate + its basic theory (addition, multiplication, order
at a point). -/
def IsMeromorphic (f : X → ℂ) : Prop :=
  ∀ x : X, MeromorphicAt (f ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)

/-- The type of meromorphic functions on `X`. -/
structure MeromorphicFunction : Type _ where
  toFun : X → ℂ
  meromorphic : IsMeromorphic X toFun

/-! ### Divisors on a compact Riemann surface

A divisor is a formal ℤ-linear combination of points of `X`, with
finite support. For compact `X`, this is simply `X →₀ ℤ`. -/

/-- A divisor on `X`: a formal ℤ-linear combination of points, with
finite support. For compact `X` (as here), finite support is
automatic from the support condition. -/
abbrev Divisor : Type _ := X →₀ ℤ

/-- The degree of a divisor is the sum of its coefficients. Defines
a group homomorphism `Divisor X →+ ℤ` via `Finsupp.degree`. -/
def Divisor.deg : Divisor X →+ ℤ := Finsupp.degree

/-- The subgroup of degree-zero divisors. On a compact Riemann
surface, every principal divisor has degree 0 (Forster §4.24). -/
noncomputable def DivisorOfDegZero : AddSubgroup (Divisor X) :=
  (Divisor.deg X).ker

/-- The divisor of a meromorphic function (classical: zeros minus
poles, counted with multiplicity). Content sorry — needs order-at-a-point
theory via `meromorphicOrderAt`. -/
noncomputable def MeromorphicFunction.div (_f : MeromorphicFunction X) : Divisor X :=
  sorry

/-- The principal divisors: image of `div`. Classical fact:
every principal divisor has degree 0, so this sits inside
`DivisorOfDegZero X`. Content sorry — requires the residue theorem. -/
noncomputable def PrincipalDivisors : AddSubgroup (Divisor X) :=
  AddSubgroup.closure (Set.range (MeromorphicFunction.div X))

/-! ### Abel–Jacobi map (on divisors of degree 0)

For a divisor `D = ∑ n_i · P_i` with `∑ n_i = 0`, the Abel–Jacobi
image is `∑ n_i · ofCurve P₀ P_i` for a chosen basepoint `P₀`
(the result is independent of `P₀` because `∑ n_i = 0`).

Note this depends on `ofCurve` being a real path-integrated map, not
the current placeholder. -/

variable {X} in
/-- Abel–Jacobi map: sends a degree-0 divisor to an element of the
Jacobian. Well-defined only when `ofCurve` is the real Abel-Jacobi
map (not the placeholder `const 0`). Content sorry. -/
noncomputable def abelJacobi (_D : DivisorOfDegZero X) :
    (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup :=
  sorry

/-! ### Abel's theorem itself

**Statement** (Forster 21.4): A degree-0 divisor `D` is principal iff
its Abel–Jacobi image is zero. Equivalently: the Abel–Jacobi map
induces an isomorphism `Pic⁰(X) ≃ Jacobian X`.

Axiomatized via a typeclass so downstream consequences can be
stated. Filling in this class is the Mathlib-contribution-scale
work to formalize divisor theory + residue theorem + Abel's proof. -/

/-- **Abel's theorem** as a typeclass. Axiomatizes the key equivalence
between principality of degree-0 divisors and vanishing in the
Jacobian. Derivable (~6-12 months of work) from the residue theorem,
divisor theory, and the classical Abel–Jacobi argument. -/
class HasAbelsTheorem : Prop where
  /-- Degree-zero principal divisor ⇒ Abel–Jacobi image is zero
  (the easy direction, follows from Stokes). -/
  principal_imp_aj_zero : ∀ D : DivisorOfDegZero X,
    (D : Divisor X) ∈ PrincipalDivisors X → abelJacobi D = 0
  /-- Abel–Jacobi image is zero ⇒ divisor is principal (the hard
  direction, Abel's original theorem). -/
  aj_zero_imp_principal : ∀ D : DivisorOfDegZero X,
    abelJacobi D = 0 → (D : Divisor X) ∈ PrincipalDivisors X

/-! ### Derivation of `ofCurve_inj` from Abel's theorem

**Sketch** (Forster §21.5): if `ofCurve P Q = ofCurve P Q'` for
`Q ≠ Q'` on a surface with genus ≥ 1, then `Q - Q'` is a degree-0
divisor whose Abel–Jacobi image is zero. By Abel, `Q - Q'` is
principal: there exists a meromorphic `f` with a simple zero at `Q`
and a simple pole at `Q'`. Such an `f` defines a degree-1 map
`X → ℙ¹`, which is a biholomorphism (by Riemann-Hurwitz / the
hyperelliptic argument), making `X` of genus 0 — contradicting
`0 < genus X`.

Formalizing this fully requires:
* `ofCurve` to be the real path-integrated map.
* The Picard-group interpretation.
* Riemann-Hurwitz / degree-1 maps to ℙ¹.

These are still sorries downstream; `ofCurve_inj` in `Jacobians.lean`
remains axiomatic pending this chain. -/

end Jacobians
