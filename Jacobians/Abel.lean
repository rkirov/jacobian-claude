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

/-! ### Basic degree computations -/

@[simp]
theorem Divisor.deg_zero : Divisor.deg X 0 = 0 :=
  map_zero _

@[simp]
theorem Divisor.deg_add (D D' : Divisor X) :
    Divisor.deg X (D + D') = Divisor.deg X D + Divisor.deg X D' :=
  map_add _ _ _

@[simp]
theorem Divisor.deg_neg (D : Divisor X) :
    Divisor.deg X (-D) = -Divisor.deg X D :=
  map_neg _ _

@[simp]
theorem Divisor.deg_sub (D D' : Divisor X) :
    Divisor.deg X (D - D') = Divisor.deg X D - Divisor.deg X D' :=
  map_sub _ _ _

@[simp]
theorem Divisor.deg_single (P : X) (n : ℤ) :
    Divisor.deg X (Finsupp.single P n) = n := by
  show Finsupp.degree (Finsupp.single P n) = n
  by_cases hn : n = 0
  · simp [hn]
  · simp [Finsupp.degree_apply, Finsupp.support_single_ne_zero _ hn,
      Finsupp.single_eq_same]

/-! ### Two-point divisor `P - Q`

The fundamental degree-0 divisor associated with two points. Every
divisor of degree 0 decomposes as a ℤ-linear combination of such
two-point divisors (choose any basepoint and subtract). -/

/-- The divisor `P - Q` (formal difference of points, as a
degree-0 divisor via `Finsupp.single`). -/
noncomputable def twoPointDivisor (P Q : X) : Divisor X :=
  Finsupp.single P 1 - Finsupp.single Q 1

@[simp]
theorem twoPointDivisor_deg (P Q : X) :
    Divisor.deg X (twoPointDivisor X P Q) = 0 := by
  simp [twoPointDivisor]

theorem twoPointDivisor_mem_degZero (P Q : X) :
    twoPointDivisor X P Q ∈ DivisorOfDegZero X := by
  show Divisor.deg X (twoPointDivisor X P Q) = 0
  exact twoPointDivisor_deg X P Q

@[simp]
theorem twoPointDivisor_self (P : X) : twoPointDivisor X P P = 0 := by
  simp [twoPointDivisor]

/-- The divisor of a meromorphic function: classical construction
`div f = (zeros of f) - (poles of f)` with multiplicities via
`meromorphicOrderAt`.

**Current implementation**: placeholder `div f := 0` (trivially
finitely-supported). A real implementation requires:
1. For each point `x`, compute `meromorphicOrderAt (f ∘ chart⁻¹) (chart x)`
   and cast to ℤ via `.untop₀`.
2. Prove the order function is finitely supported on compact `X`
   (classical: zeros of a nonzero meromorphic function are isolated;
   a compact space has finitely many isolated points per chart).

With the placeholder, `PrincipalDivisors X = {0}`, making
`HasAbelsTheorem` unsatisfiable for positive-genus surfaces (same as
`abelJacobi ≡ 0`). Real instances require real divisor theory. -/
noncomputable def MeromorphicFunction.div (_f : MeromorphicFunction X) : Divisor X :=
  0

/-- The principal divisors: image of `div`. Classical fact:
every principal divisor has degree 0, so this sits inside
`DivisorOfDegZero X`. Content sorry — requires the residue theorem. -/
noncomputable def PrincipalDivisors : AddSubgroup (Divisor X) :=
  AddSubgroup.closure (Set.range (MeromorphicFunction.div X))

/-- The zero function is trivially meromorphic: chart pullbacks of
constant functions are constant, hence meromorphic. -/
theorem IsMeromorphic.zero : IsMeromorphic X (fun _ => 0) := by
  intro x
  show MeromorphicAt (fun _ => (0 : ℂ)) ((chartAt (H := ℂ) x) x)
  exact MeromorphicAt.const 0 _

/-- With the current placeholder `MeromorphicFunction.div ≡ 0`, the
principal divisors collapse to the trivial subgroup `{0}`. This is
consistent with `abelJacobi ≡ 0`: at the placeholder level,
`HasAbelsTheorem` reduces to "every degree-0 divisor equals 0",
which is false for positive-genus surfaces (reflecting that real
instances require real `ofCurve`). -/
theorem PrincipalDivisors_eq_bot : PrincipalDivisors X = ⊥ := by
  show AddSubgroup.closure (Set.range (MeromorphicFunction.div X)) = ⊥
  have h_range : Set.range (MeromorphicFunction.div X) = {0} := by
    ext d
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨f, rfl⟩
      rfl
    · rintro rfl
      exact ⟨⟨fun _ => 0, IsMeromorphic.zero X⟩, rfl⟩
  rw [h_range, AddSubgroup.closure_singleton_zero]

/-! ### Abel–Jacobi map (on divisors of degree 0)

For a divisor `D = ∑ n_i · P_i` with `∑ n_i = 0`, the Abel–Jacobi
image is `∑ n_i · ofCurve P₀ P_i` for a chosen basepoint `P₀`
(the result is independent of `P₀` because `∑ n_i = 0`).

Note this depends on `ofCurve` being a real path-integrated map, not
the current placeholder. -/

variable {X} in
/-- Abel–Jacobi map: sends a degree-0 divisor `D = ∑ n_i · P_i` to
`∑ n_i · [ofCurve basepoint P_i]` in the Jacobian `(Fin gX → ℂ) ⧸ lattice`.

**Well-definedness** (independence of basepoint): uses `∑ n_i = 0`
to absorb the basepoint choice. For any two basepoints P₀, P₀':
`AJ_{P₀} D - AJ_{P₀'} D = (∑ n_i) · [ofCurve P₀' P₀] = 0` (since ∑ n_i = 0).

**Current implementation**: placeholder zero map, consistent with
the placeholder `Jacobian.ofCurve := fun _ _ => 0`. A real
implementation requires:
1. A real `ofCurve` via path integration (Phase 3).
2. Basepoint-independence proof (uses the degree-0 condition).

With the current placeholder, `abelJacobi ≡ 0`, so
`HasAbelsTheorem.aj_zero_imp_principal` would require every
degree-0 divisor to be principal — false for genus ≥ 1. This
inconsistency is fine as long as the axioms aren't instantiated;
real instances await real `ofCurve`. -/
noncomputable def abelJacobi (_D : DivisorOfDegZero X) :
    (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup :=
  0

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

/-! ### Consequence: two-point divisors on positive-genus surfaces

For `X` of genus ≥ 1, the divisor `P - Q` with `P ≠ Q` is NOT
principal (Forster §21.5 / Miranda Ch. V §2.8). The classical
argument:

A principal divisor `P - Q` with `P ≠ Q` means some meromorphic
function `f` has a simple zero at `P` and a simple pole at `Q` and
no other zeros/poles. Such an `f` is a degree-1 map `X → ℙ¹`, which
must be a biholomorphism (by Riemann-Hurwitz: deg-1 covers are
isomorphisms). But then `X ≃ ℙ¹`, which has genus 0 — contradiction.

Axiomatized as a typeclass field `twoPointDivisor_not_principal_of_pos_genus`,
alongside Abel's theorem itself. This is the piece that, combined
with Abel, implies `abelJacobi (P - Q) ≠ 0`, the lemma needed for
`ofCurve_inj`. -/

/-- **Non-principality of two-point divisors on positive-genus surfaces.**
Axiomatized; the proof is classical (Riemann-Hurwitz + genus-0
characterization of ℙ¹). -/
class NoDegreeOneDivisorsToPP1 : Prop where
  twoPoint_not_principal : 0 < genus X →
    ∀ {P Q : X}, P ≠ Q → twoPointDivisor X P Q ∉ PrincipalDivisors X

variable {X} in
/-- **Consequence of Abel's theorem + non-existence of degree-1 maps
to ℙ¹ on positive-genus surfaces**: the Abel–Jacobi image of a
two-point divisor `P - Q` is nonzero when `P ≠ Q` on a surface of
positive genus. -/
theorem abelJacobi_twoPoint_ne_zero [HasAbelsTheorem X] [NoDegreeOneDivisorsToPP1 X]
    (h : 0 < genus X) {P Q : X} (hPQ : P ≠ Q) :
    abelJacobi ⟨twoPointDivisor X P Q, twoPointDivisor_mem_degZero X P Q⟩ ≠ 0 := by
  intro h_aj
  have h_principal := HasAbelsTheorem.aj_zero_imp_principal _ h_aj
  -- h_principal : twoPointDivisor X P Q ∈ PrincipalDivisors X
  exact NoDegreeOneDivisorsToPP1.twoPoint_not_principal h hPQ h_principal

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
