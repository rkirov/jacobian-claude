import Jacobians.Meromorphic.Abel
import Mathlib.Analysis.CStarAlgebra.Classes

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Consequence of Abel's theorem + non-existence of degree-1 maps
to ℙ¹ on positive-genus surfaces**: the Abel–Jacobi image of a
two-point divisor `P - Q` is nonzero when `P ≠ Q` on a surface of
positive genus.

Classical argument: if `abelJacobi (P - Q) = 0`, then by Abel's theorem
`P - Q` is principal — some meromorphic function `f` has a simple zero
at `P` and a simple pole at `Q` and no other zeros/poles. Such an `f`
is a degree-1 map `X → ℙ¹`, hence a biholomorphism (Riemann-Hurwitz).
But then `X ≃ ℙ¹`, which has genus 0 — contradiction. -/
theorem abelJacobi_twoPoint_ne_zero
    (h : 0 < genus X) {P Q : X} (hPQ : P ≠ Q) :
    abelJacobi ⟨twoPointDivisor X P Q, twoPointDivisor_mem_degZero X P Q⟩ ≠ 0 := by
  intro h0
  -- the Abel hypothesis unfolds to a zero-period chain bounding `P − Q`.
  obtain ⟨c, hbd, hper⟩ := exists_oneChain_of_abelJacobi_eq_zero hPQ h0
  -- the engine: a meromorphic function with `div f = P − Q`.
  obtain ⟨f, hdiv, -⟩ := exists_meromorphic_of_oneChain c hper
  rw [hbd] at hdiv
  -- the order bookkeeping: `f` has a single simple pole at `Q`.
  have hord : ∀ x : X, f.orderAtPoint x = (twoPointDivisor X P Q) x := by
    intro x
    rw [show f.orderAtPoint x = (f.div) x from rfl, hdiv]
  have hQ : f.HasSingleSimplePole Q := by
    constructor
    · rw [hord Q, twoPointDivisor, Finsupp.sub_apply,
        Finsupp.single_eq_of_ne (Ne.symm hPQ), Finsupp.single_eq_same]
      ring
    · intro x hx
      rw [hord x, twoPointDivisor, Finsupp.sub_apply, Finsupp.single_eq_of_ne hx]
      rcases eq_or_ne P x with rfl | hxP
      · rw [Finsupp.single_eq_same]
        omega
      · rw [Finsupp.single_eq_of_ne (Ne.symm hxP)]
        omega
  -- the degree-one theory: `X ≃ₜ S²`, so `genus X = 0` — contradiction.
  have hsphere := nonempty_homeo_sphere_of_singleSimplePole f hQ
  have hg0 := genus_zero_of_nonempty_homeo_sphere hsphere
  omega

end Jacobians
