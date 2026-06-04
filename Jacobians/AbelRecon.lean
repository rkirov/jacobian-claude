/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.DegreeOneSphere

/-!
# Recon + scaffolding for the #3 Abel wall

The target is `Jacobians.abelJacobi_twoPoint_ne_zero` (`Jacobians/Abel.lean`):

> For `0 < genus X` and `P ≠ Q`, the Abel–Jacobi image of the two-point divisor
> `P − Q` is nonzero in the Jacobian `(Fin (genus X) → ℂ) ⧸ truePeriodLattice X`.

This file maps the route, isolates the one genuinely-missing classical input
(**Abel's theorem**, the surjectivity/inversion direction), and builds the
*reduction* — the part that does NOT need the missing input — fully sorry-free.

It lives **downstream** of `Jacobians.Abel` (it imports `DegreeOneSphere`, which
imports `Abel`), so it can reuse the repo's degree-one-sphere endgame. The leaf
`abelJacobi_twoPoint_ne_zero` itself sits in `Abel.lean`, *upstream* of that
endgame, so the leaf cannot be discharged in place by these downstream lemmas
without an import cycle — the reduction is proved here instead, and `Abel.lean`'s
`sorry` is left untouched (it would have to be re-pointed to this file once the
classical input lands; see the PLAN below).

## The route (Forster §§20–21, Miranda Ch. V §2)

Contrapositive of the target. Assume `abelJacobi (P − Q) = 0`.

1. **Abel's theorem (THE GAP).** A degree-0 divisor whose Abel–Jacobi image
   vanishes is *principal*: there is a meromorphic `f` with `div f = P − Q`,
   i.e. a simple zero at `P`, a simple pole at `Q`, and no other zeros/poles.
   In the repo's vocabulary this is exactly
   `f.HasSingleSimplePole Q` (order `-1` at `Q`, order `≥ 0` elsewhere).
   *This is the only missing piece.* Mathlib has no Abel's theorem / Picard
   group of a Riemann surface, and the repo's old `HasAbelsTheorem` typeclass was
   removed (see `Abel.lean` §"Abel's theorem itself"). The standard proofs:
   * **Residue/theta route** — vanishing periods ⟹ the period integral defines a
     single-valued meromorphic `f` with the prescribed divisor (Forster 21.4),
     or the theta-function construction (Jacobi inversion);
   * is genuinely greenfield at this Mathlib pin.

2. **Single simple pole ⟹ `X ≃ₜ S²`.** `Jacobians.nonempty_homeo_sphere_of_singleSimplePole`
   (repo, **axiom-clean**): `f.toSphere Q : X → ℂℙ¹` is a degree-1 holomorphic
   map, hence a homeomorphism, and `ℂℙ¹ ≃ₜ S²`. This is the repo's
   Riemann–Hurwitz-flavoured degree-one endgame — already fully proven.

3. **`X ≃ₜ S² ⟹ genus X = 0`.** `genus_zero_of_nonempty_homeo_sphere` (repo):
   `Ω(ℂℙ¹) = 0`. This is the *backward* half of `genus_eq_zero_iff_homeo` and is
   currently a `sorry` in `DegreeOneSphere.lean` (an **independent** leaf, on the
   `ProjectiveLine`/holomorphic-forms branch — NOT the Abel wall and NOT the RR
   track).

4. **Contradiction** with `0 < genus X`.

So the target reduces to (1) alone. Steps (2)–(4) are repo machinery.

## What this file delivers (all reachable parts sorry-free)

* `genus_pos_no_singleSimplePole_of` — the contrapositive glue
  (steps 2 + 4), with the `X ≃ₜ S² ⟹ genus = 0` step taken as an **explicit
  hypothesis** so the lemma is provably **axiom-clean** (no transitive `sorry`).
* `abelJacobi_twoPoint_ne_zero_of_abel` — the **full reduction**: given Abel's
  theorem (step 1) as an explicit hypothesis, *and* the genus-0 fact as a
  hypothesis, it proves the exact target statement, axiom-clean.
* `AbelStatement` — a named abbreviation for the precise shape of the missing
  classical input, so a future contributor knows exactly what to provide.
* `abelJacobi_twoPoint_ne_zero_of_abel'` — convenience wrapper discharging the
  genus-0 hypothesis via the repo's `genus_zero_of_nonempty_homeo_sphere`. This
  one is **not** axiom-clean: it inherits that theorem's backward `sorry`. Kept
  separate, and clearly flagged, so the axiom-clean glue above is unpolluted.

## How this closes the challenge

`abelJacobi_twoPoint_ne_zero` is consumed only by `ofCurve_inj` in `Jacobians.lean`
(THE #3 challenge theorem), which is *already fully proven modulo this single
leaf*. So providing the `AbelStatement` input here closes `ofCurve_inj` outright.

## References

* Forster, *Lectures on Riemann Surfaces*, §§20–21 (Abel's theorem, Jacobi
  inversion).
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. V §§2–4.
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Topology

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Step 2 + 4: positive genus forbids a single simple pole

The contrapositive of the chain "single simple pole ⟹ `X ≃ₜ S²` ⟹ `genus = 0`".
We take the final `X ≃ₜ S² ⟹ genus = 0` implication as a hypothesis `hSphere`
so this lemma is **axiom-clean** (the repo's concrete witness for `hSphere`,
`genus_zero_of_nonempty_homeo_sphere`, currently carries a `sorry` on an
independent branch; plugging it in is the wrapper `…'` below). -/

/-- **Positive genus ⟹ no single simple pole** (axiom-clean glue).

If some meromorphic `f` had a single simple pole, then `X ≃ₜ S²`
(`nonempty_homeo_sphere_of_singleSimplePole`, repo, axiom-clean), whence
`genus X = 0` by the supplied `hSphere`, contradicting `0 < genus X`. -/
theorem genus_pos_no_singleSimplePole_of
    (hSphere : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      genus X = 0)
    (hg : 0 < genus X)
    (P : X) (f : MeromorphicFunction X) (hP : f.HasSingleSimplePole P) :
    False := by
  have hHomeo : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    nonempty_homeo_sphere_of_singleSimplePole f hP
  have hgenus0 : genus X = 0 := hSphere hHomeo
  omega

/-! ### The precise shape of the missing classical input (Abel's theorem)

`AbelStatement X` is exactly what a contributor must supply: for *distinct* `P Q`,
if the Abel–Jacobi image of `P − Q` vanishes then `P − Q` is principal, witnessed
by a meromorphic function with a single simple pole at `Q` (a simple zero at `P`,
a simple pole at `Q`, no other zeros or poles). -/

/-- The exact missing input — **Abel's theorem** (inversion direction), as a
`Prop` on `X`. Distinct points `P ≠ Q` with vanishing Abel–Jacobi image
`abelJacobi (P − Q) = 0` admit a meromorphic `f` with `f.HasSingleSimplePole Q`.

This is the one genuinely-greenfield gap: Mathlib has neither Abel's theorem nor
the Picard group of a Riemann surface at this pin. -/
def AbelStatement (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Prop :=
  ∀ {P Q : X}, P ≠ Q →
    abelJacobi ⟨twoPointDivisor X P Q, twoPointDivisor_mem_degZero X P Q⟩ = 0 →
    ∃ f : MeromorphicFunction X, f.HasSingleSimplePole Q

/-! ### The full reduction (axiom-clean)

Given Abel's theorem (`hAbel : AbelStatement X`) and the genus-0 fact
(`hSphere`), the target `abelJacobi_twoPoint_ne_zero` follows. This lemma is
**axiom-clean**: both classical inputs are explicit hypotheses, so there is no
transitive `sorry`. It is the exact statement of `Abel.lean`'s leaf, ready to be
plugged in once `AbelStatement X` is provided. -/

/-- **Reduction of `abelJacobi_twoPoint_ne_zero` to Abel's theorem** (axiom-clean).

Contrapositive: if `abelJacobi (P − Q) = 0`, Abel's theorem `hAbel` produces a
single-simple-pole `f` at `Q`; then `genus_pos_no_singleSimplePole_of` (with the
supplied `hSphere`) derives `False` from `0 < genus X`. -/
theorem abelJacobi_twoPoint_ne_zero_of_abel
    (hAbel : AbelStatement X)
    (hSphere : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      genus X = 0)
    (hg : 0 < genus X) {P Q : X} (hPQ : P ≠ Q) :
    abelJacobi ⟨twoPointDivisor X P Q, twoPointDivisor_mem_degZero X P Q⟩ ≠ 0 := by
  intro hAJ
  obtain ⟨f, hf⟩ := hAbel hPQ hAJ
  exact genus_pos_no_singleSimplePole_of hSphere hg Q f hf

/-! ### Convenience wrapper (NOT axiom-clean — inherits the repo's backward sorry)

Discharges the `hSphere` hypothesis with the repo's concrete witness
`genus_zero_of_nonempty_homeo_sphere`. That theorem is currently a `sorry`
(`Ω(ℂℙ¹) = 0`, an independent leaf on the holomorphic-forms branch), so this
wrapper depends on `sorryAx`. Provided for ergonomics; the axiom-clean content is
`abelJacobi_twoPoint_ne_zero_of_abel` above. -/

/-- Same as `abelJacobi_twoPoint_ne_zero_of_abel` but with the genus-0 step
discharged by `genus_zero_of_nonempty_homeo_sphere`. **Not axiom-clean** — see the
section note. Once `AbelStatement X` is provided, this is the exact target
`abelJacobi_twoPoint_ne_zero`. -/
theorem abelJacobi_twoPoint_ne_zero_of_abel'
    (hAbel : AbelStatement X)
    (hg : 0 < genus X) {P Q : X} (hPQ : P ≠ Q) :
    abelJacobi ⟨twoPointDivisor X P Q, twoPointDivisor_mem_degZero X P Q⟩ ≠ 0 :=
  abelJacobi_twoPoint_ne_zero_of_abel hAbel
    (fun h => genus_zero_of_nonempty_homeo_sphere h) hg hPQ

end Jacobians
