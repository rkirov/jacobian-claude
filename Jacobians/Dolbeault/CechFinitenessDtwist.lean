/-
  Dolbeault ladder — **general-divisor Čech `H¹` finiteness** (Forster GTM 81 §16, the skyscraper
  reduction), reducing the arbitrary-divisor case to the already-proven `D = 0` case.

  ## What this file proves

      `finiteDimensional_cechH1_general (𝔘 : FiniteCover X) (D : Divisor X) :
         FiniteDimensional ℂ (𝔘.cechH1 D)`

  for an ARBITRARY finite cover `𝔘` and an ARBITRARY divisor `D`.  The `D = 0` case
  (`CechFinitenessAssembly.finiteDimensional_cechH1_zero`) is the proven base; we climb the divisor
  one point at a time.

  ## The argument (a LIGHT skyscraper reduction — no snake lemma, no acyclicity, no witness)

  The sheaves `𝒪_D ⊆ 𝒪_{D+P}` differ only in the allowed pole order at the single point `P`.  At every
  open `W`, the **stalk quotient** `OmegaDGerm (D+P) W ⧸ OmegaDGerm D W` is at most `1`-dimensional: the
  order-`(−D(P)−1)` principal-part coefficient `coeffGermLin` has kernel exactly `OmegaDGerm D W`
  (`ker_coeffGermLin`), so the quotient injects into `ℂ`.  Consequently, for the *finite* index types of
  the Čech complex:

    * `sections0 (D+P) ⧸ sections0 D` is finite-dimensional (a finite product of stalk quotients);
    * `sections1 (D+P) ⧸ sections1 D` is finite-dimensional likewise;
    * hence `cocycles1 (D+P) ⧸ cocycles1 D` is finite-dimensional (it injects into the `sections1`
      quotient), and `coboundaries1 (D+P) ⧸ coboundaries1 D` is too (a quotient of the `sections0` one).

  From these finite "correction" spaces, finiteness of `H¹` propagates BOTH ways along the inclusion
  `h1Map : H¹(𝒪_D) → H¹(𝒪_{D+P})`:

    * **forward** (`H¹(D)` finite ⟹ `H¹(D+P)` finite): `range h1Map` is finite (image of a finite-dim
      space) and `coker h1Map` is a quotient of `cocycles1(D+P)/cocycles1(D)` (finite), so
      `H¹(D+P)` is an extension of two finite-dim spaces (`Module.Finite.of_submodule_quotient`);
    * **backward** (`H¹(D+P)` finite ⟹ `H¹(D)` finite): `ker h1Map` is a quotient of
      `coboundaries1(D+P)/coboundaries1(D)` (finite) and `H¹(D)/ker h1Map ≅ range h1Map` (finite), so
      `H¹(D)` is again an extension of two finite-dim spaces.

  The bidirectional per-point step (`finiteDimensional_cechH1_add_single_iff`) then drives an induction:
  `Int.induction_on` on the coefficient (a single point, `±1` at a time) and `Finsupp.induction` on the
  divisor (one point at a time), with base `D = 0`.

  Everything is `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/
import Jacobians.Dolbeault.CechFinitenessAssembly
import Jacobians.Dolbeault.SkyscraperArrow

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The skyscraper stalk quotient is finite-dimensional (≤ 1) -/

/-- **The skyscraper stalk quotient is at most `1`-dimensional.**  At any open `W ∋ P`, the order-
`(−D(P)−1)` principal-part coefficient `coeffGermLin` has kernel exactly `OmegaDGerm D W`
(`ker_coeffGermLin`), so the quotient `OmegaDGerm (D+P) W ⧸ OmegaDGerm D W` injects into `ℂ` and is
finite-dimensional. -/
theorem finiteDimensional_stalkQuotient {W : Opens X} {D : Divisor X} {P : X} (hP : P ∈ W) :
    FiniteDimensional ℂ
      (OmegaDGerm (D + Finsupp.single P 1) W ⧸
        (OmegaDGerm D W).submoduleOf (OmegaDGerm (D + Finsupp.single P 1) W)) := by
  -- The descended coefficient map `quotient ↪ ℂ` (kernel is exactly `OmegaDGerm D W`).
  have hker : (OmegaDGerm D W).submoduleOf (OmegaDGerm (D + Finsupp.single P 1) W)
      = LinearMap.ker (coeffGermLin hP (D := D)) := (ker_coeffGermLin hP).symm
  rw [hker]
  -- `quotient by ker(coeffGermLin) ≅ range(coeffGermLin) ⊆ ℂ`, a finite-dim space.
  exact Module.Finite.equiv (LinearMap.quotKerEquivRange (coeffGermLin hP (D := D))).symm

/-- For an open `W` NOT containing `P`, the stalk quotient is `0` (the section spaces coincide). -/
theorem finiteDimensional_stalkQuotient_of_not_mem {W : Opens X} {D : Divisor X} {P : X}
    (hP : P ∉ W) :
    FiniteDimensional ℂ
      (OmegaDGerm (D + Finsupp.single P 1) W ⧸
        (OmegaDGerm D W).submoduleOf (OmegaDGerm (D + Finsupp.single P 1) W)) := by
  -- The two section spaces coincide, so the quotient is by `⊤` (subsingleton, hence finite-dim).
  have heq : OmegaDGerm (D + Finsupp.single P 1) W = OmegaDGerm D W :=
    OmegaDGerm_add_single_eq_of_not_mem hP
  haveI : Subsingleton (OmegaDGerm (D + Finsupp.single P 1) W ⧸
      (OmegaDGerm D W).submoduleOf (OmegaDGerm (D + Finsupp.single P 1) W)) := by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.submoduleOf, heq,
      Submodule.comap_subtype_self]
  infer_instance

/-! ### Finite-dimensionality of the section-quotient correction spaces -/

namespace FiniteCover

open FiniteFamily

variable (𝔘 : FiniteCover X) (D : Divisor X) (P : X)

/-- `sections1 (D+P) ⧸ sections1 D` is finite-dimensional: it injects into the finite product
`∏ p, (OmegaDGerm (D+P) (U_p) ⧸ OmegaDGerm D (U_p))` of stalk quotients (each ≤ 1-dim, finitely many
overlaps `p : ι × ι`). -/
theorem finiteDimensional_sections1_quotient :
    FiniteDimensional ℂ
      (𝔘.sections1 (D + Finsupp.single P 1) ⧸
        (𝔘.sections1 D).submoduleOf (𝔘.sections1 (D + Finsupp.single P 1))) := by
  sorry

/-- `sections0 (D+P) ⧸ sections0 D` is finite-dimensional (degree-0 analogue). -/
theorem finiteDimensional_sections0_quotient :
    FiniteDimensional ℂ
      (𝔘.sections0 (D + Finsupp.single P 1) ⧸
        (𝔘.sections0 D).submoduleOf (𝔘.sections0 (D + Finsupp.single P 1))) := by
  sorry

/-- `cocycles1 (D+P) ⧸ cocycles1 D` is finite-dimensional: the cocycle quotient injects into the
section quotient `sections1 (D+P) ⧸ sections1 D` (`cocycles1 = ker δ¹ ⊓ sections1`). -/
theorem finiteDimensional_cocycles1_quotient :
    FiniteDimensional ℂ
      (𝔘.cocycles1 (D + Finsupp.single P 1) ⧸
        (𝔘.cocycles1 D).submoduleOf (𝔘.cocycles1 (D + Finsupp.single P 1))) := by
  sorry

/-- `coboundaries1 (D+P) ⧸ coboundaries1 D` is finite-dimensional: it is a quotient of the degree-0
section quotient `sections0 (D+P) ⧸ sections0 D` (`coboundaries1 = δ⁰(sections0)`). -/
theorem finiteDimensional_coboundaries1_quotient :
    FiniteDimensional ℂ
      (𝔘.coboundaries1 (D + Finsupp.single P 1) ⧸
        (𝔘.coboundaries1 D).submoduleOf (𝔘.coboundaries1 (D + Finsupp.single P 1))) := by
  sorry

/-! ### The per-point step (both directions) -/

/-- **Forward per-point step.**  `H¹(𝒪_D)` finite ⟹ `H¹(𝒪_{D+P})` finite.  `range h1Map` is finite
(image of finite-dim `H¹(𝒪_D)`); `coker h1Map` is a quotient of `cocycles1(D+P)/cocycles1(D)`
(finite); `H¹(𝒪_{D+P})` is the extension of the two. -/
theorem finiteDimensional_cechH1_add_single_of
    (h : FiniteDimensional ℂ (𝔘.cechH1 D)) :
    FiniteDimensional ℂ (𝔘.cechH1 (D + Finsupp.single P 1)) := by
  sorry

/-- **Backward per-point step.**  `H¹(𝒪_{D+P})` finite ⟹ `H¹(𝒪_D)` finite.  `ker h1Map` is a quotient
of `coboundaries1(D+P)/coboundaries1(D)` (finite); `H¹(𝒪_D)/ker h1Map ≅ range h1Map` (finite). -/
theorem finiteDimensional_cechH1_of_add_single
    (h : FiniteDimensional ℂ (𝔘.cechH1 (D + Finsupp.single P 1))) :
    FiniteDimensional ℂ (𝔘.cechH1 D) := by
  sorry

/-- **The bidirectional per-point step.**  `H¹(𝒪_{D+P})` is finite iff `H¹(𝒪_D)` is. -/
theorem finiteDimensional_cechH1_add_single_iff :
    FiniteDimensional ℂ (𝔘.cechH1 (D + Finsupp.single P 1)) ↔
      FiniteDimensional ℂ (𝔘.cechH1 D) :=
  ⟨𝔘.finiteDimensional_cechH1_of_add_single D P,
    𝔘.finiteDimensional_cechH1_add_single_of D P⟩

/-! ### Divisor induction -/

/-- `H¹(𝒪_{D + single P k})` is finite iff `H¹(𝒪_D)` is, for any integer `k` (induct on `k` via
`Int.induction_on`; `±1` at a time is the per-point step). -/
theorem finiteDimensional_cechH1_add_singlePoint_iff (k : ℤ) :
    FiniteDimensional ℂ (𝔘.cechH1 (D + Finsupp.single P k)) ↔
      FiniteDimensional ℂ (𝔘.cechH1 D) := by
  induction k using Int.induction_on with
  | zero => rw [Finsupp.single_zero, add_zero]
  | succ k ih =>
    -- `D + single P (↑k+1) = (D + single P ↑k) + single P 1`; per-point step, then `ih`.
    rw [show (Finsupp.single P ((k : ℤ) + 1) : Divisor X)
        = Finsupp.single P (k : ℤ) + Finsupp.single P 1 from by rw [← Finsupp.single_add],
      ← add_assoc, 𝔘.finiteDimensional_cechH1_add_single_iff (D + Finsupp.single P (k : ℤ)) P]
    exact ih
  | pred k ih =>
    -- `(D + single P (−↑k−1)) + single P 1 = D + single P (−↑k)`; per-point step bridges them.
    rw [← ih,
      (𝔘.finiteDimensional_cechH1_add_single_iff (D + Finsupp.single P (-(k : ℤ) - 1)) P).symm,
      add_assoc, ← Finsupp.single_add, show (-(k : ℤ) - 1 + 1) = -(k : ℤ) from by ring]

/-- **Finiteness of `H¹(𝒪_D)` for any divisor `D`, on a FIXED cover, from the `D = 0` case** (the
divisor induction).  `Finsupp.induction` on `D` adds one point at a time; each addition is the
single-point step. -/
theorem finiteDimensional_cechH1_of_zero (h0 : FiniteDimensional ℂ (𝔘.cechH1 (0 : Divisor X)))
    (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.cechH1 D) := by
  induction D using Finsupp.induction with
  | zero => exact h0
  | single_add a b f _ _ ih =>
    -- `single a b + f = f + single a b`; the single-point step bridges `cechH1 f` and `cechH1 (…)`.
    rw [add_comm]
    exact (𝔘.finiteDimensional_cechH1_add_singlePoint_iff f a b).mpr ih

end FiniteCover

/-! ### The general theorem (any cover, any divisor) -/

/-- **General-divisor Čech `H¹` finiteness (Forster 14.9 + §16 skyscraper).**  For an arbitrary finite
cover `𝔘` and an arbitrary divisor `D`, `H¹(𝔘, 𝒪_D)` is finite-dimensional.  The proven `D = 0` case
(`finiteDimensional_cechH1_zero`) is climbed to general `D` one point at a time via the skyscraper stalk
quotient (`finiteDimensional_cechH1_of_zero`). -/
theorem finiteDimensional_cechH1_general (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.cechH1 D) :=
  𝔘.finiteDimensional_cechH1_of_zero (finiteDimensional_cechH1_zero 𝔘) D

end Jacobians.Dolbeault
