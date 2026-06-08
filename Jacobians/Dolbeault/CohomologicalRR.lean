/-
  Dolbeault ladder — cohomological Riemann–Roch (χ-additivity, Forster §16).

  This file proves the `DolbeaultLadder` leaf

      `(h⁰(D) : ℤ) − h¹(D) = deg D + 1 − h¹(0)`

  by the standard Euler-characteristic argument. Write `χ(D) := (h⁰(D) : ℤ) − h¹(D)`. The theorem
  is `χ(D) = deg D + χ(0)` together with the Liouville base `h⁰(0) = 1` (so `χ(0) = 1 − h¹(0)`).

  Structure (Forster §16):
  * **Base** `h⁰(0) = 1`: the `h⁰ = l` bridge (`CechH0.h0Dim_eq_lDim`) plus `l(0) = 1`
    (`RiemannRoch.lDim_zero_eq_one`, Liouville on the compact `X`). CLOSED.
  * **Single-point jump** `χ(D + P) = χ(D) + 1`: from the skyscraper short exact sequence
    `0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0` and its six-term long exact sequence in Čech cohomology
    `0 → H⁰(𝒪_D) → H⁰(𝒪_{D+P}) → ℂ_P → H¹(𝒪_D) → H¹(𝒪_{D+P}) → 0` (the skyscraper has `H^{≥1}=0`).
    This is **decomposed** into a proven crank and an isolated kernel:
      - `six_term_exact_alt_sum`: alternating dim sum of a 6-term exact sequence of fin-dim spaces
        is `0` (pure rank–nullity). PROVEN, axiom-clean.
      - the H⁰-inclusion `f₁ = h0Incl` (`globalSections D ↪ globalSections (D+P)`, order weakening),
        its injectivity, and the inclusion-induced `f₄ = h1Map`. PROVEN, axiom-clean.
      - `chi_jump_of_LES`: runs the crank on a `SkyscraperLES` to get the jump. PROVEN, axiom-clean.
      - `exists_skyscraperLES`: THE single named honest `sorry` (a **TRUE** statement), packaging the
        genuine `ℂ_P` (the 1-dim skyscraper, `finrank = 1` now trivial), the coefficient arrow
        `f₂ = h0ToSky` with `range f₁ = ker f₂` (`exact₁₂`), the snake-lemma data
        (`f₃`, exactness `exact₂`/`exact₃`/`surj₄`), and `H¹` finiteness. NOT faked.
        SOUNDNESS FIX (2026-06-02): the middle term was the H⁰-cokernel with a `skyDim:finrank=1`
        field that is FALSE at base points; re-pointed to the genuine `ℂ_P` (see `Skyscraper`).
  * **Iterated jump + induction on the divisor** (`Int.induction_on`, `Finsupp.induction`,
    `Divisor.deg` additivity): pure `ℤ`-bookkeeping built on `chi_jump`. CLOSED.

  So: `cohomological_riemannRoch` is proven *modulo the single `exists_skyscraperLES` sorry*;
  everything else (base, the LES crank, the structural arrows, the induction skeleton) is sorry-free.
-/
import Jacobians.Dolbeault.CohomologicalRRChartDisk

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Classical

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The homological crank: alternating dimension sum of a 6-term exact sequence

The single non-trivial *algebraic* fact behind the χ-jump is that a 6-term exact sequence of
finite-dimensional vector spaces `0 → A → B → C → D → E → 0` has alternating sum of dimensions `0`.
This is pure linear algebra (rank–nullity at each map plus the exactness `range fₖ = ker fₖ₊₁`); it
is proven here in full, with **no** `sorry` and **no** homological-algebra machinery. -/

/-- **Alternating dimension sum of a 6-term exact sequence** (rank–nullity crank). For an exact
sequence of finite-dimensional `K`-vector spaces
`0 → A →[f₁] B →[f₂] C →[f₃] D →[f₄] E → 0`
(`f₁` injective, exact at `B`, `C`, `D`, `f₄` surjective) the alternating sum of dimensions is `0`:
`dim A − dim B + dim C − dim D + dim E = 0`.

Proof: rank–nullity `dim (range fₖ) + dim (ker fₖ) = dim (source)` at each of the four maps;
exactness rewrites every `ker fₖ₊₁` as `range fₖ`; `ker f₁ = 0` (injective) and `range f₄ = E`
(surjective); `omega` finishes the integer bookkeeping. -/
theorem six_term_exact_alt_sum {K A B C E F : Type*} [Field K]
    [AddCommGroup A] [Module K A] [FiniteDimensional K A]
    [AddCommGroup B] [Module K B] [FiniteDimensional K B]
    [AddCommGroup C] [Module K C] [FiniteDimensional K C]
    [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    [AddCommGroup F] [Module K F] [FiniteDimensional K F]
    (f₁ : A →ₗ[K] B) (f₂ : B →ₗ[K] C) (f₃ : C →ₗ[K] E) (f₄ : E →ₗ[K] F)
    (hf₁ : Function.Injective f₁)
    (h₁ : Function.Exact f₁ f₂) (h₂ : Function.Exact f₂ f₃) (h₃ : Function.Exact f₃ f₄)
    (hf₄ : Function.Surjective f₄) :
    (Module.finrank K A : ℤ) - Module.finrank K B + Module.finrank K C
      - Module.finrank K E + Module.finrank K F = 0 := by
  have rn1 := f₁.finrank_range_add_finrank_ker
  have rn2 := f₂.finrank_range_add_finrank_ker
  have rn3 := f₃.finrank_range_add_finrank_ker
  have rn4 := f₄.finrank_range_add_finrank_ker
  rw [LinearMap.exact_iff] at h₁ h₂ h₃
  rw [← LinearMap.ker_eq_bot] at hf₁
  rw [← LinearMap.range_eq_top] at hf₄
  have e1 : Module.finrank K (LinearMap.ker f₁) = 0 := by rw [hf₁]; simp
  have e4 : Module.finrank K (LinearMap.range f₄) = Module.finrank K F := by rw [hf₄]; simp
  rw [h₁] at rn2
  rw [h₂] at rn3
  rw [h₃] at rn4
  rw [e1] at rn1
  rw [e4] at rn4
  omega

namespace FiniteCover

open FiniteFamily

/-- The **Euler characteristic** `χ(D) := h⁰(D) − h¹(D)` (as an integer). -/
noncomputable def chi (𝔘 : FiniteCover X) (D : Divisor X) : ℤ :=
  (𝔘.h0Dim D : ℤ) - 𝔘.h1Dim D

/-! ### Structural inclusion `𝒪_D ↪ 𝒪_{D+P}`, `Skyscraper`, `h0Incl`, `h1Map`, `SkyscraperLES`

These order-bookkeeping arrows and the `SkyscraperLES` structure now live in the base file
`SkyscraperLESBase` (imported transitively via `CohomologicalRRChartDisk`), so that the proven
downstream assembly can sit *upstream* of this χ-induction and discharge `exists_skyscraperLES`. -/

/-! ### Base: `h⁰(0) = 1` (Liouville) -/

/-- **Base case (Liouville).** `h⁰(𝔘, 𝒪) = 1`: the `h⁰ = l(D)` bridge identifies the global Čech
sections with the linear system, and `l(0) = 1` by Liouville on the compact connected `X`. -/
theorem h0Dim_zero_eq_one (𝔘 : FiniteCover X) : (𝔘.h0Dim 0 : ℤ) = 1 := by
  rw [𝔘.h0Dim_eq_lDim 0, lDim_zero_eq_one]; norm_num

/-- **The crank (sorry-free).** Given the skyscraper long exact sequence, the single-point χ-jump
`χ(D+P) = χ(D) + 1` is pure linear algebra: the alternating dimension sum of the six-term exact
sequence is `0` (`six_term_exact_alt_sum`), and `finrank ℂ_P = 1` (`skyDim`). Rearranging
`h⁰(D) − h⁰(D+P) + 1 − h¹(D) + h¹(D+P) = 0` gives the jump. No analytic content. -/
theorem chi_jump_of_LES {𝔘 : FiniteCover X} {D : Divisor X} {P : X}
    (S : SkyscraperLES 𝔘 D P) : 𝔘.chi (D + Finsupp.single P 1) = 𝔘.chi D + 1 := by
  haveI := S.finH1D; haveI := S.finH1DP; haveI := S.finH0D; haveI := S.finH0DP
  have halt := six_term_exact_alt_sum
    (𝔘.h0Incl D P) S.h0ToSky S.f₃ (𝔘.h1Map D P)
    (𝔘.h0Incl_injective D P) S.exact₁₂ S.exact₂ S.exact₃ S.surj₄
  -- `finrank ℂ_P = finrank ℂ ℂ = 1` (genuine 1-dim stalk), and identify the four other `finrank`s.
  rw [show Module.finrank ℂ (𝔘.Skyscraper D P) = 1 from Module.finrank_self ℂ] at halt
  simp only [chi, h0Dim, h1Dim, Nat.cast_one] at halt ⊢
  linarith

/-- **Existence of the local-realization datum — THE NAMED HONEST `sorry`** (the single irreducible
analytic+combinatorial core of cohomological Riemann–Roch, Forster §16).

`LocalRealizationData 𝔘 D P` (`SkyscraperSnake`) packages **exactly** the two pieces that the snake
lemma cannot supply — and nothing else (finiteness is now discharged unconditionally):
  * `e0 : H⁰(Q) ≅ ℂ` with `hcompat` — the **local realization** of the degree-0 quotient cohomology
    with the skyscraper stalk `ℂ` (the order-`(−D(P)−1)` principal-part coefficient at `P`);
  * `Subsingleton H¹(Q)` — **acyclicity** of the skyscraper quotient complex.
Everything else (the snake connecting map, all exactness, the LES termination, AND the three
`FiniteDimensional` inputs — `H¹` by `finiteDimensional_cechH1_general` axiom-clean, `H⁰(𝒪_{D+P})` by
the `CohomologicalH0Finiteness.finiteDimensional_globalSections` instance) is PROVEN, so
`exists_skyscraperLES` is now a *theorem* (below), reducing the whole cohomological-RR `sorry` to this
single datum. This is strictly smaller than the old `exists_skyscraperLES` `sorry`: the snake and
finiteness have been stripped off.

WHY IT IS STILL A `sorry` (the precise, *corrected* diagnosis — see also `CohomologicalRRChartDisk`):
the proven chart-disk assembly `SkyscraperAssembly.skyscraperLES_of_chartDisk` /
`localRealizationData_of_chartDisk` produces this datum only under geometric hypotheses
(`hP`/`hWsrc`/`hDsupp`/`hstar`) that **cannot hold on a fixed finite cover of a compact connected `X`**
for all `(D, P)`:
* `hstar` (`P ∈ U j → j = i`, singleton star) at *every* `P` would force the cover sets pairwise
  disjoint — disconnecting `X` — or a single chart-disk `= X` (impossible for compact `X`). Overlap
  points always exist, so the χ-induction's per-support-point demand is never met. (The earlier
  "shrink to an adapted singleton-star cover" framing asked for a cover that does **not exist**.)
* `hWsrc` (`U i ⊆ (chartAt ℂ P).source`) and `hDsupp` (`D` supported on `U i` only at `P`) also fail
  for a fixed cover and general `(D, P)`.

Closing `exists_localRealizationData` therefore needs **one of** two genuinely-unbanked, substantial
builds:
  (A) a *multi-vertex / full-simplex-star* construction of `LocalRealizationData` for GENERAL `(D, P)`
      on the chart-disk cover (dropping `hstar`/`hWsrc`/`hDsupp`). Its keystone missing primitive is
      the **general-`D` local realization (Mittag–Leffler on a disk)**: `coeffGermLin` surjective via
      the explicit *product* witness in the cover-set's CENTER chart `φ`,
      `a·(z−φP)^{−(D P)−1}·∏_{Q∈ supp D∩U i, Q≠P}(z−φQ)^{−(D Q)}` (forced poles/zeros at the other
      support points so it lies in `𝒪_{D+P}(U i)`; `meromorphicOrderAt_prod` for the orders), coupled
      with the full-simplex cochain cone-contraction for `Subsingleton H¹(Q)`;
  (B) `h¹` cover-independence among Leray covers (strictly-finer `refineH1` surjectivity,
      `CechRefinementLeray`'s `## SURJECTIVITY`, NOT the global `IsDiskAcyclic`), to switch to a
      `P`-adapted cover per jump (the explicitly-unbanked STEP B).

Route (A) is the task's "cochain-LES" plan; the keystone is the general-`D` product-witness
realization. Neither is a quick win — this is the single honest `sorry`, *not* faked. -/
theorem exists_localRealizationData (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) (D : Divisor X) (P : X) :
    Nonempty (𝔘.LocalRealizationData D P) :=
  sorry

/-- **The skyscraper long exact sequence** (Forster §16) — now a *theorem*, reduced to the single
local-realization datum `exists_localRealizationData` via the proven snake assembly
`skyscraperLES_of_localRealization` (which builds the connecting map, all exactness, the LES
termination, and carries the finiteness instances). -/
theorem exists_skyscraperLES (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) (D : Divisor X) (P : X) :
    Nonempty (SkyscraperLES 𝔘 D P) :=
  (exists_localRealizationData 𝔘 hL D P).elim fun L => ⟨skyscraperLES_of_localRealization L⟩

/-! ### The single-point χ-jump (sorry-free GIVEN the skyscraper LES) -/

/-- **Single-point χ-jump (Forster §16).** `χ(D + P) = χ(D) + 1`. Obtained by running the proven
linear-algebra crank `chi_jump_of_LES` on the skyscraper long exact sequence
(`exists_skyscraperLES`, the single isolated homological/analytic kernel). -/
theorem chi_jump (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) (D : Divisor X) (P : X) :
    𝔘.chi (D + Finsupp.single P 1) = 𝔘.chi D + 1 :=
  (exists_skyscraperLES 𝔘 hL D P).elim chi_jump_of_LES

/-! ### Iterated jump along a single point — `Int.induction_on` (CLOSED, pure ℤ-bookkeeping) -/

/-- **Iterated χ-jump.** `χ(D + n·P) = χ(D) + n` for every integer `n`, by induction on `n` built on
the unit jump `chi_jump` (both directions). Pure `ℤ`-arithmetic; no analytic content. -/
theorem chi_add_single (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) (D : Divisor X) (P : X) (n : ℤ) :
    𝔘.chi (D + Finsupp.single P n) = 𝔘.chi D + n := by
  induction n using Int.induction_on with
  | zero => simp [Finsupp.single_zero]
  | succ k ih =>
    -- `single P (k+1) = single P k + single P 1`, so we add one more point and apply `chi_jump`.
    rw [Finsupp.single_add, ← add_assoc, 𝔘.chi_jump hL (D + Finsupp.single P (k : ℤ)) P, ih]
    ring
  | pred k ih =>
    -- Downward: `single P (-k-1) + single P 1 = single P (-k)`, so `chi_jump` relates the two.
    have hstep : 𝔘.chi (D + Finsupp.single P (-(k : ℤ) - 1)) + 1
        = 𝔘.chi (D + Finsupp.single P (-(k : ℤ))) := by
      rw [← 𝔘.chi_jump hL (D + Finsupp.single P (-(k : ℤ) - 1)) P, add_assoc, ← Finsupp.single_add]
      ring_nf
    rw [ih] at hstep
    linarith

/-! ### Induction on the divisor — `Finsupp.induction` (CLOSED, pure ℤ-bookkeeping) -/

/-- **χ-additivity over the base.** `χ(D) = deg D + χ(0)` for every divisor `D`, by induction on the
finite support of `D` (`Finsupp.induction`): the empty divisor is the base, and each
`single a b`-summand contributes `b = deg (single a b)` to both sides via the iterated jump
`chi_add_single` and additivity of `deg` (`Divisor.deg_add`/`deg_single`). Pure `ℤ`-arithmetic. -/
theorem chi_eq_deg_add_chi_zero (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) (D : Divisor X) :
    𝔘.chi D = Divisor.deg X D + 𝔘.chi 0 := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [add_comm (Finsupp.single a b) f, 𝔘.chi_add_single hL f a b, ih, Divisor.deg_add,
      Divisor.deg_single]
    ring

end FiniteCover

/-! ### Cohomological Riemann–Roch (the leaf) -/

/-- **Cohomological Riemann–Roch (χ-additivity, Forster §16).**
`h⁰(D) − h¹(D) = deg D + 1 − h¹(0)`.

Rearrangement of `χ(D) = deg D + χ(0)` (`chi_eq_deg_add_chi_zero`, the iterated skyscraper jump +
divisor induction) using the Liouville base `h⁰(0) = 1` (`h0Dim_zero_eq_one`), since then
`χ(0) = 1 − h¹(0)`. This is the exact `DolbeaultLadder` leaf statement; it is proven *modulo the
single named homological `sorry` `chi_jump`* — base and induction are sorry-free. -/
theorem cohomological_riemannRoch (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) (D : Divisor X) :
    (𝔘.h0Dim D : ℤ) - 𝔘.h1Dim D = Divisor.deg X D + 1 - 𝔘.h1Dim 0 := by
  have hχ := 𝔘.chi_eq_deg_add_chi_zero hL D
  have hbase := 𝔘.h0Dim_zero_eq_one
  simp only [FiniteCover.chi] at hχ
  rw [hbase] at hχ
  linarith

end Jacobians.Dolbeault
