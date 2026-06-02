/-
  Dolbeault ladder — cohomological Riemann–Roch (χ-additivity, Forster §16).

  This file proves the `DolbeaultLadder` leaf

      `(h⁰(D) : ℤ) − h¹(D) = deg D + 1 − h¹(0)`

  by the standard Euler-characteristic argument. Write `χ(D) := (h⁰(D) : ℤ) − h¹(D)`. The theorem
  is `χ(D) = deg D + χ(0)` together with the Liouville base `h⁰(0) = 1` (so `χ(0) = 1 − h¹(0)`).

  Structure (Forster §16):
  * **Base** `h⁰(0) = 1`: the `h⁰ = l` bridge (`CechH0.h0Dim_eq_lDim`) plus `l(0) = 1`
    (`RiemannRoch.lDim_zero_eq_one`, Liouville on the compact `X`). CLOSED.
  * **Single-point jump** `χ(D + P) = χ(D) + 1`: the skyscraper short exact sequence
    `0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0` and its long exact sequence in Čech cohomology (the skyscraper has
    `H^{≥1} = 0`, so the alternating dimension sum gives the jump). This is the genuine homological
    content; it is isolated as the single named `sorry` `chi_jump`. NOT faked, NOT weakened.
  * **Iterated jump + induction on the divisor** (`Int.induction_on`, `Finsupp.induction`,
    `Divisor.deg` additivity): pure `ℤ`-bookkeeping built on `chi_jump`. CLOSED.

  So: `cohomological_riemannRoch` is proven *modulo the single `chi_jump` sorry*; everything else
  (base + induction skeleton) is sorry-free.
-/
import Jacobians.Dolbeault.CechH0

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

/-- The **Euler characteristic** `χ(D) := h⁰(D) − h¹(D)` (as an integer). -/
noncomputable def chi (𝔘 : FiniteCover X) (D : Divisor X) : ℤ :=
  (𝔘.h0Dim D : ℤ) - 𝔘.h1Dim D

/-! ### Structural inclusion `𝒪_D ↪ 𝒪_{D+P}` (provable, no analytic content)

Adding the effective point divisor `P` only *weakens* the order bound (`D ≤ D + P` pointwise), so a
section of `𝒪_D` is a section of `𝒪_{D+P}`; this gives a degreewise inclusion of the section
submodules and hence of the global-section and cochain spaces. These facts are pure order
bookkeeping — the genuinely-hard analytic/homological data (skyscraper quotient, connecting map) is
isolated separately in `SkyscraperLES`. -/

/-- Pointwise monotonicity of the divisor under adding an effective point: `D x ≤ (D + P) x`. -/
theorem divisor_le_add_single (D : Divisor X) (P x : X) :
    (D : Divisor X) x ≤ (D + Finsupp.single P 1 : Divisor X) x := by
  rw [Finsupp.add_apply, Finsupp.single_apply]; split <;> omega

/-- The order bound for `𝒪_D` implies that for `𝒪_{D+P}` (the bound `−(D+P) ≤ −D` weakens). -/
theorem mem_OmegaD_add_single {D : Divisor X} {P : X} {U : Opens X} {f : U → ℂ}
    (hf : f ∈ OmegaD D U) : f ∈ OmegaD (D + Finsupp.single P 1) U := by
  refine ⟨hf.1, fun u => le_trans ?_ (hf.2 u)⟩
  exact_mod_cast neg_le_neg (divisor_le_add_single D P u.1)

/-- Germ-class sections inherit the inclusion `𝒪_D(U) ⊆ 𝒪_{D+P}(U)`. -/
theorem OmegaDGerm_le_add_single (D : Divisor X) (P : X) (U : Opens X) :
    OmegaDGerm D U ≤ OmegaDGerm (D + Finsupp.single P 1) U := by
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, mem_OmegaD_add_single hg, rfl⟩

/-- The `𝒪_D` 0-sections are contained in the `𝒪_{D+P}` 0-sections. -/
theorem sections0_le_add_single (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.sections0 D ≤ 𝔘.sections0 (D + Finsupp.single P 1) :=
  fun _ hf i => OmegaDGerm_le_add_single D P (𝔘.U i) (hf i)

/-- The global `𝒪_D`-sections are contained in the global `𝒪_{D+P}`-sections (same `ker δ⁰`, weaker
sheaf condition). This is the underlying map of the long-exact-sequence arrow `H⁰(D) → H⁰(D+P)`. -/
theorem globalSections_le_add_single (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.globalSections D ≤ 𝔘.globalSections (D + Finsupp.single P 1) :=
  inf_le_inf_left _ (𝔘.sections0_le_add_single D P)

/-! ### Base: `h⁰(0) = 1` (Liouville) -/

/-- **Base case (Liouville).** `h⁰(𝔘, 𝒪) = 1`: the `h⁰ = l(D)` bridge identifies the global Čech
sections with the linear system, and `l(0) = 1` by Liouville on the compact connected `X`. -/
theorem h0Dim_zero_eq_one (𝔘 : FiniteCover X) : (𝔘.h0Dim 0 : ℤ) = 1 := by
  rw [𝔘.h0Dim_eq_lDim 0, lDim_zero_eq_one]; norm_num

/-! ### The skyscraper long exact sequence (the genuine homological/analytic kernel)

The single-point χ-jump comes from the **skyscraper short exact sequence** of `𝒪_D`-modules
`0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0` (`ℂ_P` = the 1-dimensional skyscraper at `P`, a section of
`𝒪_{D+P}` modulo `𝒪_D` ≅ its principal-part coefficient of order `−D(P)−1`). Its **long exact
sequence** in Čech cohomology is
`0 → H⁰(𝒪_D) →[f₁] H⁰(𝒪_{D+P}) →[f₂] ℂ →[f₃] H¹(𝒪_D) →[f₄] H¹(𝒪_{D+P}) → 0`,
the skyscraper having `H^{≥1} = 0`.

`SkyscraperLES` bundles *exactly* this data. The first arrow `f₁` is the canonical inclusion
`globalSections D ↪ globalSections (D+P)` (provided here, fully proven — it is just the weakening
`D ≤ D+P` of the order bound, `globalSections_le_add_single`). The remaining data — the skyscraper
coefficient map `f₂`, the snake-lemma connecting map `f₃`, the inclusion-induced `f₄`, all four
exactness facts, and the finiteness of the cohomology groups — is the genuine analytic/homological
content (Forster §16), isolated as the single named `sorry` `exists_skyscraperLES`.

Given a `SkyscraperLES`, the χ-jump is **pure linear algebra**: the alternating dimension sum of the
six-term exact sequence is `0` (`six_term_exact_alt_sum`, proven), which rearranges to
`χ(D+P) = χ(D) + 1`. That crank, `chi_jump_of_LES`, is sorry-free. -/
structure SkyscraperLES (𝔘 : FiniteCover X) (D : Divisor X) (P : X) where
  /-- The skyscraper coefficient map `H⁰(𝒪_{D+P}) → ℂ_P`: a global `𝒪_{D+P}`-section maps to its
  principal-part coefficient of order `−D(P)−1` at `P` (the obstruction to lying in `𝒪_D`). -/
  f₂ : ↥(𝔘.globalSections (D + Finsupp.single P 1)) →ₗ[ℂ] ℂ
  /-- The connecting homomorphism `ℂ_P → H¹(𝒪_D)` (snake lemma of the SES of cochain complexes). -/
  f₃ : ℂ →ₗ[ℂ] 𝔘.cechH1 D
  /-- The map `H¹(𝒪_D) → H¹(𝒪_{D+P})` induced by the inclusion `𝒪_D ↪ 𝒪_{D+P}`. -/
  f₄ : 𝔘.cechH1 D →ₗ[ℂ] 𝔘.cechH1 (D + Finsupp.single P 1)
  /-- Exactness at `H⁰(𝒪_{D+P})`: `range (inclusion) = ker f₂` — a section of `𝒪_{D+P}` has
  vanishing principal-part coefficient at `P` iff it actually lies in `𝒪_D`. (Analytic.) -/
  exact₁ : Function.Exact
    (Submodule.inclusion (𝔘.globalSections_le_add_single D P)) f₂
  /-- Exactness at `ℂ_P`: `range f₂ = ker f₃`. (Snake lemma.) -/
  exact₂ : Function.Exact f₂ f₃
  /-- Exactness at `H¹(𝒪_D)`: `range f₃ = ker f₄`. (Snake lemma.) -/
  exact₃ : Function.Exact f₃ f₄
  /-- The last arrow `H¹(𝒪_D) → H¹(𝒪_{D+P})` is surjective (the skyscraper has `H^{≥1} = 0`, so the
  LES terminates with `→ 0`). -/
  surj₄ : Function.Surjective f₄
  /-- `H¹(𝒪_D)` is finite-dimensional (Forster 14.9; `finiteDimensional_cechH1`). -/
  [finH1D : FiniteDimensional ℂ (𝔘.cechH1 D)]
  /-- `H¹(𝒪_{D+P})` is finite-dimensional (Forster 14.9; `finiteDimensional_cechH1`). -/
  [finH1DP : FiniteDimensional ℂ (𝔘.cechH1 (D + Finsupp.single P 1))]
  /-- `H⁰(𝒪_D)` is finite-dimensional (follows from finiteness of `H¹` and the skyscraper via the
  LES; carried as a field since the construction supplies it). -/
  [finH0D : FiniteDimensional ℂ ↥(𝔘.globalSections D)]
  /-- `H⁰(𝒪_{D+P})` is finite-dimensional (likewise). -/
  [finH0DP : FiniteDimensional ℂ ↥(𝔘.globalSections (D + Finsupp.single P 1))]

attribute [instance] SkyscraperLES.finH1D SkyscraperLES.finH1DP SkyscraperLES.finH0D
  SkyscraperLES.finH0DP

/-- **The crank (sorry-free).** Given the skyscraper long exact sequence, the single-point χ-jump
`χ(D+P) = χ(D) + 1` is pure linear algebra: the alternating dimension sum of the six-term exact
sequence is `0` (`six_term_exact_alt_sum`), and `dim ℂ_P = 1`. Rearranging
`h⁰(D) − h⁰(D+P) + 1 − h¹(D) + h¹(D+P) = 0` gives the jump. No analytic content. -/
theorem chi_jump_of_LES {𝔘 : FiniteCover X} {D : Divisor X} {P : X}
    (S : SkyscraperLES 𝔘 D P) : 𝔘.chi (D + Finsupp.single P 1) = 𝔘.chi D + 1 := by
  haveI := S.finH1D; haveI := S.finH1DP; haveI := S.finH0D; haveI := S.finH0DP
  have halt := six_term_exact_alt_sum
    (Submodule.inclusion (𝔘.globalSections_le_add_single D P)) S.f₂ S.f₃ S.f₄
    (Submodule.inclusion_injective _) S.exact₁ S.exact₂ S.exact₃ S.surj₄
  -- `dim ℂ = 1`; identify the four `finrank`s with `h0Dim`/`h1Dim`.
  rw [Module.finrank_self] at halt
  simp only [chi, h0Dim, h1Dim, Nat.cast_one] at halt ⊢
  linarith

/-- **Existence of the skyscraper long exact sequence — THE NAMED HONEST `sorry`.**

This is the genuine cohomological content of Riemann–Roch (Forster §16), isolated as the single
remaining gap. Constructing it requires:

1. the short exact sequence of germ-class cochain complexes `0 → C^•(𝒪_D) → C^•(𝒪_{D+P}) →
   C^•(ℂ_P) → 0` (degreewise; the inclusion `f₁` and its cokernel the skyscraper complex);
2. the skyscraper complex `C^•(ℂ_P)` having `H⁰ = ℂ` (1-diml) and `H^{≥1} = 0`;
3. **the analytic sub-kernel**: degreewise surjectivity onto the skyscraper stalk — local
   surjectivity of meromorphic sections, i.e. a section of `𝒪_{D+P}` near `P` realises *any*
   prescribed principal-part coefficient of order `−D(P)−1`;
4. the snake lemma (Mathlib `ShortComplex.SnakeInput` / `Algebra.Homology.HomologySequence`) turning
   the SES of complexes into the six-term LES, supplying `f₂`, `f₃`, `f₄` and the exactness;
5. finiteness of the `H¹` groups (Forster 14.9; `CechFinitenessWiring.finiteDimensional_cechH1_wired`
   modulo `exists_cechModel`).

It is stated honestly — *not* faked, *not* weakening the headline. Everything downstream
(`chi_jump_of_LES`, the induction, `cohomological_riemannRoch`) is sorry-free. -/
theorem exists_skyscraperLES (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    Nonempty (SkyscraperLES 𝔘 D P) :=
  sorry

/-! ### The single-point χ-jump (sorry-free GIVEN the skyscraper LES) -/

/-- **Single-point χ-jump (Forster §16).** `χ(D + P) = χ(D) + 1`. Obtained by running the proven
linear-algebra crank `chi_jump_of_LES` on the skyscraper long exact sequence
(`exists_skyscraperLES`, the single isolated homological/analytic kernel). -/
theorem chi_jump (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.chi (D + Finsupp.single P 1) = 𝔘.chi D + 1 :=
  (exists_skyscraperLES 𝔘 D P).elim chi_jump_of_LES

/-! ### Iterated jump along a single point — `Int.induction_on` (CLOSED, pure ℤ-bookkeeping) -/

/-- **Iterated χ-jump.** `χ(D + n·P) = χ(D) + n` for every integer `n`, by induction on `n` built on
the unit jump `chi_jump` (both directions). Pure `ℤ`-arithmetic; no analytic content. -/
theorem chi_add_single (𝔘 : FiniteCover X) (D : Divisor X) (P : X) (n : ℤ) :
    𝔘.chi (D + Finsupp.single P n) = 𝔘.chi D + n := by
  induction n using Int.induction_on with
  | zero => simp [Finsupp.single_zero]
  | succ k ih =>
    -- `single P (k+1) = single P k + single P 1`, so we add one more point and apply `chi_jump`.
    rw [Finsupp.single_add, ← add_assoc, 𝔘.chi_jump (D + Finsupp.single P (k : ℤ)) P, ih]
    ring
  | pred k ih =>
    -- Downward: `single P (-k-1) + single P 1 = single P (-k)`, so `chi_jump` relates the two.
    have hstep : 𝔘.chi (D + Finsupp.single P (-(k : ℤ) - 1)) + 1
        = 𝔘.chi (D + Finsupp.single P (-(k : ℤ))) := by
      rw [← 𝔘.chi_jump (D + Finsupp.single P (-(k : ℤ) - 1)) P, add_assoc, ← Finsupp.single_add]
      ring_nf
    rw [ih] at hstep
    linarith

/-! ### Induction on the divisor — `Finsupp.induction` (CLOSED, pure ℤ-bookkeeping) -/

/-- **χ-additivity over the base.** `χ(D) = deg D + χ(0)` for every divisor `D`, by induction on the
finite support of `D` (`Finsupp.induction`): the empty divisor is the base, and each
`single a b`-summand contributes `b = deg (single a b)` to both sides via the iterated jump
`chi_add_single` and additivity of `deg` (`Divisor.deg_add`/`deg_single`). Pure `ℤ`-arithmetic. -/
theorem chi_eq_deg_add_chi_zero (𝔘 : FiniteCover X) (D : Divisor X) :
    𝔘.chi D = Divisor.deg X D + 𝔘.chi 0 := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add a b f _ _ ih =>
    rw [add_comm (Finsupp.single a b) f, 𝔘.chi_add_single f a b, ih, Divisor.deg_add,
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
theorem cohomological_riemannRoch (𝔘 : FiniteCover X) (D : Divisor X) :
    (𝔘.h0Dim D : ℤ) - 𝔘.h1Dim D = Divisor.deg X D + 1 - 𝔘.h1Dim 0 := by
  have hχ := 𝔘.chi_eq_deg_add_chi_zero D
  have hbase := 𝔘.h0Dim_zero_eq_one
  simp only [FiniteCover.chi] at hχ
  rw [hbase] at hχ
  linarith

end Jacobians.Dolbeault
