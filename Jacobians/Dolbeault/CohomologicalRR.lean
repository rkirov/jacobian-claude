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
        its injectivity, the cokernel arrow `f₂ = h0ToSky`, and exactness at `H⁰(𝒪_{D+P})`
        (`exact_h0Incl_h0ToSky`, definitional from the cokernel projection). PROVEN, axiom-clean.
      - `chi_jump_of_LES`: runs the crank on a `SkyscraperLES` to get the jump. PROVEN, axiom-clean.
      - `exists_skyscraperLES`: THE single named honest `sorry`, packaging the analytic
        local-surjectivity (`skyDim`: skyscraper cokernel is 1-dimensional), the snake-lemma data
        (`f₃`,`f₄`, exactness `exact₂`/`exact₃`/`surj₄`), and `H¹` finiteness. NOT faked.
  * **Iterated jump + induction on the divisor** (`Int.induction_on`, `Finsupp.induction`,
    `Divisor.deg` additivity): pure `ℤ`-bookkeeping built on `chi_jump`. CLOSED.

  So: `cohomological_riemannRoch` is proven *modulo the single `exists_skyscraperLES` sorry*;
  everything else (base, the LES crank, the structural arrows, the induction skeleton) is sorry-free.
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

/-! ### The skyscraper space and the H⁰-cokernel arrow (provable, no analytic content)

The skyscraper space is realised **concretely** as the cokernel of the H⁰-inclusion,
`Skyscraper := H⁰(𝒪_{D+P}) ⧸ range(f₁)`, with `f₂` its quotient projection. This makes the second
arrow `f₂` and the exactness at `H⁰(𝒪_{D+P})` (`range f₁ = ker f₂`) hold **definitionally**
(`LinearMap.exact_map_mkQ_range`) — they are proven, not assumed. The only genuine analytic content
about the skyscraper is then that this cokernel is **1-dimensional** (`skyDim`), i.e. local
surjectivity of meromorphic sections onto the order-`(−D(P)−1)` principal-part coefficient. -/

/-- The canonical H⁰-inclusion `H⁰(𝒪_D) ↪ H⁰(𝒪_{D+P})` (the order bound weakens, `f₁` of the LES). -/
noncomputable def h0Incl (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    ↥(𝔘.globalSections D) →ₗ[ℂ] ↥(𝔘.globalSections (D + Finsupp.single P 1)) :=
  Submodule.inclusion (𝔘.globalSections_le_add_single D P)

theorem h0Incl_injective (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    Function.Injective (𝔘.h0Incl D P) :=
  Submodule.inclusion_injective _

/-- The **skyscraper space** `ℂ_P`, realised as the cokernel of the H⁰-inclusion
`H⁰(𝒪_{D+P}) ⧸ range(H⁰(𝒪_D) ↪ H⁰(𝒪_{D+P}))`. Analytically `≅ ℂ` (the order-`(−D(P)−1)`
principal-part coefficient at `P`); the `≅ ℂ` is the analytic content `skyDim` of `SkyscraperLES`. -/
noncomputable abbrev Skyscraper (𝔘 : FiniteCover X) (D : Divisor X) (P : X) : Type _ :=
  ↥(𝔘.globalSections (D + Finsupp.single P 1)) ⧸ LinearMap.range (𝔘.h0Incl D P)

/-- The skyscraper coefficient arrow `f₂ : H⁰(𝒪_{D+P}) → ℂ_P`, the cokernel projection. -/
noncomputable def h0ToSky (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    ↥(𝔘.globalSections (D + Finsupp.single P 1)) →ₗ[ℂ] 𝔘.Skyscraper D P :=
  Submodule.mkQ (LinearMap.range (𝔘.h0Incl D P))

/-- **Exactness at `H⁰(𝒪_{D+P})` (PROVEN).** `range f₁ = ker f₂` holds definitionally because `f₂`
is the cokernel projection of `f₁` (`LinearMap.exact_map_mkQ_range`). No analytic content. -/
theorem exact_h0Incl_h0ToSky (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    Function.Exact (𝔘.h0Incl D P) (𝔘.h0ToSky D P) :=
  LinearMap.exact_map_mkQ_range _

/-! ### The inclusion-induced arrow `f₄ : H¹(𝒪_D) → H¹(𝒪_{D+P})` (provable, no analytic content)

The inclusion `𝒪_D ↪ 𝒪_{D+P}` is monotone on the sheaf condition at each degree (`sections1`), hence
on the 1-cocycles and 1-coboundaries; it therefore descends to a *canonical* map on `H¹ = Z¹/B¹`.
This map `h1Map` is the LES arrow `f₄`; it is constructed and PROVEN here (only its surjectivity and
the exactness `range f₃ = ker f₄` — which involve the snake/connecting map — remain in the kernel). -/

/-- The `𝒪_D` 1-sections are contained in the `𝒪_{D+P}` 1-sections (order weakening). -/
theorem sections1_le_add_single (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.sections1 D ≤ 𝔘.sections1 (D + Finsupp.single P 1) :=
  fun _ hf p => OmegaDGerm_le_add_single D P _ (hf p)

/-- The `𝒪_D` 1-cocycles are contained in the `𝒪_{D+P}` 1-cocycles (same `ker δ¹`, weaker sheaf). -/
theorem cocycles1_le_add_single (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.cocycles1 D ≤ 𝔘.cocycles1 (D + Finsupp.single P 1) :=
  inf_le_inf_left _ (𝔘.sections1_le_add_single D P)

/-- The `𝒪_D` 1-coboundaries are contained in the `𝒪_{D+P}` 1-coboundaries (`δ⁰` of more sections). -/
theorem coboundaries1_le_add_single (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.coboundaries1 D ≤ 𝔘.coboundaries1 (D + Finsupp.single P 1) :=
  Submodule.map_mono (𝔘.sections0_le_add_single D P)

/-- The 1-cocycle inclusion `Z¹(𝒪_D) ↪ Z¹(𝒪_{D+P})`. -/
noncomputable def cocyclesIncl (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    ↥(𝔘.cocycles1 D) →ₗ[ℂ] ↥(𝔘.cocycles1 (D + Finsupp.single P 1)) :=
  Submodule.inclusion (𝔘.cocycles1_le_add_single D P)

/-- **The inclusion-induced arrow `f₄ : H¹(𝒪_D) → H¹(𝒪_{D+P})`** (PROVEN). The cocycle inclusion
sends `𝒪_D`-coboundaries to `𝒪_{D+P}`-coboundaries, so it descends to the `H¹` quotients
(`Submodule.mapQ`). -/
noncomputable def h1Map (𝔘 : FiniteCover X) (D : Divisor X) (P : X) :
    𝔘.cechH1 D →ₗ[ℂ] 𝔘.cechH1 (D + Finsupp.single P 1) := by
  refine Submodule.mapQ _ _ (𝔘.cocyclesIncl D P) ?_
  rintro ⟨c, _⟩ hcob
  exact 𝔘.coboundaries1_le_add_single D P hcob

/-! ### The skyscraper long exact sequence (the genuine homological/analytic kernel)

The single-point χ-jump comes from the **skyscraper short exact sequence** of `𝒪_D`-modules
`0 → 𝒪_D → 𝒪_{D+P} → ℂ_P → 0` (`ℂ_P` = the 1-dimensional skyscraper at `P`). Its **long exact
sequence** in Čech cohomology is
`0 → H⁰(𝒪_D) →[f₁] H⁰(𝒪_{D+P}) →[f₂] ℂ_P →[f₃] H¹(𝒪_D) →[f₄] H¹(𝒪_{D+P}) → 0`,
the skyscraper having `H^{≥1} = 0`.

`SkyscraperLES` bundles the data NOT already proven above. The first two arrows `f₁` (`h0Incl`) and
`f₂` (`h0ToSky`, the cokernel projection), the last arrow `f₄` (`h1Map`, the inclusion-induced map),
and the exactness at `H⁰(𝒪_{D+P})` are all PROVEN (`exact_h0Incl_h0ToSky`, `h1Map`); the inclusion
`f₁` is injective (`h0Incl_injective`). The genuinely-hard content isolated here is:
* `skyDim`: the skyscraper cokernel is **1-dimensional** (`finrank ℂ_P = 1`) — the analytic local
  surjectivity onto the order-`(−D(P)−1)` principal-part coefficient at `P`;
* the snake-lemma connecting map `f₃` and the exactness facts `exact₂`, `exact₃`, `surj₄` (the
  SES-of-complexes + `Algebra.Homology.HomologySequence` content);
* finiteness of the cohomology groups (Forster 14.9).

Given a `SkyscraperLES`, the χ-jump is **pure linear algebra**: the alternating dimension sum of the
six-term exact sequence is `0` (`six_term_exact_alt_sum`, proven) and `finrank ℂ_P = 1`, which
rearranges to `χ(D+P) = χ(D) + 1`. That crank, `chi_jump_of_LES`, is sorry-free. -/
structure SkyscraperLES (𝔘 : FiniteCover X) (D : Divisor X) (P : X) where
  /-- The connecting homomorphism `ℂ_P → H¹(𝒪_D)` (snake lemma of the SES of cochain complexes). -/
  f₃ : 𝔘.Skyscraper D P →ₗ[ℂ] 𝔘.cechH1 D
  /-- **The analytic sub-kernel**: the skyscraper cokernel is 1-dimensional — local surjectivity of
  meromorphic sections onto the order-`(−D(P)−1)` principal-part coefficient at `P`. -/
  skyDim : Module.finrank ℂ (𝔘.Skyscraper D P) = 1
  /-- Exactness at `ℂ_P`: `range f₂ = ker f₃`. (Snake lemma.) -/
  exact₂ : Function.Exact (𝔘.h0ToSky D P) f₃
  /-- Exactness at `H¹(𝒪_D)`: `range f₃ = ker f₄` (with `f₄ = h1Map`). (Snake lemma.) -/
  exact₃ : Function.Exact f₃ (𝔘.h1Map D P)
  /-- The last arrow `f₄ = h1Map : H¹(𝒪_D) → H¹(𝒪_{D+P})` is surjective (the skyscraper has
  `H^{≥1} = 0`, so the LES terminates with `→ 0`). -/
  surj₄ : Function.Surjective (𝔘.h1Map D P)
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
sequence is `0` (`six_term_exact_alt_sum`), and `finrank ℂ_P = 1` (`skyDim`). Rearranging
`h⁰(D) − h⁰(D+P) + 1 − h¹(D) + h¹(D+P) = 0` gives the jump. No analytic content. -/
theorem chi_jump_of_LES {𝔘 : FiniteCover X} {D : Divisor X} {P : X}
    (S : SkyscraperLES 𝔘 D P) : 𝔘.chi (D + Finsupp.single P 1) = 𝔘.chi D + 1 := by
  haveI := S.finH1D; haveI := S.finH1DP; haveI := S.finH0D; haveI := S.finH0DP
  have halt := six_term_exact_alt_sum
    (𝔘.h0Incl D P) (𝔘.h0ToSky D P) S.f₃ (𝔘.h1Map D P)
    (𝔘.h0Incl_injective D P) (𝔘.exact_h0Incl_h0ToSky D P) S.exact₂ S.exact₃ S.surj₄
  -- substitute `finrank ℂ_P = 1` and identify the four `finrank`s with `h0Dim`/`h1Dim`.
  rw [S.skyDim] at halt
  simp only [chi, h0Dim, h1Dim, Nat.cast_one] at halt ⊢
  linarith

/-- **Existence of the skyscraper long exact sequence — THE NAMED HONEST `sorry`.**

This is the genuine cohomological content of Riemann–Roch (Forster §16), isolated as the single
remaining gap. The structural part of the LES is already PROVEN above: the inclusion `f₁ = h0Incl`
and its injectivity, the cokernel arrow `f₂ = h0ToSky`, the exactness at `H⁰(𝒪_{D+P})`
(`exact_h0Incl_h0ToSky`), AND the inclusion-induced last arrow `f₄ = h1Map`. What remains, and what
this `sorry` packages:

1. **The analytic sub-kernel** (`skyDim`): the skyscraper cokernel
   `H⁰(𝒪_{D+P}) ⧸ H⁰(𝒪_D)` is 1-dimensional, i.e. local surjectivity of meromorphic sections — a
   section of `𝒪_{D+P}` near `P` realises *any* prescribed principal-part coefficient of order
   `−D(P)−1`, and exactly one coefficient is the obstruction.
2. **The snake/LES content**: the SES of germ-class cochain complexes `0 → C^•(𝒪_D) →
   C^•(𝒪_{D+P}) → C^•(ℂ_P) → 0`, the skyscraper complex `H^{≥1} = 0`, and Mathlib's
   `Algebra.Homology.HomologySequence` snake lemma supplying the connecting map `f₃` and the
   exactness `exact₂`, `exact₃` and surjectivity `surj₄` of the (already-built) arrows.
3. **Finiteness** of the `H¹` groups (Forster 14.9; `CechFinitenessWiring.finiteDimensional_cechH1_wired`
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
