/-
  Dolbeault ladder — the concrete Čech complex and `H¹`, on a fixed finite cover.

  Following `docs/dolbeault_ladder_derisk.md`. Design note (a module-instance diamond, found while
  building this): if the cochain spaces are `Π p, ↥(OmegaD D …)` (products of submodule-coes of
  function spaces), the quotient `↥(ker δ¹) ⧸ …` fails `HasQuotient` synthesis — two defeq-but-not-
  syntactic `Module ℂ (↥U → ℂ)` paths (`Pi.module` vs the algebra-induced one) clash through the
  `Submodule.module` layer (cf. `reference_module_real_diamond`). Fix (and the standard Čech setup):
  the cochains are *raw* functions `Π p, (↥… → ℂ)` (a clean, diamond-free `ℂ`-module), and the sheaf
  condition `𝒪_D` is carried as a `Submodule` *within* that ambient. `H¹` is then a quotient over a
  submodule-coe of the raw function-Pi, which is diamond-free.

  Light scaffolding: definitions + `δ² = 0` and the dimensions, with the analytic content isolated
  downstream. The only `sorry`s reachable from here are the two mechanical restriction leaves in
  `CechSection` plus `δ² = 0` (also mechanical).
-/
import Jacobians.Dolbeault.CechSection

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- A finite open cover of `X`. For the Leray/Stein property used by finiteness one takes the `U i`
to be chart-disks; that refinement is recorded where needed, not here. -/
structure FiniteCover (X : Type*) [TopologicalSpace X] where
  ι : Type
  [fintype : Fintype ι]
  U : ι → Opens X
  covers : ⨆ i, U i = ⊤

attribute [instance] FiniteCover.fintype

namespace FiniteCover

variable (𝔘 : FiniteCover X) (D : Divisor X)

/-! ### Raw cochain spaces (products of full function spaces — diamond-free `ℂ`-modules). -/

/-- Raw 0-cochains: a function on each `↥(U i)`. -/
abbrev Cochain0 : Type _ := Π i, (𝔘.U i → ℂ)

/-- Raw 1-cochains: a function on each pairwise intersection. -/
abbrev Cochain1 : Type _ := Π p : 𝔘.ι × 𝔘.ι, (↥(𝔘.U p.1 ⊓ 𝔘.U p.2) → ℂ)

/-- Raw 2-cochains: a function on each triple intersection. -/
abbrev Cochain2 : Type _ := Π t : 𝔘.ι × 𝔘.ι × 𝔘.ι, (↥(𝔘.U t.1 ⊓ 𝔘.U t.2.1 ⊓ 𝔘.U t.2.2) → ℂ)

/-- Raw restriction `(↥U → ℂ) → (↥V → ℂ)` for `V ≤ U`: precomposition with the open inclusion. -/
noncomputable abbrev rawRestrict {U V : Opens X} (h : V ≤ U) : (U → ℂ) →ₗ[ℂ] (V → ℂ) :=
  LinearMap.funLeft ℂ ℂ (openIncl h)

/-- Čech differential `δ⁰ : C⁰ → C¹`, `(δ⁰f)_{ij} = f_j|_{U_i∩U_j} − f_i|_{U_i∩U_j}`. -/
noncomputable def cechDelta0 : 𝔘.Cochain0 →ₗ[ℂ] 𝔘.Cochain1 :=
  LinearMap.pi fun p =>
    rawRestrict inf_le_right ∘ₗ LinearMap.proj p.2 - rawRestrict inf_le_left ∘ₗ LinearMap.proj p.1

/-- Čech differential `δ¹ : C¹ → C²`,
`(δ¹g)_{ijk} = g_{jk}|_{ijk} − g_{ik}|_{ijk} + g_{ij}|_{ijk}`. -/
noncomputable def cechDelta1 : 𝔘.Cochain1 →ₗ[ℂ] 𝔘.Cochain2 :=
  LinearMap.pi fun t =>
    rawRestrict (le_inf (inf_le_left.trans inf_le_right) inf_le_right) ∘ₗ LinearMap.proj (t.2.1, t.2.2)
      - rawRestrict (le_inf (inf_le_left.trans inf_le_left) inf_le_right) ∘ₗ LinearMap.proj (t.1, t.2.2)
      + rawRestrict inf_le_left ∘ₗ LinearMap.proj (t.1, t.2.1)

/-- `δ² = 0`: the alternating sum of restrictions cancels. Nested restrictions are precompositions
with open inclusions, which evaluate to `⟨x.1, _⟩` independently of the `≤` proof (proof-irrelevance),
so the six terms `f_k − f_j − f_k + f_i + f_j − f_i` pair up and vanish. -/
theorem cechDelta1_comp_cechDelta0 : (𝔘.cechDelta1) ∘ₗ (𝔘.cechDelta0) = 0 := by
  refine LinearMap.ext fun f => ?_
  funext t
  obtain ⟨i, j, k⟩ := t
  funext x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, Pi.zero_apply, cechDelta0, cechDelta1,
    rawRestrict, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.coe_comp,
    Function.comp_apply, LinearMap.proj_apply, LinearMap.funLeft_apply, Pi.sub_apply, Pi.add_apply,
    openIncl]
  ring

/-! ### The `𝒪_D` sheaf condition, as submodules of the raw cochain spaces. -/

/-- 0-cochains that are `𝒪_D`-sections on each `U i`. -/
def sections0 : Submodule ℂ 𝔘.Cochain0 where
  carrier := {f | ∀ i, f i ∈ OmegaD D (𝔘.U i)}
  add_mem' hf hg i := add_mem (hf i) (hg i)
  zero_mem' i := Submodule.zero_mem _
  smul_mem' c f hf i := Submodule.smul_mem _ c (hf i)

/-- 1-cochains that are `𝒪_D`-sections on each pairwise intersection. -/
def sections1 : Submodule ℂ 𝔘.Cochain1 where
  carrier := {g | ∀ p, g p ∈ OmegaD D (𝔘.U p.1 ⊓ 𝔘.U p.2)}
  add_mem' hf hg p := add_mem (hf p) (hg p)
  zero_mem' p := Submodule.zero_mem _
  smul_mem' c g hg p := Submodule.smul_mem _ c (hg p)

/-- The `𝒪_D` 1-cocycles: `ker δ¹` intersected with the `𝒪_D` sections. -/
noncomputable def cocycles1 : Submodule ℂ 𝔘.Cochain1 :=
  LinearMap.ker 𝔘.cechDelta1 ⊓ 𝔘.sections1 D

/-- The `𝒪_D` 1-coboundaries: the image of the `𝒪_D` 0-sections under `δ⁰`. -/
noncomputable def coboundaries1 : Submodule ℂ 𝔘.Cochain1 :=
  Submodule.map 𝔘.cechDelta0 (𝔘.sections0 D)

/-- **Čech `H¹(𝔘, 𝒪_D) = Z¹/B¹`** — cocycles modulo coboundaries, a `ℂ`-module. The ambient is the
raw function-Pi `Cochain1`, so the quotient is diamond-free. (`B¹ ⊆ Z¹` holds by `δ² = 0` and
restriction preserving `𝒪_D`; the quotient is well-formed regardless.) -/
abbrev cechH1 : Type _ :=
  ↥(𝔘.cocycles1 D) ⧸ (𝔘.coboundaries1 D).submoduleOf (𝔘.cocycles1 D)

/-- `H⁰(𝔘, 𝒪_D)` = global matching `𝒪_D`-sections = `ker δ⁰ ∩ sections`. -/
noncomputable def globalSections : Submodule ℂ 𝔘.Cochain0 :=
  LinearMap.ker 𝔘.cechDelta0 ⊓ 𝔘.sections0 D

/-- `h⁰(D)` (Forster's `h⁰(X, 𝒪_D)`). -/
noncomputable def h0Dim : ℕ := Module.finrank ℂ ↥(𝔘.globalSections D)

/-- `h¹(D)` (Forster's `h¹(X, 𝒪_D)`). -/
noncomputable def h1Dim : ℕ := Module.finrank ℂ (𝔘.cechH1 D)

end FiniteCover

end Jacobians.Dolbeault
