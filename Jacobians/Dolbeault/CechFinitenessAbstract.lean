/-
  The abstract Forster-14.9 reduction: Čech `H¹` is finite-dimensional once the cochain restriction
  to a shrinking is compact (Montel) and the Leray-combined map is surjective. Cochain Banach spaces
  appear here as abstract Banach spaces — NO manifold/Čech dependency — so this is the clean logical
  core of the finiteness node, built directly on the Schwartz lemma (Forster 14.8).

  STEP 3 of `docs/cech_finiteness_research.md`. The two remaining manifold-side inputs it consumes —
  `ρ` compact (Montel; from `CechFiniteness.isCompact_closure_restrict_bddHolo` + `BddHol`) and the
  Leray surjectivity (`H¹(disk,𝒪)=0`, from the proven G1 `DbarDisk`) — are all that stands between
  this and `DolbeaultLadder.finiteDimensional_cechH1`.
-/
import Jacobians.Dolbeault.SchwartzFiniteness

open Jacobians.SchwartzFiniteness ContinuousLinearMap

namespace Jacobians.Dolbeault.CechFiniteness

/-- **Abstract finiteness reduction (Forster 14.9 core).** Let `δ : C0 →L Z1V` (the coboundary
`C⁰(𝔙) → Z¹(𝔙)`) and `ρ : Z1U →L Z1V` (the restriction `Z¹(𝔘) → Z¹(𝔙)`) be maps of Banach spaces
such that the combined map `(η,ξ) ↦ δη + ρξ` is surjective (the **Leray** condition — restriction is
onto on `H¹`) and `ρ` is a **compact** operator (**Montel**). Then `Z1V ⧸ range δ` (i.e. `H¹(𝔙)`) is
finite-dimensional.

Proof: with `A := δ⊕ρ` (surjective) and `K := 0⊕(−ρ)` (compact), `A + K = δ⊕0` so
`range (A+K) = range δ = B¹`; the Schwartz lemma gives `Z1V ⧸ range δ` finite-dimensional. -/
theorem finiteDimensional_h1_of_leray_compact
    {C0 Z1U Z1V : Type*}
    [NormedAddCommGroup C0] [NormedSpace ℂ C0] [CompleteSpace C0]
    [NormedAddCommGroup Z1U] [NormedSpace ℂ Z1U] [CompleteSpace Z1U]
    [NormedAddCommGroup Z1V] [NormedSpace ℂ Z1V] [CompleteSpace Z1V]
    (δ : C0 →L[ℂ] Z1V) (ρ : Z1U →L[ℂ] Z1V)
    (hsurj : Function.Surjective (fun p : C0 × Z1U => δ p.1 + ρ p.2))
    (hρ : IsCompactOperator ρ) :
    FiniteDimensional ℂ (Z1V ⧸ LinearMap.range δ.toLinearMap) := by
  set A : (C0 × Z1U) →L[ℂ] Z1V := δ.comp (fst ℂ C0 Z1U) + ρ.comp (snd ℂ C0 Z1U) with hA
  set K : (C0 × Z1U) →L[ℂ] Z1V := -(ρ.comp (snd ℂ C0 Z1U)) with hK
  have hAsurj : Function.Surjective A := hsurj
  have hKcompact : IsCompactOperator K := (hρ.comp_clm (snd ℂ C0 Z1U)).neg
  have hfd := finiteDimensional_quotient_range_add_compact A hAsurj K hKcompact
  have hAK : A + K = δ.comp (fst ℂ C0 Z1U) := by rw [hA, hK]; abel
  rw [hAK] at hfd
  have hrange : LinearMap.range (δ.comp (fst ℂ C0 Z1U)).toLinearMap
      = LinearMap.range δ.toLinearMap := by
    rw [ContinuousLinearMap.coe_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.2 (Prod.fst_surjective (β := Z1U)), Submodule.map_top]
  rwa [hrange] at hfd

end Jacobians.Dolbeault.CechFiniteness
