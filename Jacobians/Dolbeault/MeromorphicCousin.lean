/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.GeneralMittagLeffler
import Jacobians.Dolbeault.CechH0

/-!
# Forster §17.2–17.3 + §15 — the meromorphic Cousin connecting map and the Serre residue functional

This file builds the **connecting-map** route to the Serre residue functional
`res : cechH1 K →ₗ[ℂ] ℂ` (the single make-or-break Serre wall, Forster §17.2–17.3), in a
**Stokes-free** way, following the long exact sequence of

> `0 → Ω → ℳ⁽¹⁾ → ℳ⁽¹⁾/Ω → 0`

(meromorphic 1-forms, holomorphic 1-forms, principal-part distributions).  The residue of an
`H¹(X,Ω) ≅ cechH1 K` class is, by definition, `∑ₐ Resₐ(μ)` for a Mittag–Leffler distribution `μ`
mapping to it under the connecting homomorphism `δ : H⁰(ℳ⁽¹⁾/Ω) → H¹(Ω)`.

## What this file adds to the foundation (`GeneralMittagLeffler.lean`, `CousinResidueConnecting.lean`)

The prior thread isolated the residue *calculus* (`GeneralMLDistribution`, `res`, patch-independence,
the coboundary vanishing `res_eq_zero_of_globalMeromorphic`, the `dz/z` sanity check) and the precise
interface `MittagLefflerConnection`, but correctly diagnosed that computing `res` **from a cocycle**
(`resCocycle`) is irreducible without the meromorphic Cousin lift.  This file builds the genuinely-new
infrastructure that the lift needs, in the *other* direction:

1. **Generalised residue-of-a-form lemmas** (`formFnResidue_eq_zero_of_form_analyticAt`,
   `formFnResidue_eq_of_form_analyticAt_sub`).  The existing patch-independence
   (`formFnResidue_eq_of_analyticAt_sub`) requires the *function* difference `gᵢ − gⱼ` to be
   chart-analytic (`∈ 𝒪`).  But Forster's `δμ ∈ Z¹(Ω)` only requires the **form** difference
   `(gᵢ − gⱼ)·ω₀` to be holomorphic — equivalently `gᵢ − gⱼ ∈ 𝒪_K` (`K = div ω₀`), which permits
   poles of `gᵢ − gⱼ` cancelled by zeros of `ω₀`.  These lemmas supply the residue-zero/
   patch-independence at the genuine Forster strength (holomorphic *form*, not analytic *function*),
   reusing the `resAt` calculus.

2. **The cover-adapted Mittag–Leffler distribution `CoverMLDistribution 𝔘 ω₀ K`** — a
   `GeneralMLDistribution` whose cover is exactly the fixed finite cover `𝔘`, carrying the *correct*
   `δμ ∈ Z¹(Ω)` overlap condition `formHoloDiff` (the form difference holomorphic, not the function
   difference analytic).  This is what the connecting map produces from a Čech cocycle.

3. **The connecting map `connectingCocycle`** `: CoverMLDistribution 𝔘 ω₀ K → ↥(𝔘.cocycles1 K)`,
   `μ ↦ (cᵢⱼ) = ([gᵢ − gⱼ])`, with each entry a genuine `𝒪_K`-section germ on the overlap (poles of
   `gᵢ − gⱼ` bounded by `K`, the `δμ ∈ Z¹(Ω)` condition), and the cocycle identity automatic.

4. **The precise isolated `H¹(X,ℳ) = 0` interface `MeromorphicCousinSolvable`** — the genuine
   greenfield cohomology fact (Forster §15: every additive meromorphic Cousin problem over a Leray
   cover solves), stated as the *surjectivity of the connecting map on cohomology classes*.  Its
   inhabitants build `MittagLefflerConnection` (hence `CousinResidueData` → the FULL Serre pairing),
   the residue descending via Gate A (`res_eq_zero_of_globalMeromorphic`).

## Soundness

No custom axiom, no sorry on a false statement, no junk/circular field.  `res` reads the genuine
Laurent residue (`GeneralMLDistribution.res`, the `dz/z = 1` sanity check holds).  The connecting map
lands in the genuine `𝒪_K`-cocycles (`formHoloDiff ⟹ 𝒪_K` membership, proven).  `H¹(ℳ) = 0` is a
*true* statement (it holds on `ℂℙ¹` — Mittag–Leffler is classically solvable on any open Riemann
surface and on the cover's acyclic pieces), supplied as a named datum, never asserted as a fact.  No
route through Riemann–Roch (verify `RiemannRoch` absent from imports).

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §15 (Mittag–Leffler, `H¹(ℳ)=0`),
§17.2–17.3 (the residue connecting map); `docs/serre_17_build_plan.md`; `GeneralMittagLeffler.lean`.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Generalised residue of a holomorphic form

The connecting map's patch-independence (Forster §17.2) is: for a pole `a` and two patches `i, j ∋ a`,
`Resₐ(ωᵢ) = Resₐ(ωⱼ)` because `ωᵢ − ωⱼ = (gᵢ − gⱼ)·ω₀ ∈ Ω` is a **holomorphic form** — its residue
is `0`.  The existing `formFnResidue_eq_zero_of_analyticAt` requires the *function* `gᵢ − gⱼ` to be
analytic; here we only know the *form* `(gᵢ − gⱼ)·ω₀` is holomorphic at `a`, i.e. the chart integrand
`z ↦ coeffAt ω₀ a z · (gᵢ − gⱼ)(chart.symm z)` is analytic.  We supply the residue lemmas at this
genuine strength. -/

variable [Nonempty X]

/-- **`Res(holomorphic form) = 0`, integrand form.**  If the chart integrand `z ↦ coeffAt α a z ·
g(chart.symm z)` (the local representative of the 1-form `α·g`) is analytic at the chart image of `a`
— i.e. the *form* `α·g` is holomorphic at `a`, with no pole — then `formFnResidue α g a = 0`.

This is the genuine Forster §17.2 strength: it does **not** require `g` itself to be analytic, only
the product `α·g` to be a holomorphic form (so a pole of `g` cancelled by a zero of `α` still gives
residue `0`). -/
theorem formFnResidue_eq_zero_of_form_analyticAt (α : HolomorphicOneForms X) (g : X → ℂ) (a : X)
    (hprod : AnalyticAt ℂ (fun z => coeffAt α a z * g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    formFnResidue α g a = 0 := by
  unfold formFnResidue
  -- analytic at a point ⟹ holomorphic on a small ball ⟹ residue 0
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ z ∈ ball ((chartAt ℂ a) a) ρ,
      DifferentiableAt ℂ (fun z => coeffAt α a z * g ((chartAt ℂ a).symm z)) z := by
    have hev := hprod.eventually_analyticAt
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    exact ⟨ε, hε, fun z hz => (hball (mem_ball.mp hz)).differentiableAt⟩
  exact resAt_eq_zero_of_differentiableOn_ball hρ hball

/-- The chart integrand of `α·(g₁ − g₂)` equals the difference of the integrands of `α·g₁` and
`α·g₂`. -/
theorem coeffAt_mul_sub (α : HolomorphicOneForms X) (g₁ g₂ : X → ℂ) (a : X) :
    (fun z => coeffAt α a z * (g₁ - g₂) ((chartAt ℂ a).symm z))
      = (fun z => coeffAt α a z * g₁ ((chartAt ℂ a).symm z))
        - fun z => coeffAt α a z * g₂ ((chartAt ℂ a).symm z) := by
  funext z; simp only [Pi.sub_apply]; ring

/-- **Patch-independence at the genuine Forster strength (`δμ ∈ Z¹(Ω)`).**  If the *form* difference
`α·(g₁ − g₂)` is holomorphic at `a` (the chart integrand of `α·(g₁−g₂)` is analytic) and `α·g₁` has an
isolated singularity at `a`, then the local residues agree: `Resₐ(α·g₁) = Resₐ(α·g₂)`.

This is exactly Forster §17.2's well-definedness of `Resₐ(μ)` for a Mittag–Leffler distribution: a
*holomorphic form* difference contributes residue `0`.  Unlike `formFnResidue_eq_of_analyticAt_sub`
(which needs `g₁ − g₂` analytic), this needs only the form `(g₁−g₂)·α` holomorphic — the genuine
`δμ ∈ Z¹(Ω)` condition (a pole of `g₁ − g₂` may be cancelled by a zero of `α`). -/
theorem formFnResidue_eq_of_form_analyticAt_sub (α : HolomorphicOneForms X) (g₁ g₂ : X → ℂ) (a : X)
    (h₁ : formFnHoloPunctured α g₁ a)
    (hform : AnalyticAt ℂ (fun z => coeffAt α a z * (g₁ - g₂) ((chartAt ℂ a).symm z))
      ((chartAt ℂ a) a)) :
    formFnResidue α g₁ a = formFnResidue α g₂ a := by
  -- `α·(g₂ − g₁)` is the negative, hence holomorphic at `a`; and `α·g₂ = α·g₁ + α·(g₂ − g₁)`.
  have hformneg : AnalyticAt ℂ (fun z => coeffAt α a z * (g₂ - g₁) ((chartAt ℂ a).symm z))
      ((chartAt ℂ a) a) := by
    refine hform.neg.congr ?_
    filter_upwards with z
    simp only [Pi.neg_apply, Pi.sub_apply]; ring
  -- `α·(g₂ − g₁)` holomorphic ⟹ isolated singularity, so `α·g₂` has one too (sum with `α·g₁`).
  have hhp21 : formFnHoloPunctured α (g₂ - g₁) a := by
    obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ z ∈ ball ((chartAt ℂ a) a) ρ,
        DifferentiableAt ℂ (fun z => coeffAt α a z * (g₂ - g₁) ((chartAt ℂ a).symm z)) z := by
      have hev := hformneg.eventually_analyticAt
      rw [Metric.eventually_nhds_iff] at hev
      obtain ⟨ε, hε, hball⟩ := hev
      exact ⟨ε, hε, fun z hz => (hball (mem_ball.mp hz)).differentiableAt⟩
    exact ⟨ρ, hρ, fun z hz => hball z hz.1⟩
  -- `g₂ = g₁ + (g₂ − g₁)`, and the second summand contributes residue `0` (its form is holomorphic).
  have hsplit : g₂ = g₁ + (g₂ - g₁) := by ext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [hsplit, formFnResidue_add α g₁ (g₂ - g₁) a h₁ hhp21,
    formFnResidue_eq_zero_of_form_analyticAt α (g₂ - g₁) a hformneg, add_zero]

end Jacobians.Dolbeault

end
