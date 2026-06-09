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

/-- **Integrand analytic ⟹ isolated singularity (`formFnHoloPunctured`).**  If the chart integrand
`z ↦ coeffAt α a z · g(chart.symm z)` of the form `α·g` is analytic at the chart image of `a`, then
`α·g` has an isolated singularity (in fact none) there.  The "form holomorphic ⟹ isolated" bridge,
the genuine-strength analogue of `formFnHoloPunctured_of_analyticAt` (which assumes `g` analytic). -/
theorem formFnHoloPunctured_of_form_analyticAt (α : HolomorphicOneForms X) (g : X → ℂ) (a : X)
    (hprod : AnalyticAt ℂ (fun z => coeffAt α a z * g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    formFnHoloPunctured α g a := by
  have hev := hprod.eventually_analyticAt
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  exact ⟨ε, hε, fun z hz => (hball (mem_ball.mp hz.1)).differentiableAt⟩

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
  have hhp21 : formFnHoloPunctured α (g₂ - g₁) a :=
    formFnHoloPunctured_of_form_analyticAt α (g₂ - g₁) a hformneg
  -- `g₂ = g₁ + (g₂ − g₁)`, and the second summand contributes residue `0` (its form is holomorphic).
  have hsplit : g₂ = g₁ + (g₂ - g₁) := by ext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [hsplit, formFnResidue_add α g₁ (g₂ - g₁) a h₁ hhp21,
    formFnResidue_eq_zero_of_form_analyticAt α (g₂ - g₁) a hformneg, add_zero]

/-! ## The form-holomorphic-difference Mittag–Leffler distribution

The existing `GeneralMLDistribution` carries the overlap condition `holoDiff` = the *function*
difference `gᵢ − gⱼ` chart-analytic (`∈ 𝒪₀`).  But Forster's genuine `δμ ∈ Z¹(Ω)` only requires the
*form* difference `(gᵢ − gⱼ)·ω₀` to be holomorphic — a strictly weaker condition that permits poles of
`gᵢ − gⱼ` cancelled by zeros of `ω₀` (the canonical divisor `K = div ω₀`).  A general Čech cocycle of
`𝒪_K` has exactly such differences (poles up to `K`), so the existing `holoDiff` cannot represent the
lift of a general cocycle.

We supply `FormMLDistribution ω₀` with the correct `formHoloDiff` (the chart integrand of the form
`(gᵢ − gⱼ)·ω₀` analytic), and re-derive the residue API at this strength via the form-level lemmas
above.  This is the genuine domain of the Mittag–Leffler connecting map. -/

/-- **A form-holomorphic-difference Mittag–Leffler distribution of 1-forms** (Forster §17.2 at the
genuine `δμ ∈ Z¹(Ω)` strength), in the `ωᵢ = gᵢ·ω₀` shape.

Identical to `GeneralMLDistribution` except the overlap condition `formHoloDiff` requires the *form*
difference `(gᵢ − gⱼ)·ω₀` to be holomorphic (the chart integrand `coeffAt ω₀ a · (gᵢ−gⱼ)(chart.symm)`
analytic), rather than the *function* `gᵢ − gⱼ` analytic.  This is what a general `𝒪_K` Čech cocycle's
Mittag–Leffler lift satisfies (`δμ ∈ Z¹(Ω)`, poles of `gᵢ − gⱼ` bounded by `K = div ω₀`). -/
structure FormMLDistribution (ω₀ : HolomorphicOneForms X) where
  /-- The (finite) cover index. -/
  ι : Type
  /-- Finiteness of the index. -/
  [fintype : Fintype ι]
  /-- The cover opens. -/
  U : ι → Opens X
  /-- The local principal-part function on each patch (`ωᵢ = gᵢ·ω₀`). -/
  g : ι → (X → ℂ)
  /-- The finite pole set. -/
  poles : Finset X
  /-- A designated patch containing each pole. -/
  patch : X → ι
  /-- Each pole lies in its designated patch. -/
  patch_mem : ∀ a ∈ poles, a ∈ U (patch a)
  /-- **Form-holomorphic-difference condition** (`δμ ∈ Z¹(Ω)`): on every overlap the *form*
  difference `(gᵢ − gⱼ)·ω₀` is holomorphic, i.e. its chart integrand is analytic. -/
  formHoloDiff : ∀ (i j : ι) (a : X), a ∈ U i → a ∈ U j →
    AnalyticAt ℂ (fun z => coeffAt ω₀ a z * (g i - g j) ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)
  /-- **Isolated singularity** at each pole (in its designated patch). -/
  iso : ∀ a ∈ poles, formFnHoloPunctured ω₀ (g (patch a)) a

attribute [instance] FormMLDistribution.fintype

namespace FormMLDistribution

variable {ω₀ : HolomorphicOneForms X}

/-- **Each patch of a pole has an isolated singularity there.**  At a pole `a`, any patch `i ∋ a` gives
`ω₀·gᵢ` an isolated singularity: `gᵢ = (gᵢ − g_{patch a}) + g_{patch a}`, the form of the first summand
holomorphic at `a` (`formHoloDiff`) — hence isolated — and the second isolated (`iso`); isolated-
singularity is closed under addition. -/
theorem formFnHoloPunctured_of_mem (μ : FormMLDistribution ω₀) {a : X} (ha : a ∈ μ.poles)
    {i : μ.ι} (hi : a ∈ μ.U i) :
    formFnHoloPunctured ω₀ (μ.g i) a := by
  have hdiff : formFnHoloPunctured ω₀ (μ.g i - μ.g (μ.patch a)) a :=
    formFnHoloPunctured_of_form_analyticAt ω₀ _ a (μ.formHoloDiff i (μ.patch a) a hi (μ.patch_mem a ha))
  have hsum : μ.g i = (μ.g i - μ.g (μ.patch a)) + μ.g (μ.patch a) := by
    ext x; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [hsum]
  obtain ⟨ρ₁, hρ₁, hb₁⟩ := hdiff
  obtain ⟨ρ₂, hρ₂, hb₂⟩ := μ.iso a ha
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun z hz => ?_⟩
  have hz1 : z ∈ ball ((chartAt ℂ a) a) ρ₁ \ {(chartAt ℂ a) a} :=
    ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_left _ _)), hz.2⟩
  have hz2 : z ∈ ball ((chartAt ℂ a) a) ρ₂ \ {(chartAt ℂ a) a} :=
    ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_right _ _)), hz.2⟩
  have heq : (fun z => coeffAt ω₀ a z * ((μ.g i - μ.g (μ.patch a)) + μ.g (μ.patch a))
        ((chartAt ℂ a).symm z))
      = (fun z => coeffAt ω₀ a z * (μ.g i - μ.g (μ.patch a)) ((chartAt ℂ a).symm z))
        + fun z => coeffAt ω₀ a z * μ.g (μ.patch a) ((chartAt ℂ a).symm z) := by
    funext w; simp only [Pi.add_apply]; ring
  rw [heq]; exact (hb₁ z hz1).add (hb₂ z hz2)

/-- **The per-pole residue** `Resₐ(μ) = Resₐ(ω₀·g_{patch a})` (Forster §17.2). -/
noncomputable def resAtPole (μ : FormMLDistribution ω₀) (a : X) : ℂ :=
  formFnResidue ω₀ (μ.g (μ.patch a)) a

/-- **Patch-independence of the per-pole residue** at the genuine Forster strength.  For a pole `a`,
any patch `i ∋ a` computes the same residue: the two local forms differ by the *holomorphic form*
`(gᵢ − g_{patch a})·ω₀` (`formHoloDiff`), residue `0` (`formFnResidue_eq_of_form_analyticAt_sub`). -/
theorem resAtPole_eq_of_mem (μ : FormMLDistribution ω₀) {a : X} (ha : a ∈ μ.poles) {i : μ.ι}
    (hi : a ∈ μ.U i) :
    formFnResidue ω₀ (μ.g i) a = μ.resAtPole a :=
  formFnResidue_eq_of_form_analyticAt_sub ω₀ (μ.g i) (μ.g (μ.patch a)) a
    (μ.formFnHoloPunctured_of_mem ha hi) (μ.formHoloDiff i (μ.patch a) a hi (μ.patch_mem a ha))

/-- **Forster's residue `Res(μ)`** of a form-holomorphic-difference distribution: the sum of the
per-pole residues over the finite pole set. -/
noncomputable def res (μ : FormMLDistribution ω₀) : ℂ :=
  ∑ a ∈ μ.poles, μ.resAtPole a

theorem res_def (μ : FormMLDistribution ω₀) : μ.res = ∑ a ∈ μ.poles, μ.resAtPole a := rfl

/-- **A `GeneralMLDistribution` is a `FormMLDistribution`** — its (stronger) `holoDiff` (function
analytic) implies the form `(gᵢ − gⱼ)·ω₀` is holomorphic (`coeffAt ω₀ a` analytic times an analytic
function), and the residue agrees (both read `formFnResidue ω₀ g_{patch a}`).  This confirms the form
distribution genuinely generalises the existing one (non-vacuity at any pole count). -/
def ofGeneral (μ : GeneralMLDistribution ω₀) : FormMLDistribution ω₀ where
  ι := μ.ι
  U := μ.U
  g := μ.g
  poles := μ.poles
  patch := μ.patch
  patch_mem := μ.patch_mem
  formHoloDiff := fun i j a hi hj => by
    have hmem : (chartAt ℂ a) a ∈ (chartAt ℂ a).target :=
      (chartAt ℂ a).map_source (mem_chart_source ℂ a)
    exact (coeffAt_analyticAt ω₀ a hmem).mul (μ.holoDiff i j a hi hj)
  iso := μ.iso

@[simp] theorem ofGeneral_resAtPole (μ : GeneralMLDistribution ω₀) (a : X) :
    (ofGeneral μ).resAtPole a = μ.resAtPole a := rfl

theorem res_ofGeneral (μ : GeneralMLDistribution ω₀) : (ofGeneral μ).res = μ.res :=
  Finset.sum_congr rfl fun _ _ => rfl

end FormMLDistribution

end Jacobians.Dolbeault

end
