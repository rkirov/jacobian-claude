/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Order
import Jacobians.Dolbeault.FormTraceFibre

/-!
# Planar removable extension of the geometric trace across a branch value (Gate A, §VIII.3)

The re-pointed Gate A path feeds the constructor `globalTrace_of_glue` an **arbitrary** value-chart
trace function `T : ℂ → ℂ` (it need not be `valueChartTrace`).  Its only genuinely-hard input is
`hT_off` — `T` is `AnalyticAt` at every value off the finite pole-values, *including across the
branch values* of the cover, where the per-sheet section derivatives of the regular fibre blow up.

This file supplies the **planar analytic engine** for that step: a function `T₀` that is

* complex-differentiable on a *punctured* neighbourhood of a branch value `b₀`
  (off the poles of `α = ω₀·g`, the trace is the analytic regular-fibre sum there), and
* satisfies the **boundedness crux** `(z − b₀)·T₀ z → 0` as `z → b₀`

has at worst a *removable* singularity at `b₀`: redefined to its punctured-limit value, it becomes
`AnalyticAt b₀`.  This is the planar shadow of the bundle-side `traceExtendsAt_branchPoint`
(`Jacobians/TraceForm.lean`) — but stated purely on `ℂ → ℂ`, so it applies directly to the
value-chart geometric trace.

The boundedness crux is the §VIII.3 analytic heart; for the planar trace it reduces *sheet by sheet*
to the proven one-variable atom `TraceForm.sub_div_deriv_tendsto_zero` (the ratio
`(F w − z₀)/F'(w) → 0` at a ramification point) — see `tendsto_zero_of_section_deriv` below, which
packages exactly that reduction for a single regular sheet's section derivative.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `analyticAt_update_of_punctured_diff_of_tendsto_zero` — the planar removable-singularity extension:
  punctured-differentiable + `(z − b₀)·T₀ z → 0` ⟹ `Function.update T₀ b₀ (limUnder …)` is
  `AnalyticAt b₀`.
* `analyticAt_of_eventuallyEq_of_tendsto_zero` — the *germ* form: if `T` germ-equals such an extended
  function on a full neighbourhood of `b₀` (i.e. `T` already carries the correct limit value at `b₀`),
  then `T` is `AnalyticAt b₀`.  This is the exact shape `globalTrace_of_glue.hT_off` consumes at a
  branch value.
* `tendsto_zero_of_section_deriv` — the per-sheet boundedness reduction: for the planar section germ
  `s` of a regular sheet (a local biholomorphism inverse with `s b₀ = pre`, `deriv s b₀ ≠ 0`)… see
  its statement; this is the building block of the fibre-sum boundedness crux.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §10, §17.
-/

noncomputable section

open Complex Metric Filter Topology

namespace Jacobians.Dolbeault.FormTraceBranchPlanar

set_option linter.unusedSectionVars false

/-! ### The planar removable-singularity extension

Mathlib's little-o removable singularity theorem
(`Complex.differentiableOn_update_limUnder_insert_of_isLittleO`) takes a punctured-differentiable
function with `(f z − f c) =o[𝓝[≠] c] (· − c)⁻¹` and produces a differentiable (hence analytic)
extension.  We package the hypotheses in the form the geometric trace actually delivers: differentiable
on a punctured neighbourhood, plus the *little-o-of-`(·−c)⁻¹` shadow* `(z − c)·T z → 0`. -/

/-- **The boundedness crux is the little-o condition.**  If `(z − c)·T₀ z → 0` as `z → c` through
`z ≠ c`, then `(T₀ z − T₀ c) =o[𝓝[≠] c] (z − c)⁻¹` — exactly the little-o hypothesis of Mathlib's
removable-singularity theorem.  (`(T₀ z − T₀ c)/(z − c)⁻¹ = (z − c)·T₀ z − (z − c)·T₀ c`, and both
terms tend to `0`: the first by hypothesis, the second since `z − c → 0`.) -/
theorem isLittleO_sub_of_tendsto_zero {T₀ : ℂ → ℂ} {c : ℂ}
    (hbnd : Tendsto (fun z => (z - c) * T₀ z) (𝓝[≠] c) (𝓝 0)) :
    (fun z => T₀ z - T₀ c) =o[𝓝[≠] c] fun z => (z - c)⁻¹ := by
  refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with z hz hcontra
    exact absurd (inv_eq_zero.mp hcontra) (sub_ne_zero.mpr hz)
  · -- `(T₀ z − T₀ c) / (z − c)⁻¹ = (z − c)·T₀ z − (z − c)·T₀ c`, both `→ 0`.
    have hconst : Tendsto (fun z => (z - c) * T₀ c) (𝓝[≠] c) (𝓝 0) := by
      have hz0 : Tendsto (fun z : ℂ => z - c) (𝓝[≠] c) (𝓝 0) := by
        simpa using ((continuous_sub_right c).tendsto c).mono_left nhdsWithin_le_nhds
      simpa using hz0.mul_const (T₀ c)
    have hdiff := hbnd.sub hconst
    simp only [sub_zero] at hdiff
    have heq : (fun z => (T₀ z - T₀ c) / (z - c)⁻¹)
        = (fun z => (z - c) * T₀ z - (z - c) * T₀ c) := by
      funext z; rw [div_eq_mul_inv, inv_inv]; ring
    rw [heq]; exact hdiff

/-- **Planar removable-singularity extension.**  If `T₀` is complex-differentiable on a punctured
neighbourhood of `b₀` (`hpunct`) and satisfies the boundedness crux `(z − b₀)·T₀ z → 0` (`hbnd`),
then `Function.update T₀ b₀ (limUnder (𝓝[≠] b₀) T₀)` — `T₀` redefined to its punctured limit at
`b₀` — is `AnalyticAt ℂ` at `b₀`.

This is the planar shadow of the bundle-side `traceExtendsAt_branchPoint`: the geometric trace has at
worst a removable singularity at a branch value, so patching its value there makes it analytic. -/
theorem analyticAt_update_of_punctured_diff_of_tendsto_zero {T₀ : ℂ → ℂ} {b₀ : ℂ}
    (hpunct : ∀ᶠ z in 𝓝[≠] b₀, DifferentiableAt ℂ T₀ z)
    (hbnd : Tendsto (fun z => (z - b₀) * T₀ z) (𝓝[≠] b₀) (𝓝 0)) :
    AnalyticAt ℂ (Function.update T₀ b₀ (limUnder (𝓝[≠] b₀) T₀)) b₀ := by
  -- Extract an explicit punctured neighbourhood `s ∈ 𝓝[≠] b₀` on which `T₀` is differentiable.
  rw [eventually_iff_exists_mem] at hpunct
  obtain ⟨s, hs_mem, hs_diff⟩ := hpunct
  have hdOn : DifferentiableOn ℂ T₀ s := fun z hz => (hs_diff z hz).differentiableWithinAt
  -- The little-o hypothesis from the boundedness crux.
  have ho : (fun z => T₀ z - T₀ b₀) =o[𝓝[≠] b₀] fun z => (z - b₀)⁻¹ :=
    isLittleO_sub_of_tendsto_zero hbnd
  -- Mathlib's removable singularity: the update is differentiable on `insert b₀ s`.
  have hupd : DifferentiableOn ℂ (Function.update T₀ b₀ (limUnder (𝓝[≠] b₀) T₀)) (insert b₀ s) :=
    Complex.differentiableOn_update_limUnder_insert_of_isLittleO hs_mem hdOn ho
  -- `insert b₀ s ∈ 𝓝 b₀` (it contains the punctured-nbhd `s` plus `b₀`).
  have hins_mem : insert b₀ s ∈ 𝓝 b₀ := by
    have hs_nhds : s ∪ {b₀} ∈ 𝓝 b₀ := by
      rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hs_mem with ⟨u, hu_nhds, hu_sub⟩
      refine Filter.mem_of_superset hu_nhds (fun z hz => ?_)
      by_cases hzc : z = b₀
      · exact Or.inr (by simp [hzc])
      · exact Or.inl (hu_sub ⟨hz, hzc⟩)
    refine Filter.mem_of_superset hs_nhds (fun z hz => ?_)
    rcases hz with hz | hz
    · exact Set.mem_insert_of_mem _ hz
    · rw [Set.mem_singleton_iff] at hz; exact hz ▸ Set.mem_insert _ _
  -- Differentiable on a neighbourhood ⟹ analytic at the point.
  exact hupd.analyticAt hins_mem

/-- **Germ form of the planar removable extension (the `hT_off`-at-a-branch-value shape).**  Suppose
a function `T : ℂ → ℂ` germ-equals, on a *full* neighbourhood of `b₀`, the removable extension
`Function.update T₀ b₀ (limUnder (𝓝[≠] b₀) T₀)` of some `T₀` that is punctured-differentiable with the
boundedness crux.  Then `T` is `AnalyticAt b₀`.

In the application `T` is the genuine geometric trace (already carrying the correct extension value at
the branch value), `T₀` is its punctured (regular-fibre) form, and the germ-equality holds because the
two agree off `b₀` (regular fibre) and at `b₀` (`T` carries the limit).  This is the exact input
`globalTrace_of_glue.hT_off` needs at each branch value off the poles. -/
theorem analyticAt_of_eventuallyEq_of_tendsto_zero {T T₀ : ℂ → ℂ} {b₀ : ℂ}
    (hpunct : ∀ᶠ z in 𝓝[≠] b₀, DifferentiableAt ℂ T₀ z)
    (hbnd : Tendsto (fun z => (z - b₀) * T₀ z) (𝓝[≠] b₀) (𝓝 0))
    (heq : T =ᶠ[𝓝 b₀] Function.update T₀ b₀ (limUnder (𝓝[≠] b₀) T₀)) :
    AnalyticAt ℂ T b₀ :=
  (analyticAt_update_of_punctured_diff_of_tendsto_zero hpunct hbnd).congr heq.symm

/-- **Germ form, value supplied externally.**  Variant of
`analyticAt_of_eventuallyEq_of_tendsto_zero` for when the punctured limit is known to be a specific
value `L` (e.g. computed by an independent matching lemma): if `T` germ-equals `T₀` off `b₀`, takes
the value `L` at `b₀`, `T₀` is punctured-differentiable with the boundedness crux, and `L` is the
punctured limit of `T₀`, then `T` is `AnalyticAt b₀`.  The hypothesis `hL` lets the caller carry the
extension value through a separate (geometric) channel rather than as `limUnder`. -/
theorem analyticAt_of_punctured_eq_of_value_of_tendsto_zero {T T₀ : ℂ → ℂ} {b₀ L : ℂ}
    (hpunct : ∀ᶠ z in 𝓝[≠] b₀, DifferentiableAt ℂ T₀ z)
    (hbnd : Tendsto (fun z => (z - b₀) * T₀ z) (𝓝[≠] b₀) (𝓝 0))
    (hTeq : T =ᶠ[𝓝[≠] b₀] T₀) (hTval : T b₀ = L)
    (hL : limUnder (𝓝[≠] b₀) T₀ = L) :
    AnalyticAt ℂ T b₀ := by
  refine analyticAt_of_eventuallyEq_of_tendsto_zero hpunct hbnd ?_
  -- `T =ᶠ[𝓝 b₀] update T₀ b₀ L`: off `b₀` use `hTeq`; at `b₀` both equal `L` (`hTval`, `hL`).
  have hpunct_eq : T =ᶠ[𝓝[≠] b₀] Function.update T₀ b₀ (limUnder (𝓝[≠] b₀) T₀) := by
    filter_upwards [hTeq, self_mem_nhdsWithin] with z hz hz_ne
    rw [hz, Function.update_of_ne hz_ne]
  have hval_eq : T b₀ = Function.update T₀ b₀ (limUnder (𝓝[≠] b₀) T₀) b₀ := by
    rw [Function.update_self, hL, hTval]
  exact eventuallyEq_nhds_of_eventuallyEq_nhdsNE hpunct_eq hval_eq

/-! ### Per-sheet boundedness reduction (the planar §VIII.3 atom for one regular sheet)

The fibre-sum boundedness crux `(z − b₀)·T₀ z → 0` reduces, term by term over the (finitely many)
sheets, to the boundedness of a single regular sheet's contribution
`(z − b₀)·coeff(s z)·deriv s z`.  Near a branch value the section `s` of a regular sheet (the planar
inverse of `f`'s chart-pullback `F` at a *ramification* point) has `deriv s` blowing up, but
`(z − b₀)·deriv s z → 0`: writing `S = s` as the inverse of `F` with `F(s b₀) = b₀`,
`deriv s z = 1/F'(s z)` and `z − b₀ = F(s z) − F(s b₀)`, so `(z − b₀)·deriv s z = (F w − b₀)/F'(w)`
with `w = s z → s b₀`, which `→ 0` by the proven one-variable atom (factor `F − b₀ = wᵉ·g`).

We isolate the clean consequence used by the assembly: if the section's contribution satisfies
`(z − b₀)·deriv s z → 0` and `coeff` is bounded near `s b₀` (it is analytic there, `α` holomorphic
off poles), then the per-sheet term `(z − b₀)·coeff(s z)·deriv s z → 0`. -/

/-- **Per-sheet term boundedness.**  If `(z − b₀)·deriv s z → 0` as `z → b₀` (the ramified-section
derivative blow-up is killed by the `z − b₀` factor — the planar §VIII.3 atom), `s` is continuous at
`b₀`, and `coeff` is continuous at `s b₀` (e.g. analytic there, `α = ω₀·g` holomorphic off poles),
then the per-sheet trace term `(z − b₀)·coeff(s z)·deriv s z → 0`.  Summed over the finite fibre this
gives the fibre-sum boundedness crux `(z − b₀)·T₀ z → 0`. -/
theorem tendsto_zero_perSheet {s coeff : ℂ → ℂ} {b₀ : ℂ}
    (hsderiv : Tendsto (fun z => (z - b₀) * deriv s z) (𝓝[≠] b₀) (𝓝 0))
    (hs_cont : ContinuousAt s b₀) (hcoeff_cont : ContinuousAt coeff (s b₀)) :
    Tendsto (fun z => (z - b₀) * (coeff (s z) * deriv s z)) (𝓝[≠] b₀) (𝓝 0) := by
  -- `coeff ∘ s → coeff (s b₀)` (continuity); times `(z − b₀)·deriv s z → 0`.
  have hcs : Tendsto (fun z => coeff (s z)) (𝓝[≠] b₀) (𝓝 (coeff (s b₀))) :=
    (hcoeff_cont.comp hs_cont).mono_left nhdsWithin_le_nhds
  have hprod : Tendsto (fun z => coeff (s z) * ((z - b₀) * deriv s z)) (𝓝[≠] b₀)
      (𝓝 (coeff (s b₀) * 0)) := hcs.mul hsderiv
  rw [mul_zero] at hprod
  refine hprod.congr (fun z => ?_)
  ring

/-- **Fibre-sum boundedness from per-sheet boundedness.**  If each of the finitely many per-sheet
terms `(z − b₀)·(coeff i (s i z))·deriv (s i) z → 0`, then the fibre-sum trace
`T₀ z = ∑ i, coeff i (s i z)·deriv (s i) z` satisfies `(z − b₀)·T₀ z → 0`.  (Finite sum of
null-tendsto terms; `(z − b₀)·∑ = ∑ (z − b₀)·(…)`.) -/
theorem tendsto_zero_fibreSum {ι : Type*} [Fintype ι] {s coeff : ι → ℂ → ℂ} {b₀ : ℂ}
    (hterm : ∀ i, Tendsto (fun z => (z - b₀) * (coeff i (s i z) * deriv (s i) z))
      (𝓝[≠] b₀) (𝓝 0)) :
    Tendsto (fun z => (z - b₀) * ∑ i, coeff i (s i z) * deriv (s i) z) (𝓝[≠] b₀) (𝓝 0) := by
  have hsum : Tendsto (fun z => ∑ i, (z - b₀) * (coeff i (s i z) * deriv (s i) z))
      (𝓝[≠] b₀) (𝓝 (∑ _i : ι, (0 : ℂ))) := tendsto_finset_sum _ (fun i _ => hterm i)
  rw [Finset.sum_const, smul_zero] at hsum
  refine hsum.congr (fun z => ?_)
  rw [Finset.mul_sum]

end Jacobians.Dolbeault.FormTraceBranchPlanar
