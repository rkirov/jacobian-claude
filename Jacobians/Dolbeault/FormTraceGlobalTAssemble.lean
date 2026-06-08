/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceGlobalT
import Jacobians.Dolbeault.FormTraceGlobalAssemble

/-!
# Assembling `GlobalTrace` from the global trace function `T` (Gate A, §VIII.3 step 1 — assembly)

`Jacobians.Dolbeault.FormTraceGlobalAssemble` proved Gate A (`∑ₐ Resₐ(α) = 0`) from a
`GlobalTrace ω₀ g f poles hac`.  `Jacobians.Dolbeault.FormTraceGlobalT` built the analytic
infrastructure: the principal-part → `LaurentForm` packaging and the discharge of the
holomorphic-remainder fields `hentire` / `hrecip`.  This file **assembles** the two: a single
constructor `globalTrace_of_data` that builds a `GlobalTrace` from

* the global trace function `T : ℂ → ℂ` and a rational `LaurentForm L` representing its principal
  parts (with the centre bookkeeping `hcenters`, the `∞`-fibre enumeration `Dinf`/`hxs_*`);
* the **glue** fields `hglue_fin` / `hglue_inf` — `T` germ-agrees with the local fibre traces (the
  branched-cover sheet-gluing, the substantial §VIII.3 analytic content);
* the **analytic** facts the remainder discharge needs: `T` is analytic off the finite centres,
  `T − L.R` is germ-analytic at every centre (the pole removed by `L`), `T − L.R` is **continuous at
  every centre** (junk-free), and the **genus-`0` `∞`-vanishing** — the analytic continuation of
  `recipCoeff (T − L.R)` vanishes at `0`.

`hentire` is discharged by `analyticOnNhd_remainder_of_junkFree'`, `hrecip` by
`continuousAt_recipCoeff_of_vanishing`.  Composing with `residueSum_eq_zero_of_globalTrace` makes
Gate A `∑Res = 0` follow from these honest inputs.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `globalTrace_of_data` — a `GlobalTrace` from `T`, `L`, the glue, and the remainder-analytic facts;
* `residueSum_eq_zero_of_data` — Gate A `∑Res = 0` from those inputs.

## The minimal remaining obligation

Gate A is now *unconditional modulo* the data `globalTrace_of_data` consumes for a suitable adapted
cover.  The mechanical principal-part / entire / reciprocal-chart bookkeeping is fully discharged; the
**irreducible §VIII.3 content** is exactly:

1. **The glue** (`hglue_fin` / `hglue_inf`): the global trace function `T` germ-agrees with the local
   fibre traces — the branched-cover sheet-gluing (monodromy).  For the genuine geometric trace
   `T = Tr_F α` this is the *definition* of the trace over each fibre; the only subtlety is that the
   `GlobalTrace.hglue_fin` field glues to the **pole sub-fibre** trace (`fibreReg hac`), so `T` must
   germ-agree with the pole sub-fibre trace — true for `Tr_F α` precisely when the cover separates the
   poles of `α` from the regular points over each pole-value (a generic-cover condition).
2. **The genus-`0` `∞`-vanishing**: the analytic continuation of `recipCoeff (T − L.R)` vanishes at
   `0` — a holomorphic `1`-form on `ℂℙ¹` has no `dζ`-term at `∞` only if it is `0` (`H⁰(ℂℙ¹,Ω) = 0`).
3. The junk-freeness (`T − L.R` continuous at each centre) — automatic for `T = Tr_F α` (the
   geometric pushforward is continuous after the pole is removed).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; rationality
  on `ℂℙ¹`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTracePrincipalPart

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-- **`GlobalTrace` from the global trace function `T`.**  Assembles a `GlobalTrace ω₀ g f poles hac`
from the global trace `T : ℂ → ℂ`, a rational `LaurentForm L` (its principal parts), the centre/`∞`
bookkeeping, the **glue** fields (`hglue_fin`/`hglue_inf`), and the remainder-analytic facts
(`T` analytic off the centres, `T − L.R` germ-analytic + continuous at each centre, and the genus-`0`
`∞`-vanishing of `recipCoeff (T − L.R)`).  `hentire` is `analyticOnNhd_remainder_of_junkFree'`;
`hrecip` is `continuousAt_recipCoeff_of_vanishing`.  This is the honest packaging of §VIII.3 step 1:
all bookkeeping discharged, only the glue + genus-`0` content remaining as hypotheses. -/
noncomputable def globalTrace_of_data (hac : AdaptedCover ω₀ g f poles)
    (T : ℂ → ℂ) (L : LaurentForm)
    (hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Dinf : InftyFibreData g f)
    (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hglue_fin : ∀ p ∈ (Finset.univ.image L.a),
      T =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff)
    (hglue_inf : recipCoeff T =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hT_off : ∀ z ∉ Finset.univ.image L.a, AnalyticAt ℂ T z)
    (hrem : ∀ p ∈ Finset.univ.image L.a,
      ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧ (T - L.R) =ᶠ[𝓝[≠] p] R)
    (hcont : ∀ p ∈ Finset.univ.image L.a, ContinuousAt (T - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : recipCoeff (T - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    GlobalTrace ω₀ g f poles hac where
  T := T
  L := L
  hcenters := hcenters
  Dinf := Dinf
  hxs_inj := hxs_inj
  hxs_mem := hxs_mem
  hxs_surj := hxs_surj
  hglue_fin := hglue_fin
  hglue_inf := hglue_inf
  hentire := analyticOnNhd_remainder_of_junkFree' hT_off hrem hcont
  hrecip := continuousAt_recipCoeff_of_vanishing hR₀_an hR₀0 hR₀_eq

/-- **Gate A from the global trace data.**  If an adapted cover and the global-trace data
(`globalTrace_of_data`'s inputs) exist, then the 1-form residue theorem `∑ₐ Resₐ(α) = 0` holds
*unconditionally* for `α = ω₀·g`.  Composes `globalTrace_of_data` with the proved
`residueSum_eq_zero_of_globalTrace`. -/
theorem residueSum_eq_zero_of_data (hac : AdaptedCover ω₀ g f poles)
    (T : ℂ → ℂ) (L : LaurentForm)
    (hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Dinf : InftyFibreData g f)
    (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hglue_fin : ∀ p ∈ (Finset.univ.image L.a),
      T =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff)
    (hglue_inf : recipCoeff T =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff)
    (hT_off : ∀ z ∉ Finset.univ.image L.a, AnalyticAt ℂ T z)
    (hrem : ∀ p ∈ Finset.univ.image L.a,
      ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧ (T - L.R) =ᶠ[𝓝[≠] p] R)
    (hcont : ∀ p ∈ Finset.univ.image L.a, ContinuousAt (T - L.R) p)
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : recipCoeff (T - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_globalTrace hac
    (globalTrace_of_data hac T L hcenters Dinf hxs_inj hxs_mem hxs_surj hglue_fin hglue_inf
      hT_off hrem hcont R₀ hR₀_an hR₀0 hR₀_eq)

/-! ### Non-vacuity of the constructor (end-to-end soundness)

The constructor `globalTrace_of_data` is *satisfiable*, not a disguised `False`: in the
globally-holomorphic (empty-pole) case it builds a `GlobalTrace` with `T ≡ 0`, the empty `LaurentForm`
(no centres), the empty `∞`-fibre, and the vanishing genus-`0` continuation `R₀ ≡ 0`.  All the deep
inputs (glue, junk-freeness) are vacuous over the empty centre set; the `∞`-glue is `recipCoeff 0 ≡ 0`
matching the empty `∞`-trace; `R₀ 0 = 0` and `recipCoeff (0 − 0) =ᶠ 0` hold trivially.  This mirrors
`globalTrace_holomorphic` and confirms the constructor produces a genuine `∑Res = 0`. -/

/-- **`globalTrace_of_data` non-vacuity.**  In the empty-pole case the constructor builds a
`GlobalTrace` (hence `∑Res = 0`) from `T ≡ 0`, the empty `LaurentForm`, the empty `∞`-fibre, and
`R₀ ≡ 0`: every deep input is vacuous (no centres) or trivial (the empty `∞`-trace, `R₀ 0 = 0`).
Confirms the constructor is honest (satisfiable). -/
theorem residueSum_eq_zero_of_data_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 := by
  classical
  refine residueSum_eq_zero_of_data (adaptedCover_empty ω₀ g f hdiv)
    (fun _ => 0) Jacobians.ResidueTheoremX.emptyLaurentForm
    (by rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a]; simp)
    (emptyInftyFibreData g f)
    (fun i => i.elim) (fun i => i.elim) (fun a ha _ => absurd ha (Finset.notMem_empty a))
    ?_ ?_ ?_ ?_ ?_ (fun _ => 0) analyticAt_const rfl ?_
  · -- hglue_fin: vacuous (no centres).
    intro p hp
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a] at hp
    exact absurd hp (Finset.notMem_empty p)
  · -- hglue_inf: `recipCoeff 0 =ᶠ 0` (empty `∞`-trace).
    rw [inftyFibreTrace_emptyData_traceCoeff ω₀ f]
    filter_upwards with ζ; simp [recipCoeff]
  · -- hT_off: `T = 0` analytic everywhere.
    intro z _; exact analyticAt_const
  · -- hrem: vacuous (no centres).
    intro p hp
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a] at hp
    exact absurd hp (Finset.notMem_empty p)
  · -- hcont: vacuous (no centres).
    intro p hp
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a] at hp
    exact absurd hp (Finset.notMem_empty p)
  · -- hR₀_eq: `recipCoeff (0 − emptyLaurentForm.R) =ᶠ 0`.
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_R]
    filter_upwards with ζ
    show recipCoeff ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) ζ = (0 : ℂ)
    simp [recipCoeff]

end Jacobians.Dolbeault.FormTraceGlobal
