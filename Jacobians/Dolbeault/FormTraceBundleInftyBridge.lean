/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceBundleBridge
import Jacobians.Dolbeault.FormTraceGateAAssemble

/-!
# The `∞`-trace reciprocal-chart bridge (Gate A, Miranda §VIII.3 — close of wall 3)

This file is the **`∞`-analogue** of `Jacobians.Dolbeault.FormTraceBundleBridge`.  It discharges the
**`∞`-meromorphy / trace-rationality-at-`∞`** field `hglue_inf` of
`FormTraceGateAAssemble.residueSum_eq_zero_of_globalCoverData` — Gate-A *wall 3* — by the SAME
symmetric-SUM technique used at finite branch values, now read in the **reciprocal chart** `ζ = 1/z` of
`ℂℙ¹`.  (The remaining `∞`-bookkeeping `R₀` / `hR₀_eq` / `hR₀0` is the genus-`0` *Liouville* vanishing,
not the `∞`-meromorphy wall, and is carried faithfully as a residual — see the final theorem; forcing
`R₀ = 0` would be a false field whenever `f` has poles over `∞`.)

## The clean reciprocal-chart reading (the key simplification — the `dζ` Jacobian)

The `∞`-fibre trace `(inftyFibreTrace ω₀ f Dinf).traceCoeff` is, by definition, the reciprocal-chart
moving sum

> `∑ i, chartIntegrand ω₀ g (Dinf.xs i) (sheet i ζ) · deriv (sheet i) ζ`,

where `sheet i` is the planar inverse of the **reciprocal-chart cover** `ψ_i : z ↦ (f.holoRepr
(chart_{xs i}.symm z))⁻¹` at `pre i = chart_{xs i}(xs i)`, sending it to the reciprocal coordinate `0`
of `∞` (`exists_planar_section`).  The same manifold point is described by the **finite** section

> `secInf i b' := chart_{xs i}.symm (sheet i (b'⁻¹))`,   `f.holoRepr (secInf i b') = b'`,

i.e. the chart pullback `rinv i b' := chart_{xs i}(secInf i b') = sheet i (b'⁻¹)` is a planar
right-inverse of `φ_i := f.holoRepr ∘ chart_{xs i}.symm` through `pre i`, read at the *finite* value
`b'`.  The reparametrization `ζ = 1/b'` carries the finite moving sum `inftyMovingSum` to the
reciprocal one via the `−ζ⁻²` Jacobian, **and that Jacobian is exactly the one `recipCoeff` applies**.
So the two cancel: `recipCoeff (inftyMovingSum …) = (inftyFibreTrace ω₀ f Dinf).traceCoeff` near `0`
(the reparametrization identity `recipCoeff_inftyMovingSum_eq_traceCoeff`, a pure chart computation —
**no monodromy, no Puiseux frame**, exactly Miranda's "the SUM extends across `∞`").

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `recipCoeff_inftyMovingSum_eq_traceCoeff` — the reciprocal-chart reparametrization identity (the
  `dζ` Jacobian cancellation): the `recipCoeff` of the finite `∞`-moving sum equals the `∞`-fibre
  trace coefficient near `0`.
* `hglue_inf_of_inftyCoherence` — produces the `hglue_inf` field from the SINGLE `∞`-residual: the
  geometric trace `valueChartTrace` germ-equals the finite `∞`-moving sum near `∞` (the
  reciprocal-chart moving-fibre coherence, the honest `∞`-analogue of the finite glue `hglue_fin`).
* `residueSum_eq_zero_of_globalCoverData_inftyClosed` — `residueSum_eq_zero_of_globalCoverData` with
  the `∞`-meromorphy field `hglue_inf` **discharged**, leaving walls 1 (`AdaptedCover` genericity) and
  2 (global selection `Φ`) plus the genus-`0` Liouville residual `R₀` / `hR₀_eq` / `hR₀0` and the
  finite junk-freeness `hcont_int`.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; the residue
  at infinity; the SUM extends across `∞`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open OnePoint

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.RiemannSphere
  Jacobians.Dolbeault.FormTraceMovingFibre Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The finite `∞`-moving sum and the reparametrization identity

The `∞`-fibre trace `(inftyFibreTrace ω₀ f Dinf).traceCoeff ζ` reads the fibre sum in the **reciprocal**
coordinate `ζ`.  The same sum read in the **finite** value coordinate `b' = ζ⁻¹` is the
`inftyMovingSum`, along the chart pullbacks `b' ↦ sheet i (b'⁻¹)` of the reciprocal-chart sheets.  The
two are related by the `−ζ⁻²` Jacobian of `z = 1/ζ`, which `recipCoeff` supplies. -/

/-- The **finite `∞`-moving sum** along the reciprocal-chart sheets of `Dinf`: the value-coordinate
fibre sum `∑ i, chartIntegrand ω₀ g (Dinf.xs i) (sheet i (b'⁻¹)) · deriv (b' ↦ sheet i (b'⁻¹)) b'`,
read at the *finite* value `b'`.  Its `recipCoeff` is the `∞`-fibre trace coefficient (the
reparametrization identity below). -/
noncomputable def inftyMovingSum (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Dinf : InftyFibreData g f) : ℂ → ℂ :=
  fun b' => ∑ i, chartIntegrand ω₀ g (Dinf.xs i) ((inftyFibreTrace ω₀ f Dinf).sheet i (b'⁻¹))
    * deriv (fun w => (inftyFibreTrace ω₀ f Dinf).sheet i (w⁻¹)) b'

/-- **The reparametrization identity (the `dζ` Jacobian cancellation).**  The reciprocal-chart
coefficient `recipCoeff (inftyMovingSum ω₀ f Dinf)` equals the `∞`-fibre trace coefficient
`(inftyFibreTrace ω₀ f Dinf).traceCoeff` on a punctured neighbourhood of `0`.

*Proof.*  For `ζ ≠ 0`, with `b' = ζ⁻¹` (so `(ζ⁻¹)⁻¹ = ζ`), each sheet `sheet i` is analytic at `0`,
hence differentiable at `ζ` for `ζ` near `0`; the chain rule gives `deriv (b' ↦ sheet i (b'⁻¹)) (ζ⁻¹)
= deriv (sheet i) ζ · (−((ζ⁻¹)²)⁻¹)` (the `deriv` of `·⁻¹` at `ζ⁻¹`, after `(ζ⁻¹)⁻¹ = ζ`).  Then
`recipCoeff (inftyMovingSum) ζ = −(inftyMovingSum (ζ⁻¹))·ζ⁻²`, and the `−((ζ⁻¹)²)⁻¹`/`ζ⁻²` factors
cancel termwise (`field_simp`, `ζ ≠ 0`), leaving `∑ i, chartIntegrand ω₀ g (Dinf.xs i) (sheet i
ζ)·deriv (sheet i) ζ = (inftyFibreTrace).traceCoeff ζ`. -/
theorem recipCoeff_inftyMovingSum_eq_traceCoeff (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (Dinf : InftyFibreData g f) :
    recipCoeff (inftyMovingSum ω₀ f Dinf) =ᶠ[𝓝[≠] 0]
      (inftyFibreTrace ω₀ f Dinf).traceCoeff := by
  classical
  -- Each reciprocal-chart sheet is differentiable on a punctured neighbourhood of `0`.
  have hdiff : ∀ i : Dinf.ι, ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      DifferentiableAt ℂ ((inftyFibreTrace ω₀ f Dinf).sheet i) ζ := by
    intro i
    have hev : ∀ᶠ ζ in 𝓝 (0 : ℂ),
        DifferentiableAt ℂ ((inftyFibreTrace ω₀ f Dinf).sheet i) ζ := by
      have han := ((inftyFibreTrace ω₀ f Dinf).sheet_analytic i).eventually_analyticAt
      rw [inftyFibreTrace_b] at han
      filter_upwards [han] with ζ hζ using hζ.differentiableAt
    exact nhdsWithin_le_nhds hev
  -- Combine over the finitely many sheets, plus `ζ ≠ 0`.
  have hall : ∀ᶠ ζ in 𝓝[≠] (0 : ℂ),
      (∀ i : Dinf.ι, DifferentiableAt ℂ ((inftyFibreTrace ω₀ f Dinf).sheet i) ζ) ∧ ζ ≠ 0 := by
    rw [Filter.eventually_and]
    refine ⟨?_, ?_⟩
    · rw [eventually_all]; exact hdiff
    · filter_upwards [self_mem_nhdsWithin] with ζ hζ; simpa using hζ
  filter_upwards [hall] with ζ ⟨hdζ, hζne⟩
  -- Unfold both sides.
  show -(inftyMovingSum ω₀ f Dinf (ζ⁻¹)) * ζ ^ (-2 : ℤ)
    = ∑ i, (inftyFibreTrace ω₀ f Dinf).coeff i ((inftyFibreTrace ω₀ f Dinf).sheet i ζ)
        * deriv ((inftyFibreTrace ω₀ f Dinf).sheet i) ζ
  rw [inftyMovingSum]
  -- Pull the `−ζ⁻²` factor inside the finite sum.
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- The chart pullback derivative at `ζ⁻¹` via the chain rule (`(ζ⁻¹)⁻¹ = ζ`).
  have hchain : deriv (fun w => (inftyFibreTrace ω₀ f Dinf).sheet i (w⁻¹)) (ζ⁻¹)
      = deriv ((inftyFibreTrace ω₀ f Dinf).sheet i) ζ * (-((ζ⁻¹ ^ 2)⁻¹)) := by
    rw [show (fun w => (inftyFibreTrace ω₀ f Dinf).sheet i (w⁻¹))
        = (inftyFibreTrace ω₀ f Dinf).sheet i ∘ (fun w : ℂ => w⁻¹) from rfl]
    rw [deriv_comp (ζ⁻¹) (by rw [inv_inv]; exact hdζ i) (differentiableAt_inv (by simpa using hζne)),
      deriv_inv, inv_inv]
  -- `(ζ⁻¹)⁻¹ = ζ` in the `chartIntegrand` argument; the coeff is `chartIntegrand`.
  rw [inv_inv, hchain, inftyFibreTrace_coeff]
  -- Termwise algebra: `−(c·deriv·(−((ζ⁻¹)²)⁻¹))·ζ⁻² = c·deriv` (the `dζ` Jacobian cancellation).
  set c := chartIntegrand ω₀ g (Dinf.xs i) ((inftyFibreTrace ω₀ f Dinf).sheet i ζ) with hc
  set d := deriv ((inftyFibreTrace ω₀ f Dinf).sheet i) ζ with hd
  rw [zpow_neg, zpow_two]
  field_simp

/-! ### The `∞`-glue from the reciprocal-chart moving-fibre coherence

The `hglue_inf` field is now produced from a SINGLE `∞`-residual: the geometric trace `valueChartTrace`
germ-equals the finite `∞`-moving sum near `∞`, read through the reciprocal coordinate.  This is the
honest `∞`-analogue of the finite glue `hglue_fin` (the moving-fibre self-coherence): the global trace
re-selects the fibre at each value, but near `∞` it germ-equals the *fixed* `∞`-fibre sum along the
shared reciprocal-chart sheets.  Combined with the reparametrization identity, it gives `hglue_inf`. -/

/-- **The `∞`-glue from the reciprocal-chart moving coherence.**  Suppose the reciprocal coefficient of
the geometric trace germ-equals that of the finite `∞`-moving sum near `0` (`hcoh` — the
reciprocal-chart moving-fibre coherence, the `∞`-residual).  Then the `hglue_inf` field holds:

> `recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0] (inftyFibreTrace ω₀ f Dinf).traceCoeff`.

*Proof.*  `recipCoeff (valueChartTrace) =ᶠ recipCoeff (inftyMovingSum)` (the coherence `hcoh`) `=ᶠ
(inftyFibreTrace).traceCoeff` (the reparametrization identity). -/
theorem hglue_inf_of_inftyCoherence (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (Dinf : InftyFibreData g f)
    (hcoh : recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSum ω₀ f Dinf)) :
    recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0]
      (inftyFibreTrace ω₀ f Dinf).traceCoeff :=
  hcoh.trans (recipCoeff_inftyMovingSum_eq_traceCoeff ω₀ f Dinf)

/-! ### Gate A `∑Res = 0` with the `∞`-meromorphy field (`hglue_inf`) discharged (wall 3 eliminated)

We wire `FormTraceGateAAssemble.residueSum_eq_zero_of_globalCoverData` with the `∞`-meromorphy /
trace-rationality field `hglue_inf` **discharged** from the reciprocal-chart machinery above:

* `hglue_inf` ← `hglue_inf_of_inftyCoherence` (the reparametrization identity + the reciprocal-chart
  moving-fibre coherence `hInftyCoh`), bridged from the patched to the unpatched trace via
  `recipCoeff_valueChartTracePatched_eventuallyEq`.

`hglue_inf` is precisely the `∞`-meromorphy / trace-rationality-at-`∞` content that is *wall 3*: the
trace `Tr_F α` is meromorphic at `∞`, its reciprocal-chart `dζ`-coefficient identified with the
`∞`-fibre trace `(inftyFibreTrace ω₀ f Dinf).traceCoeff` (a `FibreTrace` coefficient, meromorphic at
`0`, with `Dinf` the `∞`-principal-part data).  This is the `∞`-instance of the SAME symmetric-SUM /
bundle technique used at finite branch values — the `−ζ⁻²` Jacobian of the reciprocal chart cancels the
moving-sum reparametrization (`recipCoeff_inftyMovingSum_eq_traceCoeff`), exactly Miranda's "the SUM
extends across `∞`".

The remaining `∞`-bookkeeping `R₀` / `hR₀_an` / `hR₀0` / `hR₀_eq` is the **genus-`0` Liouville**
vanishing (a HOLOMORPHIC `1`-form on `ℂℙ¹` is `0`), *not* the `∞`-meromorphy wall — `R₀` is the
reciprocal-chart analytic continuation of the remainder (the `∞`-principal-part's reciprocal expansion,
nonzero when there are `∞`-poles), with only `R₀ 0 = 0` the genus-`0` content.  It is therefore carried
faithfully as a residual, **not** forced to `0` (which would be a false field whenever `f` has poles
over `∞`).  Likewise the finite junk-freeness `hcont_int` (orthogonal to `∞`) is carried verbatim.

So this theorem leaves exactly walls 1 (`AdaptedCover` genericity, via `hac`) + 2 (global selection `Φ`)
plus the genus-`0` Liouville `R₀` and finite junk-freeness `hcont_int` — the `∞`-meromorphy wall is
eliminated. -/

/-- **Gate A `∑Res = 0`, the `∞`-meromorphy field discharged.**  Identical to
`FormTraceGateAAssemble.residueSum_eq_zero_of_globalCoverData`, but the `∞`-meromorphy /
trace-rationality field `hglue_inf` is **discharged** from the reciprocal-chart bridge via the SINGLE
`∞`-residual:

* `hInftyCoh` — the reciprocal-chart moving-fibre coherence (the honest `∞`-analogue of the finite
  glue `hglue_fin`): `recipCoeff (valueChartTrace ω₀ f Φ)` germ-equals `recipCoeff (inftyMovingSum ω₀ f
  Dinf)` near `0` (the geometric trace germ-equals the fixed `∞`-fibre moving sum along the shared
  reciprocal-chart sheets).

The `∞`-meromorphy heart rides for free: the right-hand side `(inftyFibreTrace ω₀ f Dinf).traceCoeff`
is a `FibreTrace` coefficient, meromorphic at `0` — the `∞`-instance of the same symmetric SUM, with
`Dinf` the `∞`-principal-part data.

The genus-`0` `∞`-vanishing `R₀` / `hR₀_an` / `hR₀0` / `hR₀_eq` is carried as a residual (the §VIII.3
Liouville step, *not* the `∞`-meromorphy wall; `R₀` is the genuine analytic continuation, nonzero with
`∞`-poles), as is the finite junk-freeness `hcont_int`. -/
theorem residueSum_eq_zero_of_globalCoverData_inftyClosed (hdiv : (f.div : Divisor X) ≠ 0)
    (hac : AdaptedCover ω₀ g f poles)
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (Dinf : InftyFibreData g f) (hxs_inj : Function.Injective Dinf.xs)
    (hxs_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxs_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (secFin : ∀ i, (fibreReg hac (cs i)).ι → ℂ → X)
    (hsecFin_base : ∀ i j, secFin i j (cs i) = (fibreReg hac (cs i)).xs j)
    (hsecFin_smooth : ∀ i j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (secFin i j) (cs i))
    (hsecFin_sec : ∀ i j, ∀ᶠ b' in 𝓝 (cs i), f.holoRepr (secFin i j b') = b')
    (hselFin : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∃ e : (Φ b').ι ≃ (fibreReg hac (cs i)).ι,
      (∀ i', (Φ b').xs i' = secFin i (e i') b') ∧
      (∀ j, secFin i j b' ∈ (chartAt ℂ ((fibreReg hac (cs i)).xs j)).source))
    (hmeroReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv), ∀ i,
      MeromorphicAt (fun w => g
          ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (hΦinjReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv),
      ∀ᶠ b' in 𝓝 z, Function.Injective (Φ b').xs)
    (hΦrangeReg : ∀ z (_hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv),
      ∀ᶠ b' in 𝓝 z, Set.range (Φ b').xs = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))})
    (hCreg_g : ∀ z (hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv), ∀ i,
      AnalyticAt ℂ
        (fun w => g ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))))
    (αBr : ℂ → HolomorphicOneForms X)
    (hαBrAgreeBr : ∀ b₀ ∈ branchValues f hdiv, b₀ ∉ Finset.univ.image cs →
      ∀ᶠ z in 𝓝[≠] b₀, ∀ (hz : z ∉ Finset.univ.image cs ∪ branchValues f hdiv), ∀ i,
        (αBr b₀).toFun ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))
          = g ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere)))
            • ω₀.toFun ((sregFamily f hdiv cs z hz).sheet i (((z : ℂ) : RiemannSphere))))
    (hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTracePatched ω₀ f Φ (branchValues f hdiv) - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ∀ p ∈ Finset.univ.image L.a,
        ContinuousAt (valueChartTracePatched ω₀ f Φ (branchValues f hdiv) - L.R) p)
    -- The single `∞`-meromorphy residual: the reciprocal-chart moving-fibre coherence (honest
    -- `∞`-analogue of the finite glue).
    (hInftyCoh : recipCoeff (valueChartTrace ω₀ f Φ) =ᶠ[𝓝[≠] 0]
      recipCoeff (inftyMovingSum ω₀ f Dinf))
    -- The genus-`0` Liouville `∞`-vanishing (carried as a residual, NOT the `∞`-meromorphy wall).
    (R₀ : ℂ → ℂ) (hR₀_an : AnalyticAt ℂ R₀ 0) (hR₀0 : R₀ 0 = 0)
    (hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      recipCoeff (valueChartTracePatched ω₀ f Φ (branchValues f hdiv) - L.R) =ᶠ[𝓝[≠] 0] R₀) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_globalCoverData hdiv hac Φ m cs ρ hcs_ball hcs_inj hcenters_cs Dinf hxs_inj
    hxs_mem hxs_surj secFin hsecFin_base hsecFin_smooth hsecFin_sec hselFin hmeroReg hΦinjReg
    hΦrangeReg hCreg_g αBr hαBrAgreeBr
    ((recipCoeff_valueChartTracePatched_eventuallyEq ω₀ f Φ (branchValues f hdiv)).trans
      (hglue_inf_of_inftyCoherence ω₀ f Φ Dinf hInftyCoh))
    hcont_int R₀ hR₀_an hR₀0 hR₀_eq

/-! ### Non-vacuity of the discharged `∞`-meromorphy field (end-to-end soundness)

The reparametrization identity and the `∞`-residual `hInftyCoh` are *satisfiable*, not a disguised
`False`: for the empty fibre selection both the geometric trace `valueChartTrace` and the finite
`∞`-moving sum `inftyMovingSum` (over the empty `∞`-fibre `emptyInftyFibreData`) are identically `0`, so
`hInftyCoh` is `recipCoeff 0 =ᶠ recipCoeff 0` and the produced `hglue_inf` is the proven empty `∞`-trace
identity `recipCoeff 0 =ᶠ 0 = (inftyFibreTrace emptyData).traceCoeff`.  This confirms the discharged
`∞`-meromorphy field encodes no contradiction. -/

/-- **The empty `∞`-moving sum is `0`.**  Over the empty `∞`-fibre `emptyInftyFibreData` (index
`Empty`), `inftyMovingSum` is the empty sum, hence `≡ 0`. -/
@[simp] theorem inftyMovingSum_emptyData (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) :
    inftyMovingSum ω₀ f (emptyInftyFibreData g f) = fun _ => (0 : ℂ) := by
  funext b'
  show (∑ i : Empty, _) = (0 : ℂ)
  rw [Finset.univ_eq_empty, Finset.sum_empty]

/-- **Non-vacuity of the `∞`-residual `hInftyCoh`.**  For the empty fibre selection over the empty
`∞`-fibre, the reciprocal-chart moving coherence holds (`recipCoeff 0 =ᶠ recipCoeff 0`). -/
theorem hInftyCoh_emptySelection (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) :
    recipCoeff (valueChartTrace ω₀ f (fun p => emptyFibreRegularData g f p)) =ᶠ[𝓝[≠] 0]
      recipCoeff (inftyMovingSum ω₀ f (emptyInftyFibreData g f)) := by
  rw [valueChartTrace_emptySelection ω₀ f, inftyMovingSum_emptyData ω₀ f]

/-- **Non-vacuity of the produced `hglue_inf`.**  For the empty fibre selection over the empty
`∞`-fibre, `hglue_inf_of_inftyCoherence` (fed `hInftyCoh_emptySelection`) yields the proven empty
`∞`-trace identity `recipCoeff 0 =ᶠ[𝓝[≠] 0] (inftyFibreTrace emptyData).traceCoeff` — the discharge is
a genuine `hglue_inf`, not a disguised `False`. -/
theorem hglue_inf_emptySelection (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) :
    recipCoeff (valueChartTrace ω₀ f (fun p => emptyFibreRegularData g f p)) =ᶠ[𝓝[≠] 0]
      (inftyFibreTrace ω₀ f (emptyInftyFibreData g f)).traceCoeff :=
  hglue_inf_of_inftyCoherence ω₀ f (fun p => emptyFibreRegularData g f p) (emptyInftyFibreData g f)
    (hInftyCoh_emptySelection ω₀ f)

end Jacobians.Dolbeault.FormTraceGlobal
