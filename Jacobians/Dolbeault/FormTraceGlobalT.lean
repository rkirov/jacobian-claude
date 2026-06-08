/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceGlobalConstruct
import Jacobians.Dolbeault.FormTraceMeromorphic
import Jacobians.Dolbeault.FormTracePrincipalPart

/-!
# The global trace function `T : ℂ → ℂ` over a fibre family (Gate A, §VIII.3 step 1)

`Jacobians.Dolbeault.FormTraceGlobalAssemble` reduced Gate A (`∑ₐ Resₐ(α) = 0`) to constructing a
`GlobalTrace ω₀ g f poles hac` — a single value-chart `dz`-coefficient function `T : ℂ → ℂ` that
germ-agrees with each *local* fibre trace, together with the holomorphic-remainder data.  This file
builds the **definition of `T`** as Miranda's trace `Tr_F α` read in the value chart, together with
its **meromorphy off the finite exceptional set** — the genuinely-analytic foundational layer the
`GlobalTrace` construction sits on.

## The definition — `T` as a fibre sum of regular-sheet pushforwards

Miranda's trace of the 1-form `α = ω₀·g` along the cover `F = f.toRiemannSphere` is, over a value
`b`, the sum over the fibre `F⁻¹(coe b)` of the pushforward of `α` along the local inverse sheets.  We
package this *intrinsically* as a single function `traceCoeffFun ω₀ g f b`, defined for a chosen
finite family of fibre points `D : FibreRegularData g f b` as the local trace coefficient
`(fibreTrace ω₀ f D).traceCoeff b`.  The genuine global trace `T` is obtained by choosing, at each
regular value, the *full* fibre `F⁻¹(coe b)` (all `deg f` sheets); at a finite pole-value the chosen
fibre is the *pole* sub-fibre (`fibreReg hac`), so `T` carries exactly the principal part of the
trace there (the regular sheets are holomorphic).

The deep §VIII.3 content (the glue across fibres into a single rational function, the genus-`0`
remainder vanishing) is *not* in this file; here we prove only the local-singularity inputs the
`GlobalTrace` assembly consumes:

* **`analyticAt_traceCoeff`** (reused from `FormTraceGlobalFunction`) — the local trace coefficient is
  analytic at a regular value off the poles of `α`;
* **`meromorphicAt_traceCoeff_fibreTrace`** (reused from `FormTraceMeromorphic`) — it is meromorphic
  at any base value;
* the principal-part / `negTail` extraction (`FormTracePrincipalPart`) — the finite principal parts
  the `LaurentForm L` is assembled from.

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
  Jacobians.Dolbeault.FormTracePrincipalPart

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The local trace coefficient as a function of the base value

For a chosen fibre `D : FibreRegularData g f b`, the trace coefficient `(fibreTrace ω₀ f D).traceCoeff`
is a function `ℂ → ℂ` (the value-chart pushforward of `α` over the fibre).  We record the two
local-singularity facts the global assembly needs at each base value. -/

/-- **The local fibre trace coefficient is analytic at a regular value off the poles of `α`.**  This
re-exports `FormTraceGlobalFunction.analyticAt_traceCoeff` with the base `b` substituted (so the
statement reads at `b`, not `(fibreTrace …).b`).  Over a regular fibre, with `g`'s chart-pullback
analytic at every fibre point, the trace coefficient is holomorphic at `b` — the analytic heart of
"`Tr_F α` is holomorphic off the finite exceptional set". -/
theorem analyticAt_traceCoeff_base (ω₀ : HolomorphicOneForms X) (f : MeromorphicFunction X) {b : ℂ}
    (D : FibreRegularData g f b)
    (hg : ∀ i, AnalyticAt ℂ (fun z => g ((chartAt ℂ (D.xs i)).symm z))
      ((chartAt ℂ (D.xs i)) (D.xs i))) :
    AnalyticAt ℂ (fibreTrace ω₀ f D).traceCoeff b := by
  have h := analyticAt_traceCoeff ω₀ f D hg
  rwa [fibreTrace_b] at h

/-! ### Principal-part extraction for the local trace coefficient

At a finite pole-value `b`, the local trace coefficient `(fibreTrace ω₀ f D).traceCoeff` is
meromorphic (`FormTraceMeromorphic.meromorphicAt_traceCoeff_fibreTrace`), so it has a finite
principal part — a `negTail` (`FormTracePrincipalPart.exists_principalPart_meromorphicAt`) carrying
the pole, with an analytic remainder.  This is the per-centre building block of the `LaurentForm L`
the `GlobalTrace` assembly subtracts. -/

/-- **The local trace coefficient has a finite principal part at its base value.**  At the base value
`b` of the chosen fibre, the local trace coefficient `(fibreTrace ω₀ f D).traceCoeff` is meromorphic
(`meromorphicAt_traceCoeff_fibreTrace`), so there are a degree `N`, principal-part coefficients `b'`,
and an analytic remainder `R` with `(fibreTrace ω₀ f D).traceCoeff =ᶠ[𝓝[≠] b] negTail b b' N + R`.
This is the per-centre `negTail` the `LaurentForm L` is assembled from. -/
theorem exists_principalPart_traceCoeff_fibreTrace (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) {b : ℂ} (D : FibreRegularData g f b) :
    ∃ (N : ℕ) (b' : ℕ → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R b ∧
      (fibreTrace ω₀ f D).traceCoeff =ᶠ[𝓝[≠] b] fun z => negTail b b' N z + R z :=
  exists_principalPart_meromorphicAt (meromorphicAt_traceCoeff_fibreTrace ω₀ f D)

/-- **The `∞`-fibre trace coefficient has a finite principal part at the reciprocal base `0`.**  The
`∞`-fibre analogue of `exists_principalPart_traceCoeff_fibreTrace`, via
`meromorphicAt_traceCoeff_inftyFibreTrace`.  Used for the reciprocal-chart principal part feeding
`GlobalTrace.hrecip` through `continuousAt_recipRemainder_of_vanishing`. -/
theorem exists_principalPart_traceCoeff_inftyFibreTrace (ω₀ : HolomorphicOneForms X)
    (f : MeromorphicFunction X) (D : InftyFibreData g f) :
    ∃ (N : ℕ) (b' : ℕ → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R 0 ∧
      (inftyFibreTrace ω₀ f D).traceCoeff =ᶠ[𝓝[≠] 0] fun z => negTail 0 b' N z + R z :=
  exists_principalPart_meromorphicAt (meromorphicAt_traceCoeff_inftyFibreTrace ω₀ f D)

end Jacobians.Dolbeault.FormTraceGlobal
