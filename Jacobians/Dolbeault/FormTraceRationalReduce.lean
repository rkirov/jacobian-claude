/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceGlobalConstruct
import Jacobians.Dolbeault.FormTraceGlobalFunction

/-!
# Reducing `TraceRationalityWitness` to the trace-representation agreement (Gate A, §VIII.3 step 4)

`Jacobians.Dolbeault.FormTraceGlobalConstruct` isolated the deep §VIII.3 core of Gate A into the
`TraceRationalityWitness` — a rational `LaurentForm L` representing `Tr_F α` on `ℂℙ¹`, with the three
fields `hcenters`/`hL32`/`infty_eq`.  This file reduces the two *analytic* fields `hL32` and
`infty_eq` to a single honest geometric input: **`L.R` agrees with the local trace coefficient near
each value**.

## The reduction (Miranda Lemma 3.2 read through the agreement)

The fibre trace `fibreTrace ω₀ f (fibreReg hac p)` over a finite center `p` has base `b = p`, and
Miranda's Lemma 3.2 (`resAt_traceCoeff_fibreTrace`, *proved*, unconditional via the residue
change-of-variables `MeromorphicTrace.residueChangeOfVariables`) gives

> `resAt (Tr_F α over the fibre) p = ∑ᵢ Res_{xᵢ}(α)`   (the fibre residue sum).

So if the rational `L.R` **agrees with the local trace coefficient on a punctured neighbourhood of
`p`** (`L.R =ᶠ[𝓝[≠] p] (fibreTrace …).traceCoeff` — the honest "`L` represents `Tr_F α`" condition),
then `resAt L.R p = resAt (Tr_F α) p = ∑ᵢ Res_{xᵢ}(α)`, which is exactly the `hL32` field
(`FibreTrace.resAt_traceCoeff'` turns its `∑ᵢ resAt (coeff i) (pre i)` LHS into `resAt traceCoeff p`).

This file proves:

* `hL32_of_agree` — the `hL32` field from the per-center agreement;
* `traceRationalityWitness_of_agree` — the full `TraceRationalityWitness` from a `LaurentForm` with
  `hcenters` (the discrete center-bookkeeping, an explicit choice of representation), the per-center
  agreement (`hL32`), and the `∞`-fibre residue identity (`infty_eq`, the reciprocal-chart Lemma 3.2,
  the genuinely-honest large-circle contour content carried as a field).

The reduction makes the remaining obligation precise: **construct the global trace coefficient as a
rational `LaurentForm L` agreeing with the local `Tr_F α` near each value** (finite centres) and
matching the `∞`-fibre residue at infinity.  The per-center agreement is exactly "`L.R` is the
partial-fraction expansion of the meromorphic `Tr_F α`" (Miranda's rationality on the compact `ℂℙ¹`).

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
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormResidueTheorem

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### Lemma 3.2 at a finite centre, read through the agreement

The fibre trace over the finite center `p` is `fibreTrace ω₀ f (fibreReg hac p)`, with base `b = p`.
By `FibreTrace.resAt_traceCoeff'` its `∑ᵢ resAt (coeff i) (pre i)` is `resAt (Tr_F α) p`, and by
`resAt_traceCoeff_fibreTrace` that equals the fibre residue sum `∑ᵢ formFnResidue ω₀ g (xs i)`.  So
the `hL32` field is exactly `resAt L.R p = resAt (Tr_F α) p`, which holds whenever `L.R` agrees with
the trace coefficient off `p`. -/

/-- **Lemma 3.2 at a finite centre, from the trace agreement.**  If the rational coefficient `L.R`
agrees with the local trace coefficient `(fibreTrace ω₀ f (fibreReg hac p)).traceCoeff` on a
punctured neighbourhood of `p`, then the `hL32` field holds at `p`:

> `∑ᵢ resAt ((fibreTrace ω₀ f (fibreReg hac p)).coeff i) ((fibreTrace ω₀ f (fibreReg hac p)).pre i)
>     = resAt L.R p`.

*Proof.*  By `FibreTrace.resAt_traceCoeff'` the LHS is `resAt (Tr_F α) (fibreTrace …).b = resAt (Tr_F
α) p`; by `resAt_congr` and the agreement that is `resAt L.R p`. -/
theorem hL32_of_agree (hac : AdaptedCover ω₀ g f poles) (L : LaurentForm) (p : ℂ)
    (hagree : L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff) :
    (∑ i, resAt ((fibreTrace ω₀ f (fibreReg hac p)).coeff i)
        ((fibreTrace ω₀ f (fibreReg hac p)).pre i)) = resAt L.R p := by
  rw [← (fibreTrace ω₀ f (fibreReg hac p)).resAt_traceCoeff']
  -- `(fibreTrace …).b = p`, and `L.R =ᶠ traceCoeff` off `p`, so the residues agree.
  rw [fibreTrace_b]
  exact (resAt_congr hagree).symm

/-- **The fibre residue sum at a finite centre, from the trace agreement.**  Combining
`hL32_of_agree` with `resAt_traceCoeff_fibreTrace`: when `L.R` agrees with the local trace coefficient
off `p`, its residue there is the fibre residue sum of `α = ω₀·g`:

> `resAt L.R p = ∑ᵢ formFnResidue ω₀ g ((fibreReg hac p).xs i)`. -/
theorem resAt_eq_fibreResidueSum_of_agree (hac : AdaptedCover ω₀ g f poles) (L : LaurentForm)
    (p : ℂ) (hagree : L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff) :
    resAt L.R p = ∑ i, formFnResidue ω₀ g ((fibreReg hac p).xs i) := by
  -- `resAt L.R p = resAt (Tr_F α) p` (agreement), then Lemma 3.2 over the fibre (base `p`, `rfl`).
  rw [resAt_congr hagree]
  exact resAt_traceCoeff_fibreTrace ω₀ f (fibreReg hac p)

/-! ### The full `TraceRationalityWitness` from the agreement + the `∞`-residue identity

With `hL32` reduced to the per-center agreement (`hL32_of_agree`), the only remaining genuinely-deep
content is `hcenters` (a discrete choice of which centres `L` carries — the finite pole-values) and
`infty_eq` (Lemma 3.2 at `∞`, the honest large-circle contour content).  We package the assembly:
given `L`, `hcenters`, the per-center agreement, and `infty_eq`, a `TraceRationalityWitness` exists. -/

/-- **`TraceRationalityWitness` from the trace agreement.**  Given:

* a `LaurentForm L`,
* `hcenters` — the `L`-centres, mapped to the sphere, are exactly the finite pole-values (the discrete
  choice of representation),
* `hagree` — for each centre `p` of `L`, `L.R` agrees with the local trace coefficient off `p` (the
  honest "`L.R` is the partial-fraction expansion of the meromorphic `Tr_F α`" condition), and
* `infty_eq` — Lemma 3.2 at `∞` (the `∞`-residue of `L.R` is the `∞`-fibre residue sum),

a `TraceRationalityWitness ω₀ g f poles hac` exists.  *Proof:* `hcenters`/`infty_eq` are passed
through; `hL32` is `hL32_of_agree` applied at each centre. -/
def traceRationalityWitness_of_agree (hac : AdaptedCover ω₀ g f poles) (L : LaurentForm)
    (hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hagree : ∀ p ∈ (Finset.univ.image L.a),
      L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff)
    (hinfty : resAtInfty L.R L.ρ
      = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a) :
    TraceRationalityWitness ω₀ g f poles hac where
  L := L
  hcenters := hcenters
  hL32 := fun p hp => hL32_of_agree hac L p (hagree p hp)
  infty_eq := hinfty

/-- **Gate A from the trace agreement.**  If an adapted cover and a `LaurentForm` representing
`Tr_F α` (with the centre bookkeeping, the per-centre agreement, and the `∞`-residue identity) exist,
then the 1-form residue theorem `∑ₐ Resₐ(α) = 0` holds *unconditionally* for `α = ω₀·g`.  This
composes `traceRationalityWitness_of_agree` with the proved
`Jacobians.Dolbeault.FormTraceGlobal.residueSum_eq_zero_of_adapted`. -/
theorem residueSum_eq_zero_of_agree (hac : AdaptedCover ω₀ g f poles) (L : LaurentForm)
    (hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hagree : ∀ p ∈ (Finset.univ.image L.a),
      L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (fibreReg hac p)).traceCoeff)
    (hinfty : resAtInfty L.R L.ρ
      = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_adapted hac (traceRationalityWitness_of_agree hac L hcenters hagree hinfty)

end Jacobians.Dolbeault.FormTraceGlobal
