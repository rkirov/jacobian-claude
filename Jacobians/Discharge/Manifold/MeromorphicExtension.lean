/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.Discharge.Manifold.MeromorphicAt
import Jacobians.Discharge.Manifold.RiemannSphere
import Jacobians.Discharge.Divisor.PrincipalDivisor
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Meromorphic.Order

set_option autoImplicit true


/-! # Pole-extension of a meromorphic function to the Riemann sphere

This file builds the **pole extension**

`f̃ : X → RiemannSphere`

of a non-vanishing-germ meromorphic function `f : X → ℂ` on a compact
complex 1-manifold `X`. Concretely:

* `f̃ x = (some (f x) : OnePoint ℂ)` if `f` is regular at `x` (order `≥ 0`);
* `f̃ x = ∞` if `x` is a pole of `f` (order `< 0`).

The branching is controlled by the order in `WithTop ℤ` (so the case split
is between `0 ≤ order` — covering both finite-non-negative orders and the
unreachable `⊤` slot ruled out by `nonvanishing_germ` — and `order < 0`).

## What this file ships

* `MeromorphicNonzero.toRiemannSphere : (f : MeromorphicNonzero X) → X → RiemannSphere`
  — the genuine branched definition.
* `toRiemannSphere_apply_of_nonneg` and `toRiemannSphere_apply_of_neg`
  — point-wise unfolding lemmas matching the two branches.
* `toRiemannSphere_apply_of_orderTop` — convenience: a `⊤`-order point goes
  to `some (f x)` (vacuous in the presence of `nonvanishing_germ`, but
  useful for case splits).
* `toRiemannSphere_eq_some_iff_nonneg`,
  `toRiemannSphere_eq_infty_iff_neg` — the two `iff` characterizations of
  the branches, expressed in terms of the order.

* `toRiemannSphere_contMDiff_statement` —the `Prop`-valued **statement**
  that the pole extension is `ContMDiff ω` from `X` to `RiemannSphere`.
  Marked as a `Prop`-valued `def`, **not an axiom**: callers must explicitly
  thread it as a hypothesis. Discharging it requires:

  1. **At a regular point** `x` with order `≥ 0`: the pole set is locally
     finite (this is the local-finsupp content of
     `Jacobians.Discharge.MMeromorphicOn.divisor`, established in
     `Manifold/MeromorphicDivisor.lean`). On a punctured neighborhood of
     `x`, `f̃` agrees with the continuous map `(some : ℂ → OnePoint ℂ) ∘ f`,
     and `f` itself extends continuously by `MeromorphicAt.analyticAt`
     (continuity at `x` upgrades meromorphy to analyticity). The map is
     then read through the north chart `chartN` on the codomain, and the
     local representative is precisely the analytic representative of `f`.
  2. **At a pole** `x` with order `< 0`: again local finiteness of the
     pole set provides a punctured neighborhood with no other poles. On
     that neighborhood, `f̃ y = some (f y)` and `1 / (f̃ y) = some (1 / f y)`
     when `f y ≠ 0`. The function `1/f` extends analytically with value
     `0` at `x` (mathlib's `meromorphicOrderAt_inv` flips the sign of the
     order, so `1/f` has positive order at the pole, hence is analytic with
     `1/f (x) = 0`). The map `f̃` is then read through the south chart
     `chartS` on the codomain (which sends `(some w) ↦ 1/w` for `w ≠ 0` and
     `∞ ↦ 0`); the local representative is the analytic representative of
     `1/f`.

Both branches require chart-side bookkeeping through `OpenPartialHomeomorph`
and the `ChartedSpace ℂ X` atlas. The deferred material is recorded honestly in
`OPEN.md` (this `Prop`-only statement is the named hook).

This is the **R1** discharge from
`Jacobians.Discharge.Manifold.ResidueTheorem`'s named-gap decomposition.
-/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set OnePoint

namespace Jacobians.Discharge

universe u

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

namespace MeromorphicNonzero

/-- The **pole extension** of a non-vanishing-germ meromorphic function
`f : X → ℂ` to a map `f̃ : X → RiemannSphere`.

* At a regular point `x` (`0 ≤ mmeromorphicOrderAt I f.toFun x` in
  `WithTop ℤ`), `f̃ x = (some (f.toFun x) : OnePoint ℂ)`.
* At a pole `x` (`mmeromorphicOrderAt I f.toFun x < 0`), `f̃ x = ∞`.

The branching is on the actual `WithTop ℤ` order (not its `untop₀`-image),
so the `⊤` case (germ identically zero) is folded into the `0 ≤` branch
where it would map to `some (f.toFun x)` — but this branch is unreachable
under the `nonvanishing_germ` field of `MeromorphicNonzero X`. -/
def toRiemannSphere (f : MeromorphicNonzero X) : X → RiemannSphere :=
  fun x =>
    if 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x then
      (OnePoint.some (f.toFun x) : RiemannSphere)
    else
      ∞

/-! ### Branch-unfolding lemmas

These are the API-friendly point-wise unfoldings of `toRiemannSphere` at
the two branches. They are stated in terms of the underlying order in
`WithTop ℤ`, not its `untop₀`-image, so they compose cleanly with the order
theory in `Manifold/MeromorphicAt.lean` and the divisor packaging in
`Manifold/MeromorphicDivisor.lean`. -/

/-- At a regular point (order `≥ 0`), the pole extension equals the simple
coercion `some (f x)` into `OnePoint ℂ`. -/
@[simp] lemma toRiemannSphere_apply_of_nonneg
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    f.toRiemannSphere x = (OnePoint.some (f.toFun x) : RiemannSphere) := by
  unfold toRiemannSphere
  rw [if_pos hx]

/-- At a pole (order `< 0`), the pole extension equals `∞`. -/
@[simp] lemma toRiemannSphere_apply_of_neg
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0) :
    f.toRiemannSphere x = (∞ : RiemannSphere) := by
  unfold toRiemannSphere
  rw [if_neg (not_le.mpr hx)]

/-- The pole extension of `f` is `some (f x)` iff `x` is a regular point
of `f` (order `≥ 0`). -/
lemma toRiemannSphere_eq_some_iff_nonneg
    (f : MeromorphicNonzero X) (x : X) :
    f.toRiemannSphere x = (OnePoint.some (f.toFun x) : RiemannSphere) ↔
      0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x := by
  constructor
  · intro h
    by_contra hneg
    push_neg at hneg
    rw [toRiemannSphere_apply_of_neg f hneg] at h
    exact (OnePoint.infty_ne_coe (f.toFun x)) h
  · intro h
    exact toRiemannSphere_apply_of_nonneg f h

/-- The pole extension of `f` is `∞` iff `x` is a pole of `f` (order `< 0`).
The `→` direction uses the `nonvanishing_germ` field to rule out the (in
this branch unreachable) `⊤`-order point: by definition of the `if`, the
pole extension is `∞` only when the order is **not** `≥ 0`, i.e. strictly
less than `0` in `WithTop ℤ`; together with `order ≠ ⊤` this is exactly
`order < 0`. -/
lemma toRiemannSphere_eq_infty_iff_neg
    (f : MeromorphicNonzero X) (x : X) :
    f.toRiemannSphere x = (∞ : RiemannSphere) ↔
      mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0 := by
  constructor
  · intro h
    by_contra hnonneg
    push_neg at hnonneg
    rw [toRiemannSphere_apply_of_nonneg f hnonneg] at h
    exact (OnePoint.coe_ne_infty (f.toFun x)) h
  · intro h
    exact toRiemannSphere_apply_of_neg f h

/-- The pole extension never sends a regular point's image to `∞`:
contrapositive form, useful for chart-source membership arguments. -/
lemma toRiemannSphere_ne_infty_of_nonneg
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    f.toRiemannSphere x ≠ (∞ : RiemannSphere) := by
  rw [toRiemannSphere_apply_of_nonneg f hx]
  exact OnePoint.coe_ne_infty _

/-- The pole extension at a pole point is exactly `∞` (not a finite value).
Useful for chartS-source membership arguments. -/
lemma toRiemannSphere_ne_some_of_neg
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < 0) (z : ℂ) :
    f.toRiemannSphere x ≠ (OnePoint.some z : RiemannSphere) := by
  rw [toRiemannSphere_apply_of_neg f hx]
  exact OnePoint.infty_ne_coe _

/-! ### `ContMDiff` of the pole extension — partial content

This section ships the **proven local building blocks** for the smoothness of
`toRiemannSphere`. The full headline `theorem` is recorded conditionally
under an explicit value-vs-germ hypothesis (`HasGermValueAlignment`), and
the unconditional `Prop`-valued statement is preserved as a hook.

#### What this section proves (zero `sorry`)

* `toRiemannSphere_eventuallyEq_some_of_nonpole` — at any non-pole `x`, the
  map `toRiemannSphere` agrees on a full neighborhood of `x` with the simple
  composition `OnePoint.some ∘ f.toFun`. This is the local-finiteness leg
  (uses `MMeromorphicOn.poles_finite`).
* `toRiemannSphere_eventuallyEq_some_punctured_of_pole` — at any pole `x`,
  the same identity holds on a *punctured* neighborhood (the value at `x`
  itself is `∞`).
* `toRiemannSphere_chartN_localForm` — chart-coordinate identity for the
  chart-pulled-back representative through the north chart, on a full
  neighborhood of `(chartAt ℂ x) x` for non-pole `x`.
* `toRiemannSphere_chartS_localForm` — chart-coordinate identity through the
  south chart, on a punctured neighborhood of `(chartAt ℂ x) x` for pole `x`.

#### Why the headline is not unconditional

`MeromorphicNonzero X` constrains the *germ* of `f.toFun` at every point
(via `mmeromorphicOrderAt _ _ ≠ ⊤` and `MMeromorphicOn _ _ Set.univ`),
but does not constrain the pointwise value `f.toFun x` to match the germ's
analytic representative at `x`. Concretely, mathlib's `MeromorphicAt f x`
predicate is invariant under modifying `f` at `x` (a single-point change
does not affect the germ). The Lean structure thus admits
"meromorphic functions" whose pointwise values disagree with the analytic
limit at finitely many regular points — and at such points,
`toRiemannSphere` is genuinely discontinuous (the chart-coordinate
representative reads as `f.toFun x`, but the analytic candidate provided by
`meromorphicOrderAt_eq_int_iff` reads as the germ limit).

The classical statement on a Riemann surface holds because
"meromorphic function" in classical analysis silently includes
value-equals-germ-limit at every point. This is **not** part of the Lean
type, so the headline `theorem` requires the auxiliary hypothesis
`HasGermValueAlignment` (or, equivalently, switching to a quotient by germ
equivalence — a structural change to `MeromorphicNonzero`). We expose the
hypothesis explicitly and ship the conditional discharge.

#### Gating obstruction (named for the OPEN tracker)

The unconditional discharge requires either:
1. A new mathlib lemma `MeromorphicAt.value_eq_analytic_limit_of_continuous`
   plus a continuity hypothesis built into `MeromorphicNonzero`; OR
2. Restructuring `MeromorphicNonzero` to be a quotient by germ-equivalence
   (changes `Divisor/PrincipalDivisor.lean` API).

Neither is in scope for R1 itself. The conditional theorem
`toRiemannSphere_contMDiff_of_germValueAligned` below is the strongest
unconditional statement provable at this Lean pin without those changes,
and the unconditional `toRiemannSphere_contMDiff_statement` is preserved
as a `Prop`-valued statement so callers thread it as a hypothesis.
-/

end MeromorphicNonzero

/-! ### Local-finite-pole consequences and chart-coordinate forms

These are the load-bearing local lemmas underlying the smoothness proof.
They use only the divisor-side local-finiteness (R2) and chart unfolds. -/

namespace MeromorphicNonzero

/-- **Local-finite-pole identity at a non-pole.** On a full neighborhood of
any non-pole `x`, the pole extension agrees with `OnePoint.some ∘ f.toFun`.

Proof: the pole set is finite (`MMeromorphicOn.poles_finite`), hence closed
in the T₂ space `X`. Its complement is open and contains `x`. -/
lemma toRiemannSphere_eventuallyEq_some_of_nonpole
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    f.toRiemannSphere =ᶠ[𝓝 x]
      (fun y => (OnePoint.some (f.toFun y) : RiemannSphere)) := by
  have h_poles_fin :
      {y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < (0 : WithTop ℤ)}.Finite :=
    Jacobians.Discharge.MMeromorphicOn.poles_finite (X := X) (𝓘(ℂ, ℂ))
      f.toFun f.meromorphic f.nonvanishing_germ
  set P : Set X :=
      {y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < (0 : WithTop ℤ)} with hP_def
  have hx_notin : x ∉ P := by
    intro hxP
    simp only [hP_def, Set.mem_setOf_eq] at hxP
    exact absurd hx (not_le.mpr hxP)
  have h_open_compl : IsOpen (Pᶜ) := by
    rw [isOpen_compl_iff]
    exact h_poles_fin.isClosed
  have hx_compl : x ∈ Pᶜ := hx_notin
  refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨Pᶜ, h_open_compl.mem_nhds hx_compl, ?_⟩
  intro y hy
  simp only [Set.mem_compl_iff, hP_def, Set.mem_setOf_eq, not_lt] at hy
  exact toRiemannSphere_apply_of_nonneg f hy

/-- **Local-finite-pole identity at a pole.** On a *punctured* neighborhood
of any pole `x`, the pole extension agrees with `OnePoint.some ∘ f.toFun`.
The value at `x` itself is `∞` (not `some _`); restricting away from `x`
is essential.

Proof: the pole set minus `{x}` is finite (`MMeromorphicOn.poles_finite`
intersected with `{x}ᶜ`), hence closed. Working in `𝓝[≠] x` filters out `x`
itself. -/
lemma toRiemannSphere_eventuallyEq_some_punctured_of_pole
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ)) :
    f.toRiemannSphere =ᶠ[𝓝[≠] x]
      (fun y => (OnePoint.some (f.toFun y) : RiemannSphere)) := by
  have h_poles_fin :
      {y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < (0 : WithTop ℤ)}.Finite :=
    Jacobians.Discharge.MMeromorphicOn.poles_finite (X := X) (𝓘(ℂ, ℂ))
      f.toFun f.meromorphic f.nonvanishing_germ
  set P : Set X :=
      {y : X | mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun y < (0 : WithTop ℤ)} with hP_def
  -- "Other poles" = `P \ {x}` is finite.
  have h_others_fin : (P \ {x}).Finite := h_poles_fin.diff
  have h_others_closed : IsClosed (P \ {x}) := h_others_fin.isClosed
  -- The `𝓝[≠] x`-eventuality: on `(P \ {x})ᶜ ∩ {x}ᶜ`, every point is not a
  -- pole. We use that `(P \ {x})ᶜ ∈ 𝓝 x` (since x ∉ P\{x}) and pass to the
  -- punctured filter.
  have h_open : IsOpen ((P \ {x})ᶜ) := h_others_closed.isOpen_compl
  have hx_in : x ∈ ((P \ {x})ᶜ) := by
    intro hxP; exact hxP.2 rfl
  -- Use `eventually_nhdsWithin_iff` to construct the punctured-nhd EventuallyEq.
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [h_open.mem_nhds hx_in] with y hy_compl hy_ne
  -- `hy_compl : y ∈ (P \ {x})ᶜ`, `hy_ne : y ∈ {x}ᶜ`, i.e. `y ≠ x`.
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy_ne
  by_cases hyP : y ∈ P
  · -- y ∈ P and y ≠ x ⟹ y ∈ P \ {x}, contradicting `hy_compl`.
    exact absurd ⟨hyP, hy_ne⟩ hy_compl
  · -- y ∉ P ⟹ 0 ≤ order ⟹ apply the non-pole branch.
    simp only [hP_def, Set.mem_setOf_eq, not_lt] at hyP
    exact toRiemannSphere_apply_of_nonneg f hyP

end MeromorphicNonzero

/-! ### `chartAt` reduction lemmas for `RiemannSphere`

The `ChartedSpace` instance picks `chartN` for finite points and `chartS`
for `∞`. We expose the two reductions as `simp`-friendly lemmas. -/

@[simp] lemma chartAt_riemannSphere_coe (z : ℂ) :
    (chartAt ℂ ((z : RiemannSphere))) = RiemannSphere.chartN := by
  show RiemannSphere.chartAt' ((z : RiemannSphere)) = RiemannSphere.chartN
  exact RiemannSphere.chartAt'_coe z

@[simp] lemma chartAt_riemannSphere_infty :
    (chartAt ℂ (∞ : RiemannSphere)) = RiemannSphere.chartS := by
  show RiemannSphere.chartAt' (∞ : RiemannSphere) = RiemannSphere.chartS
  exact RiemannSphere.chartAt'_infty

namespace MeromorphicNonzero

/-- **Chart-coordinate local form, non-pole branch (chartN).** On a full
neighborhood of `(chartAt ℂ x) x` (for any non-pole `x`), the chart-pulled-back
representative `chartN ∘ toRiemannSphere ∘ (chartAt ℂ x).symm` agrees with
`f.toFun ∘ (chartAt ℂ x).symm`.

This is the chartN-side input to the smoothness proof; the analyticity of the
right-hand side at `(chartAt ℂ x) x` is exactly the open structural gap (see
the section header). -/
lemma toRiemannSphere_chartN_localForm
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    (RiemannSphere.chartN ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
      =ᶠ[𝓝 ((chartAt ℂ x) x)]
      (f.toFun ∘ (chartAt ℂ x).symm) := by
  -- Pull `f.toRiemannSphere = some ∘ f.toFun` (on a nhd of `x`) back through
  -- `(chartAt ℂ x).symm` to a nhd of `(chartAt ℂ x) x`.
  have h_evEq : f.toRiemannSphere =ᶠ[𝓝 x]
      (fun y => (OnePoint.some (f.toFun y) : RiemannSphere)) :=
    f.toRiemannSphere_eventuallyEq_some_of_nonpole hx
  -- Continuity of the chart inverse at `(chartAt ℂ x) x`.
  have h_chart_continuousAt :
      ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) := by
    have h_open : IsOpen (chartAt ℂ x).target := (chartAt ℂ x).open_target
    have h_in : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    have h_co : ContinuousOn (chartAt ℂ x).symm (chartAt ℂ x).target :=
      (chartAt ℂ x).continuousOn_invFun
    exact h_co.continuousAt (h_open.mem_nhds h_in)
  -- The base point is `((chartAt ℂ x).symm) ((chartAt ℂ x) x) = x`.
  have h_pt : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  -- Pull back: on a nhd of `(chartAt ℂ x) x`, `f.toRiemannSphere ∘ chart⁻¹ = some ∘ f.toFun ∘ chart⁻¹`.
  have h_pulled : (chartAt ℂ x).symm ⁻¹' {y | f.toRiemannSphere y =
      (OnePoint.some (f.toFun y) : RiemannSphere)} ∈ 𝓝 ((chartAt ℂ x) x) := by
    apply h_chart_continuousAt.preimage_mem_nhds
    rw [h_pt]
    exact h_evEq
  filter_upwards [h_pulled] with z hz
  -- Goal: `chartN (f.toRiemannSphere ((chartAt ℂ x).symm z))
  --        = f.toFun ((chartAt ℂ x).symm z)`.
  show RiemannSphere.chartN (f.toRiemannSphere ((chartAt ℂ x).symm z))
      = f.toFun ((chartAt ℂ x).symm z)
  rw [hz]
  exact RiemannSphere.chartN_apply_coe _

/-- **Chart-coordinate local form, pole branch (chartS), punctured.** On a
*punctured* neighborhood of `(chartAt ℂ x) x` (for any pole `x`), the
chart-pulled-back representative `chartS ∘ toRiemannSphere ∘ (chartAt ℂ x).symm`
agrees with `(f.toFun ∘ (chartAt ℂ x).symm)⁻¹` (i.e., `1 / f` in chart
coordinates).

By `meromorphicOrderAt_inv`, `(f.toFun ∘ chart⁻¹)⁻¹` has order `> 0` at the
chart point, hence vanishes there with multiplicity `|order|`. The full
chartS form on a non-punctured nhd uses `chartS ∞ = 0` plus an analytic
extension argument (the same value-vs-germ subtlety arises here too — the
chart inverse's analytic candidate has value `0` at the chart point, but the
literal value at the chart point is `chartS ∞ = 0`, which DOES match by
construction; the only obstruction is whether `f.toFun` on neighbors equals
its germ representative). -/
lemma toRiemannSphere_chartS_localForm_punctured
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ)) :
    (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
      =ᶠ[𝓝[≠] ((chartAt ℂ x) x)]
      (fun z => (f.toFun ((chartAt ℂ x).symm z))⁻¹) := by
  -- `f.toRiemannSphere = some ∘ f.toFun` on `𝓝[≠] x`, in `eventually_nhdsWithin_iff` form.
  have h_evEq : f.toRiemannSphere =ᶠ[𝓝[≠] x]
      (fun y => (OnePoint.some (f.toFun y) : RiemannSphere)) :=
    f.toRiemannSphere_eventuallyEq_some_punctured_of_pole hx
  -- Decompose `𝓝[≠] x` membership into a witness `u ∈ 𝓝 x` such that the EqOn holds on `u ∩ {x}ᶜ`.
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff] at h_evEq
  -- `h_evEq : ∀ᶠ y in 𝓝 x, y ≠ x → f.toRiemannSphere y = some (f.toFun y)`.
  -- Step 1: pull `h_evEq` (which lives in `𝓝 x`) back to a nhd of `(chartAt ℂ x) x`.
  have h_chart_continuousAt :
      ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) := by
    have h_open : IsOpen (chartAt ℂ x).target := (chartAt ℂ x).open_target
    have h_in : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    have h_co : ContinuousOn (chartAt ℂ x).symm (chartAt ℂ x).target :=
      (chartAt ℂ x).continuousOn_invFun
    exact h_co.continuousAt (h_open.mem_nhds h_in)
  have h_pt : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  -- Pull back to a nhd of `(chartAt ℂ x) x` via `Tendsto.eventually`.
  -- We use the explicit form `Tendsto (chart.symm) (𝓝 (chart x)) (𝓝 x)` (after
  -- collapsing `chart.symm (chart x) = x` via `h_pt`). The cleanest path is to
  -- first compose: produce `Tendsto chart.symm (𝓝 (chart x)) (𝓝 x)` directly.
  have h_chart_tendsto :
      Filter.Tendsto (chartAt ℂ x).symm (𝓝 ((chartAt ℂ x) x)) (𝓝 x) := by
    have := h_chart_continuousAt
    rw [ContinuousAt, h_pt] at this
    exact this
  have h_pulled := h_chart_tendsto.eventually h_evEq
  -- We also need `(chartAt ℂ x).symm z ≠ x` whenever `z ≠ (chartAt ℂ x) x` and `z ∈ chart target`,
  -- by injectivity of `(chartAt ℂ x).symm` on its target.
  -- Promote the implication-eventually to a punctured-nhd EqOn:
  -- on `𝓝[≠] ((chartAt ℂ x) x)`, both `z ≠ (chartAt ℂ x) x` AND `z` is eventually in chart target,
  -- giving `(chartAt ℂ x).symm z ≠ x`.
  -- We bundle this into an `EventuallyEq` on `𝓝[≠] ((chartAt ℂ x) x)`.
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  -- Goal: `∀ᶠ z in 𝓝 ((chartAt ℂ x) x), z ∈ {(chartAt ℂ x) x}ᶜ →
  --        chartS (f.toRiemannSphere ((chartAt ℂ x).symm z)) = (f.toFun ((chartAt ℂ x).symm z))⁻¹`.
  -- We combine `h_pulled` (impl eventually) with chart-target membership (open nhd).
  have h_target_mem : (chartAt ℂ x).target ∈ 𝓝 ((chartAt ℂ x) x) :=
    (chartAt ℂ x).open_target.mem_nhds
      ((chartAt ℂ x).map_source (mem_chart_source ℂ x))
  filter_upwards [h_pulled, h_target_mem] with z hz_impl hz_target hz_ne
  -- `hz_ne : z ∈ {(chartAt ℂ x) x}ᶜ`, i.e. `z ≠ (chartAt ℂ x) x`.
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz_ne
  -- Show `(chartAt ℂ x).symm z ≠ x`.
  have h_symm_ne : (chartAt ℂ x).symm z ≠ x := by
    intro hzx
    apply hz_ne
    have := (chartAt ℂ x).right_inv hz_target
    rw [hzx] at this
    exact this.symm
  -- Apply the implication. `hz_impl` expects `(chartAt ℂ x).symm z ∈ ({x} : Set X)ᶜ`.
  have h_symm_compl : (chartAt ℂ x).symm z ∈ ({x} : Set X)ᶜ := by
    simp [Set.mem_compl_iff, Set.mem_singleton_iff, h_symm_ne]
  have hz : f.toRiemannSphere ((chartAt ℂ x).symm z) =
      (OnePoint.some (f.toFun ((chartAt ℂ x).symm z)) : RiemannSphere) :=
    hz_impl h_symm_compl
  -- Conclude.
  show RiemannSphere.chartS (f.toRiemannSphere ((chartAt ℂ x).symm z))
      = (f.toFun ((chartAt ℂ x).symm z))⁻¹
  rw [hz]
  exact RiemannSphere.chartS_apply_coe _

end MeromorphicNonzero

/-! ### Headline statement (Prop-only, preserved as a hook)

The headline `toRiemannSphere_contMDiff_statement` is preserved as a
`Prop`-valued `def`. The unconditional discharge requires either a
strengthening of `MeromorphicNonzero` (germ-value alignment) or a quotient
restructure; see the section header for the obstruction analysis.
-/

namespace MeromorphicNonzero

/-- **(R1, statement only)** The pole extension of `f` is `ContMDiff` from
`X` to `RiemannSphere` (with model `𝓘(ℂ, ℂ) → 𝓘(ℂ)`, smoothness `ω`).

Preserved as a `Prop`-valued `def` for downstream callers that may have
threaded it as an explicit hypothesis. Now discharged unconditionally by
`MeromorphicNonzero.toRiemannSphere_contMDiff` (see below), because the
`regular_continuousAt` field added in `M1` closes the value-vs-germ gap
that previously blocked the discharge. -/
def toRiemannSphere_contMDiff_statement (f : MeromorphicNonzero X) : Prop :=
  ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f.toRiemannSphere

end MeromorphicNonzero

/-! ### `R1` headline — full unconditional `ContMDiff` of the pole extension

With `MeromorphicNonzero.regular_continuousAt` (the `M1`-shipped continuity
field), we discharge the headline `R1` theorem unconditionally. The proof
case-splits at every `x : X`:

* **Non-pole branch** (`0 ≤ mmeromorphicOrderAt I f x`): `regular_continuousAt`
  gives `ContinuousAt f.toFun x`, hence `(f.toFun ∘ chart.symm)` is continuous
  at `chart x`. Combined with chart-pulled-back meromorphy at `chart x`,
  mathlib's `MeromorphicAt.analyticAt` upgrades it to `AnalyticAt`, and we
  read the result through the north chart `chartN` (`chartN ∘ some = id` on
  finite points), giving `ContMDiffAt`.

* **Pole branch** (`mmeromorphicOrderAt I f x < 0`): the south chart `chartS`
  sends `∞ ↦ 0` and `(some w) ↦ w⁻¹`. The chart-coordinate composition
  `chartS ∘ f.toRiemannSphere ∘ chart.symm` agrees with `(f.toFun ∘ chart.symm)⁻¹`
  on a punctured neighborhood of `chart x` (by L1's
  `toRiemannSphere_chartS_localForm_punctured`) and equals `0` at `chart x`
  (since `f.toRiemannSphere x = ∞` and `chartS ∞ = 0`). The chart-pulled-back
  inverse has *positive* meromorphic order at `chart x` (`meromorphicOrderAt_inv`
  flips sign), so `(f.toFun ∘ chart.symm)⁻¹` tends to `0` as `z → chart x`
  (`tendsto_zero_of_meromorphicOrderAt_pos`); together with the central value
  `0`, this means our composition is **continuous at `chart x`**. The
  composition is also meromorphic at `chart x` (germ-equivalent to the
  meromorphic chart-pulled-back inverse), so by `MeromorphicAt.analyticAt`
  it is analytic at `chart x`, hence `ContMDiffAt`.

The `regular_continuousAt` field is **load-bearing** in the non-pole branch:
without it, `f.toFun x` could disagree with the analytic-continuation limit
at finitely many regular points, making `toRiemannSphere` genuinely
discontinuous there, and the headline theorem **false** in the prior
`MeromorphicNonzero` structure. -/

namespace MeromorphicNonzero

/-! #### Helper lemmas (chart-pullback ↔ literal, continuity, analyticity) -/

/-- **Chart pushes punctured neighborhoods to punctured neighborhoods.** Used
to transfer pole-side `Tendsto` statements from the chart-pulled-back form to
the literal form. The proof uses injectivity of the chart on its source. -/
private lemma tendsto_chart_nhdsNE (x : X) :
    Filter.Tendsto (chartAt ℂ x) (𝓝[≠] x) (𝓝[≠] ((chartAt ℂ x) x)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · -- Continuity at `x` ⇒ Tendsto on punctured filter (mono_left).
    have h_co : ContinuousAt (chartAt ℂ x) x :=
      (chartAt ℂ x).continuousAt (mem_chart_source ℂ x)
    exact h_co.tendsto.mono_left nhdsWithin_le_nhds
  · -- Eventually, `chart y ≠ chart x` for `y ≠ x` near `x`.
    have h_source_mem : (chartAt ℂ x).source ∈ 𝓝 x :=
      (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
    have h_source_ne : (chartAt ℂ x).source ∈ 𝓝[≠] x :=
      mem_nhdsWithin_of_mem_nhds h_source_mem
    filter_upwards [h_source_ne, self_mem_nhdsWithin (s := ({x} : Set X)ᶜ) (a := x)]
      with y hy_source hy_ne
    -- Goal: `chart y ∈ {chart x}ᶜ`, i.e. `chart y ≠ chart x`.
    intro h_eq
    apply hy_ne
    -- `chart y = chart x` and `y, x ∈ source` ⇒ `y = x` by injectivity on source.
    have h_inj : (chartAt ℂ x).symm ((chartAt ℂ x) y)
        = (chartAt ℂ x).symm ((chartAt ℂ x) x) :=
      congrArg _ h_eq
    rw [(chartAt ℂ x).left_inv hy_source,
        (chartAt ℂ x).left_inv (mem_chart_source ℂ x)] at h_inj
    exact h_inj

/-- The literal `f.toFun` and the round-trip `(f.toFun ∘ chart.symm) ∘ chart`
agree on a neighborhood of `x` (specifically on the chart source, which is a
nhd of `x`). -/
private lemma toFun_eventuallyEq_chartPullback (f : MeromorphicNonzero X) (x : X) :
    f.toFun =ᶠ[𝓝 x]
      ((f.toFun ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) := by
  have h_source_mem : (chartAt ℂ x).source ∈ 𝓝 x :=
    (chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)
  filter_upwards [h_source_mem] with y hy
  show f.toFun y = f.toFun ((chartAt ℂ x).symm ((chartAt ℂ x) y))
  rw [(chartAt ℂ x).left_inv hy]

/-- At a non-pole `x`, the chart-pulled-back representative
`(f.toFun ∘ (chartAt ℂ x).symm)` is **continuous at** `(chartAt ℂ x) x`.
Load-bearing: uses `f.regular_continuousAt`. -/
private lemma continuousAt_chartPullback_of_nonneg
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    ContinuousAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := by
  have h_chart_continuousAt :
      ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) := by
    have h_open : IsOpen (chartAt ℂ x).target := (chartAt ℂ x).open_target
    have h_in : (chartAt ℂ x) x ∈ (chartAt ℂ x).target :=
      (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    have h_co : ContinuousOn (chartAt ℂ x).symm (chartAt ℂ x).target :=
      (chartAt ℂ x).continuousOn_invFun
    exact h_co.continuousAt (h_open.mem_nhds h_in)
  have h_pt : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  have h_f_continuousAt : ContinuousAt f.toFun x := f.regular_continuousAt x hx
  -- `ContinuousAt.comp` expects `ContinuousAt g (f x₀)`; we need to align the
  -- inner point via `h_pt` (rewriting `x` as `chart.symm (chart x)`).
  have h_f_at_pt :
      ContinuousAt f.toFun ((chartAt ℂ x).symm ((chartAt ℂ x) x)) := by
    rw [h_pt]; exact h_f_continuousAt
  exact h_f_at_pt.comp h_chart_continuousAt

/-- At a non-pole `x`, the chart-pulled-back representative
`(f.toFun ∘ chart.symm)` is **analytic** at `(chartAt ℂ x) x`. This is the
load-bearing use of `regular_continuousAt`: continuity + meromorphy ⇒ analyticity
(via mathlib's `MeromorphicAt.analyticAt`). -/
private lemma analyticAt_chartPullback_of_nonneg
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := by
  have h_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    f.meromorphic x trivial
  have h_cont := f.continuousAt_chartPullback_of_nonneg hx
  exact h_mero.analyticAt h_cont

/-- At a pole `x`, the chart-pulled-back inverse `(f.toFun ∘ chart.symm)⁻¹`
has **positive** meromorphic order at `(chartAt ℂ x) x`. -/
private lemma meromorphicOrderAt_inv_chartPullback_pos
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ)) :
    0 < meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)⁻¹ ((chartAt ℂ x) x) := by
  have h_orderEq :
      mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x
        = meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := rfl
  rw [h_orderEq] at hx
  rw [meromorphicOrderAt_inv]
  -- Direct manipulation in `WithTop ℤ`: from `hx : a < 0`, extract `a = (n : ℤ)` with
  -- `n < 0`, then `-a = (-n : ℤ)` with `-n > 0`.
  -- Since `a < 0` we have `a ≠ ⊤` (top isn't `< 0`).
  have h_ne_top : meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) ≠ ⊤ := fun h => by
    rw [h] at hx; exact absurd hx (not_lt.mpr le_top)
  -- Lift to `ℤ` and conclude.
  cases h_eq : meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) with
  | top => exact absurd h_eq h_ne_top
  | coe n =>
    -- `cases h_eq:` substitutes `meromorphicOrderAt ...` ↦ `↑n` in the goal but NOT
    -- in `hx` (Lean 4 behavior). Manually rewrite `hx`.
    rw [h_eq] at hx
    -- Now `hx : ↑n < 0` and goal: `0 < -↑n`.
    have h_n_neg : n < 0 := by exact_mod_cast hx
    -- `-↑n = ↑(-n)` and `0 = ↑0` in `WithTop ℤ` (rfl), so reduce to `0 < (-n : ℤ)`.
    show (0 : WithTop ℤ) < ((-n : ℤ) : WithTop ℤ)
    exact_mod_cast (neg_pos.mpr h_n_neg)

/-- At a pole `x`, the chart-pulled-back form `(f.toFun ∘ chart.symm)` tends
to `cobounded ℂ` on the punctured nhd of `(chartAt ℂ x) x`. -/
private lemma tendsto_chartPullback_cobounded_of_neg
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ)) :
    Filter.Tendsto (f.toFun ∘ (chartAt ℂ x).symm)
      (𝓝[≠] ((chartAt ℂ x) x)) (Bornology.cobounded ℂ) := by
  have h_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
    f.meromorphic x trivial
  have h_ord :
      meromorphicOrderAt (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) < 0 := hx
  exact (tendsto_cobounded_iff_meromorphicOrderAt_neg h_mero).mpr h_ord

/-- At a pole `x`, the literal `f.toFun` tends to `cobounded ℂ` on `𝓝[≠] x`.
Combines the chart-pulled-back `Tendsto` with chart's punctured-nhd
push-forward and the `EvEq` from `f.toFun` to `(f ∘ chart.symm) ∘ chart`. -/
private lemma tendsto_cobounded_of_pole
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ)) :
    Filter.Tendsto f.toFun (𝓝[≠] x) (Bornology.cobounded ℂ) := by
  have h_chart_pun := tendsto_chart_nhdsNE (X := X) x
  have h_pole := f.tendsto_chartPullback_cobounded_of_neg hx
  have h_comp :
      Filter.Tendsto ((f.toFun ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x))
        (𝓝[≠] x) (Bornology.cobounded ℂ) :=
    h_pole.comp h_chart_pun
  have h_evEq : f.toFun =ᶠ[𝓝 x]
      ((f.toFun ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) :=
    f.toFun_eventuallyEq_chartPullback x
  have h_evEq_pun :
      f.toFun =ᶠ[𝓝[≠] x] ((f.toFun ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x)) :=
    h_evEq.filter_mono nhdsWithin_le_nhds
  exact h_comp.congr' h_evEq_pun.symm

/-- At a pole `x`, `f.toRiemannSphere` is `ContinuousAt x`. The image is `∞`,
and as `y → x` (punctured), `f.toFun y → cobounded ℂ`, hence `some (f.toFun y) → ∞`
in `OnePoint ℂ`. Combined with the trivial pure-`x` branch (image `∞`), this
yields full `Tendsto f.toRiemannSphere (𝓝 x) (𝓝 ∞)`. -/
private lemma continuousAt_toRiemannSphere_of_pole
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ)) :
    ContinuousAt f.toRiemannSphere x := by
  have h_val : f.toRiemannSphere x = (∞ : RiemannSphere) :=
    f.toRiemannSphere_apply_of_neg hx
  rw [ContinuousAt, h_val]
  -- Decompose the source filter: `𝓝 x = 𝓝[≠] x ⊔ pure x`.
  rw [show (𝓝 x) = 𝓝[≠] x ⊔ pure x from (nhdsNE_sup_pure x).symm]
  rw [Filter.tendsto_sup]
  refine ⟨?_, ?_⟩
  · -- 𝓝[≠] x branch: agrees with `some ∘ f.toFun`, which → 𝓝 ∞ via cobounded.
    have h_evEq : f.toRiemannSphere =ᶠ[𝓝[≠] x]
        (fun y => (OnePoint.some (f.toFun y) : RiemannSphere)) :=
      f.toRiemannSphere_eventuallyEq_some_punctured_of_pole hx
    refine Filter.Tendsto.congr' h_evEq.symm ?_
    -- `Tendsto (some ∘ f.toFun) (𝓝[≠] x) (𝓝 ∞)`. Land in the left summand.
    have h_pole_cobd := f.tendsto_cobounded_of_pole hx
    -- `cobounded ℂ = cocompact ℂ` (metric spaces) ≤ `coclosedCompact ℂ`.
    have h_cocl :
        Filter.Tendsto f.toFun (𝓝[≠] x) (Filter.coclosedCompact ℂ) := by
      have h1 : Filter.Tendsto f.toFun (𝓝[≠] x) (Filter.cocompact ℂ) := by
        rw [← Metric.cobounded_eq_cocompact]; exact h_pole_cobd
      exact h1.mono_right Filter.cocompact_le_coclosedCompact
    -- `Tendsto ((↑) : ℂ → RiemannSphere) (coclosedCompact ℂ) (map ↑ ...)` is `tendsto_map`.
    have h_some_cocl :
        Filter.Tendsto (fun y => (OnePoint.some (f.toFun y) : RiemannSphere))
            (𝓝[≠] x) (Filter.map ((↑) : ℂ → RiemannSphere) (Filter.coclosedCompact ℂ)) :=
      Filter.tendsto_map.comp h_cocl
    -- Bump up to `𝓝 ∞ = map ↑ ... ⊔ pure ∞` via `mono_right le_sup_left`.
    rw [OnePoint.nhds_infty_eq]
    exact h_some_cocl.mono_right le_sup_left
  · -- pure x branch: `pure (f.toRiemannSphere x) = pure ∞ ≤ 𝓝 ∞`.
    -- `Tendsto F (pure x) g ↔ pure (F x) ≤ g`. With `F x = ∞`, this is `pure ∞ ≤ 𝓝 ∞`.
    refine (Filter.tendsto_pure_left).mpr ?_
    intro s hs
    rw [h_val]
    exact mem_of_mem_nhds hs

/-! #### Pole branch: chart-coordinate analyticity through `chartS` -/

/-- At a pole `x`, the chart-coordinate composition
`chartS ∘ f.toRiemannSphere ∘ chart.symm` is **continuous at** `(chartAt ℂ x) x`.
On the punctured nhd it equals the chart-pulled-back inverse
`(f.toFun ∘ chart.symm)⁻¹`, which → `0` (`tendsto_zero_of_meromorphicOrderAt_pos`),
and at the central point it equals `chartS ∞ = 0`. -/
private lemma continuousAt_chartS_chartPullback_of_pole
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ)) :
    ContinuousAt
        (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := by
  -- Decompose `𝓝 (chart x) = 𝓝[≠] (chart x) ⊔ pure (chart x)`.
  rw [ContinuousAt]
  -- Establish the value at the central point: `chartS ∞ = 0`.
  have h_val_at_x :
      (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x) = (0 : ℂ) := by
    show RiemannSphere.chartS (f.toRiemannSphere ((chartAt ℂ x).symm ((chartAt ℂ x) x))) = 0
    rw [(chartAt ℂ x).left_inv (mem_chart_source ℂ x),
        f.toRiemannSphere_apply_of_neg hx]
    exact RiemannSphere.chartS_apply_infty
  rw [h_val_at_x]
  rw [show (𝓝 ((chartAt ℂ x) x)) = 𝓝[≠] ((chartAt ℂ x) x) ⊔ pure ((chartAt ℂ x) x)
      from (nhdsNE_sup_pure ((chartAt ℂ x) x)).symm]
  rw [Filter.tendsto_sup]
  refine ⟨?_, ?_⟩
  · -- 𝓝[≠] (chart x): use L1's `chartS_localForm_punctured` to reduce to
    -- `(f.toFun ∘ chart.symm)⁻¹`, which → 0 by `tendsto_zero_of_meromorphicOrderAt_pos`.
    have h_local := f.toRiemannSphere_chartS_localForm_punctured hx
    refine Filter.Tendsto.congr' h_local.symm ?_
    -- Goal: `Tendsto (fun z => (f.toFun ((chartAt ℂ x).symm z))⁻¹) (𝓝[≠] (chart x)) (𝓝 0)`.
    -- This is `Tendsto (f.toFun ∘ chart.symm)⁻¹ (𝓝[≠] (chart x)) (𝓝 0)`.
    -- By `tendsto_zero_of_meromorphicOrderAt_pos` applied to `(f ∘ chart.symm)⁻¹`.
    have h_pos := f.meromorphicOrderAt_inv_chartPullback_pos hx
    have h_tend :=
      tendsto_zero_of_meromorphicOrderAt_pos (f := (f.toFun ∘ (chartAt ℂ x).symm)⁻¹)
        (x := (chartAt ℂ x) x) h_pos
    -- The goal-LHS is `fun z => (f.toFun (chart.symm z))⁻¹`; this is exactly
    -- `(f.toFun ∘ chart.symm)⁻¹`.
    convert h_tend using 1
  · -- pure (chart x): immediate.
    refine (Filter.tendsto_pure_left).mpr ?_
    intro s hs
    -- Goal: `(chartS ∘ f.toRiemannSphere ∘ chart.symm) (chart x) ∈ s`.
    -- We've already shown this equals `0`. After the `rw [h_val_at_x]` above, the
    -- LHS in this branch is reduced to checking `0 ∈ s` under `s ∈ 𝓝 (0 : ℂ)`.
    -- BUT wait — the outer `rw [h_val_at_x]` happened BEFORE the source decomposition
    -- and only changed the *target* of the Tendsto (from `𝓝 (... (chart x))` to `𝓝 0`).
    -- The source filter is still `pure (chart x)`, and the function being applied
    -- is the original `chartS ∘ f.toRiemannSphere ∘ chart.symm`, NOT `0`.
    -- So we need: `(chartS ∘ f.toRiemannSphere ∘ chart.symm) (chart x) ∈ s`.
    -- By `h_val_at_x`, that LHS equals `0`, and `0 ∈ s` follows from `s ∈ 𝓝 0`.
    rw [h_val_at_x]
    exact mem_of_mem_nhds hs

/-- At a pole `x`, the chart-coordinate composition
`chartS ∘ f.toRiemannSphere ∘ chart.symm` is **meromorphic at** `(chartAt ℂ x) x`.
On a punctured nhd it equals the chart-pulled-back inverse
`(f.toFun ∘ chart.symm)⁻¹`; meromorphy is invariant under such modification. -/
private lemma meromorphicAt_chartS_chartPullback_of_pole
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ)) :
    MeromorphicAt
        (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := by
  -- The chart-pulled-back inverse is meromorphic at `chart x`.
  have h_inv_mero : MeromorphicAt (f.toFun ∘ (chartAt ℂ x).symm)⁻¹ ((chartAt ℂ x) x) :=
    (f.meromorphic x trivial).inv
  -- Local form gives EvEq on `𝓝[≠] (chart x)` to `(f.toFun ∘ chart.symm)⁻¹`.
  have h_local := f.toRiemannSphere_chartS_localForm_punctured hx
  -- `meromorphicAt_congr` lifts.
  have h_local' :
      (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
        =ᶠ[𝓝[≠] ((chartAt ℂ x) x)] (f.toFun ∘ (chartAt ℂ x).symm)⁻¹ := h_local
  exact (MeromorphicAt.meromorphicAt_congr h_local').mpr h_inv_mero

/-- At a pole `x`, the chart-coordinate composition
`chartS ∘ f.toRiemannSphere ∘ chart.symm` is **analytic at** `(chartAt ℂ x) x`.
Combines pole-side continuity (above) with pole-side meromorphy (above) via
mathlib's `MeromorphicAt.analyticAt`. -/
private lemma analyticAt_chartS_chartPullback_of_pole
    (f : MeromorphicNonzero X) {x : X}
    (hx : mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x < (0 : WithTop ℤ)) :
    AnalyticAt ℂ
        (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) :=
  (f.meromorphicAt_chartS_chartPullback_of_pole hx).analyticAt
    (f.continuousAt_chartS_chartPullback_of_pole hx)

/-! #### Non-pole branch: continuity of `f.toRiemannSphere` -/

/-- At a non-pole `x`, `f.toRiemannSphere` is `ContinuousAt x`: it agrees with
the continuous map `OnePoint.some ∘ f.toFun` on a neighborhood of `x`, by L1's
`toRiemannSphere_eventuallyEq_some_of_nonpole` plus `regular_continuousAt`. -/
private lemma continuousAt_toRiemannSphere_of_nonpole
    (f : MeromorphicNonzero X) {x : X}
    (hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x) :
    ContinuousAt f.toRiemannSphere x := by
  have h_evEq := f.toRiemannSphere_eventuallyEq_some_of_nonpole hx
  have h_some_cont :
      ContinuousAt (fun y => (OnePoint.some (f.toFun y) : RiemannSphere)) x :=
    OnePoint.continuous_coe.continuousAt.comp (f.regular_continuousAt x hx)
  exact h_some_cont.congr h_evEq.symm

end MeromorphicNonzero

/-! ### `R1` headline theorem -/

namespace MeromorphicNonzero

/-- **R1, full headline (unconditional).** The pole extension of `f` is
`ContMDiff` of class `ω` (analytic) from `X` to `RiemannSphere`, with model
`𝓘(ℂ, ℂ) → 𝓘(ℂ)`.

The proof case-splits at every `x : X`:

* **Non-pole** (`0 ≤ mmeromorphicOrderAt I f x`): `regular_continuousAt` makes
  `f.toRiemannSphere` continuous at `x` and the chart-coord composition
  `chartN ∘ f.toRiemannSphere ∘ chart.symm` analytic at `(chartAt ℂ x) x`.
* **Pole** (`< 0`): `f.toRiemannSphere` is continuous at `x` (the punctured
  neighborhood maps via `some ∘ f.toFun` to a cobounded set, hence to a
  neighborhood of `∞`) and `chartS ∘ f.toRiemannSphere ∘ chart.symm` is
  analytic at `(chartAt ℂ x) x`.

The `regular_continuousAt` field is **load-bearing** in the non-pole branch:
without it, `f.toRiemannSphere` would be discontinuous at finitely many
regular points and the headline theorem **false**. -/
theorem toRiemannSphere_contMDiff (f : MeromorphicNonzero X) :
    ContMDiff (𝓘(ℂ, ℂ)) (𝓘(ℂ)) ω f.toRiemannSphere := by
  intro x
  -- Source-side chart membership.
  have hx_source : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
  have hfx_source :
      f.toRiemannSphere x ∈ (chartAt ℂ (f.toRiemannSphere x)).source :=
    mem_chart_source ℂ (f.toRiemannSphere x)
  -- Reduce `ContMDiffAt` to (continuity ∧ chart-coord ContDiffWithinAt).
  rw [contMDiffAt_iff_of_mem_source hx_source hfx_source]
  -- The model on the source is `𝓘(ℂ,ℂ)` with `range I = univ`.
  have h_range : Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) = Set.univ :=
    ModelWithCorners.range_eq_univ _
  rw [h_range, contDiffWithinAt_univ]
  -- Case split on pole vs non-pole.
  by_cases hx : 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) f.toFun x
  · -- Non-pole branch.
    refine ⟨f.continuousAt_toRiemannSphere_of_nonpole hx, ?_⟩
    -- Target chart is `chartN`.
    have h_target_eq : f.toRiemannSphere x = (OnePoint.some (f.toFun x) : RiemannSphere) :=
      f.toRiemannSphere_apply_of_nonneg hx
    have h_chartTarget :
        chartAt ℂ (f.toRiemannSphere x) = RiemannSphere.chartN := by
      rw [h_target_eq]; exact chartAt_riemannSphere_coe (f.toFun x)
    -- Use `ContDiffAt.congr_of_eventuallyEq` with the analytic candidate
    -- `f.toFun ∘ chart.symm`.
    have h_an : AnalyticAt ℂ (f.toFun ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) :=
      f.analyticAt_chartPullback_of_nonneg hx
    have h_cd : ContDiffAt ℂ (ω : WithTop ℕ∞) (f.toFun ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := h_an.contDiffAt
    -- Local form: chart-coord composition agrees with `f.toFun ∘ chart.symm`
    -- on a nhd of `(chartAt ℂ x) x`.
    have h_local := f.toRiemannSphere_chartN_localForm hx
    -- The goal references `extChartAt` on both sides; collapse to bare charts
    -- since the model `𝓘(ℂ,ℂ)` is the identity.
    have h_extChart_x : (extChartAt 𝓘(ℂ, ℂ) x) x = (chartAt ℂ x) x := by
      simp [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe]
    rw [h_extChart_x]
    refine h_cd.congr_of_eventuallyEq ?_
    -- We must show:
    --   `extChartAt 𝓘(ℂ) (f.toRiemannSphere x) ∘ f.toRiemannSphere
    --      ∘ (extChartAt 𝓘(ℂ,ℂ) x).symm =ᶠ[𝓝 (chart x)] f.toFun ∘ (chartAt ℂ x).symm`.
    -- Since `𝓘(ℂ,ℂ) = id`, both `extChartAt`s collapse to bare charts.
    refine h_local.mono ?_
    intro z hz
    -- `hz : chartN (f.toRiemannSphere ((chartAt ℂ x).symm z))
    --        = f.toFun ((chartAt ℂ x).symm z)`.
    show (extChartAt 𝓘(ℂ) (f.toRiemannSphere x))
            (f.toRiemannSphere ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
        = (f.toFun ∘ (chartAt ℂ x).symm) z
    have h_extSymm : (extChartAt 𝓘(ℂ, ℂ) x).symm z = (chartAt ℂ x).symm z := by
      simp [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe_symm]
    rw [h_extSymm]
    have h_extApply :
        (extChartAt 𝓘(ℂ) (f.toRiemannSphere x))
            (f.toRiemannSphere ((chartAt ℂ x).symm z))
          = RiemannSphere.chartN (f.toRiemannSphere ((chartAt ℂ x).symm z)) := by
      simp [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
            h_chartTarget]
    rw [h_extApply]
    -- Goal: `chartN (f.toRiemannSphere (chart.symm z)) = (f.toFun ∘ chart.symm) z`.
    -- `hz` provides the same equation up to `Function.comp_apply` unfolding.
    simpa [Function.comp_apply] using hz
  · -- Pole branch.
    push_neg at hx
    refine ⟨f.continuousAt_toRiemannSphere_of_pole hx, ?_⟩
    -- Target chart is `chartS`.
    have h_target_eq : f.toRiemannSphere x = (∞ : RiemannSphere) :=
      f.toRiemannSphere_apply_of_neg hx
    have h_chartTarget :
        chartAt ℂ (f.toRiemannSphere x) = RiemannSphere.chartS := by
      rw [h_target_eq]; exact chartAt_riemannSphere_infty
    -- Analytic candidate: `chartS ∘ f.toRiemannSphere ∘ chart.symm` is itself analytic at `chart x`.
    have h_an : AnalyticAt ℂ
        (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) :=
      f.analyticAt_chartS_chartPullback_of_pole hx
    have h_cd : ContDiffAt ℂ (ω : WithTop ℕ∞)
        (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := h_an.contDiffAt
    have h_extChart_x : (extChartAt 𝓘(ℂ, ℂ) x) x = (chartAt ℂ x) x := by
      simp [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe]
    rw [h_extChart_x]
    -- Goal: `ContDiffAt ... (extChartAt I' y ∘ f.toRiemannSphere ∘ (extChartAt I x).symm) (chart x)`.
    -- We rewrite both extChartAt's: source via `extend_coe_symm` (collapses to chart.symm)
    -- and target via the chart-rewrite to `chartS`.
    refine h_cd.congr_of_eventuallyEq ?_
    -- EvEq on `𝓝 (chart x)`: pointwise the extChartAt-compositions equal the bare ones.
    refine Filter.Eventually.of_forall ?_
    intro z
    show (extChartAt 𝓘(ℂ) (f.toRiemannSphere x))
            (f.toRiemannSphere ((extChartAt 𝓘(ℂ, ℂ) x).symm z))
        = (RiemannSphere.chartS ∘ f.toRiemannSphere ∘ (chartAt ℂ x).symm) z
    have h_extSymm : (extChartAt 𝓘(ℂ, ℂ) x).symm z = (chartAt ℂ x).symm z := by
      simp [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe_symm]
    rw [h_extSymm]
    show (extChartAt 𝓘(ℂ) (f.toRiemannSphere x))
            (f.toRiemannSphere ((chartAt ℂ x).symm z))
        = RiemannSphere.chartS (f.toRiemannSphere ((chartAt ℂ x).symm z))
    simp [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_coe,
          h_chartTarget]

end MeromorphicNonzero

end Jacobians.Discharge

