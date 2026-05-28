/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Analysis.Analytic.Order
import Jacobians.Discharge.Manifold.AnalyticFiberDiscrete
import Jacobians.Discharge.Manifold.CriticalSetDiscrete
import Jacobians.Discharge.Manifold.CriticalSetDefinition
import Jacobians.Discharge.Manifold.CriticalSetFiniteUnconditional
import Jacobians.Discharge.Manifold.CriticalSetWitnessSupplier

set_option autoImplicit true


/-! # Planar criticality core: critical points are isolated

This file delivers the **planar-side analytic core** that powers
"critical values of a non-constant analytic map between compact connected
charted spaces over ℂ are finite":

> If `F : ℂ → ℂ` is analytic at `z₀` and not eventually equal to `F z₀`
> on any neighbourhood of `z₀`, then there is an open set `U ∋ z₀` on
> which `z₀` is the unique zero of `deriv F` — that is, `z₀` is an
> *isolated* critical point of `F`.

The argument is the standard "non-constant analytic map has isolated
critical points" reduction, packaged here purely on the planar `ℂ → ℂ`
side via mathlib's `AnalyticAt.analyticOrderAt_deriv_add_one`. This
lemma states `analyticOrderAt (deriv F) z₀ + 1 = analyticOrderAt (F · - F z₀) z₀`,
so once we know the right-hand side is finite (the "non-constant" content),
the left-hand side is also finite, ruling out the "deriv `F` eventually
zero" branch of the analytic dichotomy.

## What this file ships

* `AnalyticAt.deriv_not_eventually_zero_of_not_eventually_const` — the
  planar core: from "`F` analytic at `z₀` and not eventually `F z₀`",
  conclude `deriv F` is not eventually `0`.

* `AnalyticAt.isolated_critical_of_not_eventually_const` — the
  isolation form: there is an open `U ∋ z₀` with
  `U ∩ {z | deriv F z = 0} ⊆ {z₀}`.

* `criticalChartPullbackData_of_chart_pullback_not_eventually_const` —
  manifold-side wrapper. Given:
  - a `CriticalChartBridgeBundle f x` whose `F'` is `deriv F` for the
    chart pullback `F`, and
  - the chart-pullback non-eventual-constancy hypothesis,
  produce a `CriticalChartPullbackData f.toRiemannSphere f.criticalSet x`
  by recycling the existing `criticalChartPullbackData_of_bridge`
  constructor.

  This file does **not** build the bridge bundle from a `MeromorphicNonzero`
  function (that requires the order-bridging carpentry already named in
  `CriticalSetWitnessSupplier.lean` as residual R-MN); the wrapper here
  is the planar-core hand-off that consumes the "not eventually constant"
  hypothesis and produces the `hF'ne` field of the bundle.

## Status — no `sorry`, no `axiom`

* No `axiom`, no `sorry`.
* No signature change to anything outside this new file.
* The headline `criticalSet.Finite` for arbitrary non-constant
  `ContMDiff f : X → Y` between compact connected charted spaces over ℂ
  is **not** delivered unconditionally: it still routes through
  `CriticalSetFiniteUnconditional.criticalSet_finite_of_witness`, which
  consumes the `CriticalSetWitness` package whose construction (residuals
  R-MN and R-Closed) is owed to separate chips. What this file delivers
  is the planar-side critical-point isolation core that those chips will
  consume.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff

namespace Jacobians.Discharge

namespace Manifold

universe u v

/-! ## ℂ-analytic core: derivative is not eventually zero -/

/-- **Derivative not eventually zero from non-constancy.** If
`F : ℂ → ℂ` is analytic at `z₀` and `F` is not eventually equal to
`F z₀` on any neighbourhood of `z₀`, then `deriv F` is not eventually
zero on any neighbourhood of `z₀`.

The proof reads off `AnalyticAt.analyticOrderAt_deriv_add_one`:
`analyticOrderAt (deriv F) z₀ + 1 = analyticOrderAt (F · - F z₀) z₀`.
The hypothesis "`F` not eventually `F z₀`" forces the right-hand side
to be ≠ ⊤ (otherwise `F z = F z₀` on a neighbourhood, contradiction).
Hence the left-hand side is ≠ ⊤, i.e. `deriv F` is not eventually 0
(via `analyticOrderAt_eq_top`). -/
lemma deriv_not_eventually_zero_of_analyticAt_not_eventually_const
    {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F z₀)
    (hne : ¬ ∀ᶠ z in 𝓝 z₀, F z = F z₀) :
    ¬ ∀ᶠ z in 𝓝 z₀, deriv F z = 0 := by
  -- Suppose `deriv F` is eventually 0; derive `F` eventually `F z₀`,
  -- contradicting `hne`.
  intro h_dz
  -- `analyticOrderAt (deriv F) z₀ = ⊤` from `analyticOrderAt_eq_top`.
  have h_dz_top : analyticOrderAt (deriv F) z₀ = ⊤ :=
    analyticOrderAt_eq_top.mpr h_dz
  -- The mathlib lemma: order(deriv F) + 1 = order(F - F z₀).
  have h_eq : analyticOrderAt (deriv F) z₀ + 1 =
      analyticOrderAt (fun z => F z - F z₀) z₀ :=
    hF.analyticOrderAt_deriv_add_one
  -- So `order(F - F z₀) = ⊤ + 1 = ⊤`.
  have h_F_top : analyticOrderAt (fun z => F z - F z₀) z₀ = ⊤ := by
    rw [h_dz_top] at h_eq
    -- ⊤ + 1 = ⊤ in ℕ∞.
    simpa using h_eq.symm
  -- That means `F z = F z₀` eventually near `z₀`.
  have h_F_eq : ∀ᶠ z in 𝓝 z₀, F z - F z₀ = 0 :=
    analyticOrderAt_eq_top.mp h_F_top
  apply hne
  filter_upwards [h_F_eq] with z hz
  exact sub_eq_zero.mp hz

/-! ## ℂ-analytic core: critical points are isolated -/

/-- **Isolated critical point of an analytic map.** If `F : ℂ → ℂ` is
analytic at `z₀` and `F` is not eventually equal to `F z₀` on any
neighbourhood of `z₀`, then there is an open `U ∋ z₀` such that
`U ∩ {z | deriv F z = 0} ⊆ {z₀}`.

Either `deriv F z₀ = 0` (in which case the conclusion strengthens to
`U ∩ {z | deriv F z = 0} = {z₀}`) or `deriv F z₀ ≠ 0` (in which case
the conclusion strengthens to `U ∩ {z | deriv F z = 0} = ∅`). The
weaker `⊆` form is what downstream chart-pullback data consumes. -/
lemma isolated_critical_of_analyticAt_not_eventually_const
    {F : ℂ → ℂ} {z₀ : ℂ}
    (hF : AnalyticAt ℂ F z₀)
    (hne : ¬ ∀ᶠ z in 𝓝 z₀, F z = F z₀) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧
      U ∩ {z | deriv F z = 0} ⊆ {z₀} := by
  -- `deriv F` is analytic at `z₀` and not eventually 0.
  have hdF : AnalyticAt ℂ (deriv F) z₀ := hF.deriv
  have hdne : ¬ ∀ᶠ z in 𝓝 z₀, deriv F z = 0 :=
    deriv_not_eventually_zero_of_analyticAt_not_eventually_const hF hne
  -- Dichotomy from mathlib: either eventually 0, or `≠ 0` on a punctured nbhd.
  rcases hdF.eventually_eq_zero_or_eventually_ne_zero with h_ev0 | h_punc
  · exact (hdne h_ev0).elim
  · -- Extract an open punctured nbhd on which `deriv F z ≠ 0`.
    rw [eventually_nhdsWithin_iff] at h_punc
    rcases (mem_nhds_iff.mp h_punc) with ⟨U, hU_sub, hU_open, hU_mem⟩
    refine ⟨U, hU_open, hU_mem, ?_⟩
    rintro z ⟨hzU, hz0⟩
    -- `hz0 : deriv F z = 0`. The punctured nbhd condition says `z ≠ z₀`
    -- ⇒ `deriv F z ≠ 0`. Contrapose: `deriv F z = 0` ⇒ `z = z₀`.
    by_contra hne_z
    have : deriv F z ≠ 0 := hU_sub hzU hne_z
    exact this hz0

/-! ## Manifold-side wrapper

The next constructor takes a `CriticalChartBridgeBundle f x` whose
`F'` is morally `deriv F` for the chart pullback `F`, and the
"chart pullback not eventually constant" hypothesis, and recycles the
existing `criticalChartPullbackData_of_bridge` constructor to produce
the `CriticalChartPullbackData` witness.

Why this is useful: the bottleneck in the existing `CriticalSetWitnessSupplier`
is supplying the bundle's `hF'ne` field — "the chart-pullback
*derivative* is not eventually zero". The planar lemma
`AnalyticAt.deriv_not_eventually_zero_of_not_eventually_const` reduces
this to "the chart pullback `F` is not eventually `F z₀`", which is
exactly the manifold-side hypothesis already named (and partially
discharged) in `ChartPullbackNotEventuallyConstDischarge.lean`.

The wrapper below does this reduction, exposing a shape that bundles
the analytic data and consumes the non-eventual-constancy hypothesis. -/

/-- **Bundle constructor from non-eventual-constancy.**

Given the chart pullback `F` analytic at `z₀ := (chartAt ℂ x) x`, an
open neighbourhood `V ⊆ X` of `x` with `V ⊆ (chartAt ℂ x).source`, the
non-eventual-constancy hypothesis on `F` near `z₀`, and the pointwise
compatibility of `criticalSet f` with `(deriv F) (chart x') = 0` on `V`,
build the `CriticalChartBridgeBundle` whose `F'` is `deriv F`. -/
structure DerivBridgeData
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : Jacobians.Discharge.MeromorphicNonzero X) (x : X) where
  /-- Open neighbourhood of `x`, contained in the source-chart. -/
  V : Set X
  hV_open : IsOpen V
  hxV : x ∈ V
  hV_subS : V ⊆ (chartAt ℂ x).source
  /-- The chart pullback. -/
  F : ℂ → ℂ
  /-- `F` is analytic at the chart image of `x`. -/
  hFA : AnalyticAt ℂ F ((chartAt ℂ x) x)
  /-- The non-eventual-constancy hypothesis from
  `ChartPullbackNotEventuallyConstHypothesis`. -/
  hFne : ¬ ∀ᶠ z in 𝓝 ((chartAt ℂ x) x), F z = F ((chartAt ℂ x) x)
  /-- Compatibility: criticality at `x'` ↔ `deriv F` vanishes at chart `x'`. -/
  hCompat :
    ∀ x' ∈ V, (x' ∈ f.criticalSet) ↔ deriv F ((chartAt ℂ x) x') = 0

/-- **Build a `CriticalChartBridgeBundle` from `DerivBridgeData`.**

The bundle's `F'` is set to `deriv F`. The "not eventually zero" field
`hF'ne` comes from the planar lemma
`AnalyticAt.deriv_not_eventually_zero_of_not_eventually_const`. -/
noncomputable def criticalChartBridgeBundle_of_derivBridge
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {f : Jacobians.Discharge.MeromorphicNonzero X} {x : X}
    (D : DerivBridgeData f x) :
    Jacobians.Discharge.MeromorphicNonzero.CriticalChartBridgeBundle f x where
  V := D.V
  hV_open := D.hV_open
  hxV := D.hxV
  hV_subS := D.hV_subS
  F' := deriv D.F
  hF'A := D.hFA.deriv
  hF'ne :=
    deriv_not_eventually_zero_of_analyticAt_not_eventually_const D.hFA D.hFne
  hCompat := D.hCompat

/-- **Chart-pullback data from `DerivBridgeData`.** Composes the bundle
constructor with `criticalChartPullbackData_of_bridge`. -/
noncomputable def criticalChartPullbackData_of_derivBridge
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {f : Jacobians.Discharge.MeromorphicNonzero X} {x : X}
    (D : DerivBridgeData f x) :
    Jacobians.Discharge.ContMDiff.Owed.degree.CriticalChartPullbackData
      f.toRiemannSphere f.criticalSet x :=
  Jacobians.Discharge.MeromorphicNonzero.criticalChartPullbackData_of_bridge f
    (criticalChartBridgeBundle_of_derivBridge D)

/-- **Globalised: `CriticalSetWitness` from per-point `DerivBridgeData`
and closedness.** -/
noncomputable def criticalSetWitness_of_derivBridge
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    {f : Jacobians.Discharge.MeromorphicNonzero X}
    (h_closed : IsClosed f.criticalSet)
    (h : ∀ x ∈ f.criticalSet, DerivBridgeData f x) :
    Jacobians.Discharge.MeromorphicNonzero.CriticalSetWitness f :=
  Jacobians.Discharge.MeromorphicNonzero.criticalSetWitness_of_bridge f h_closed
    (fun x hx => criticalChartBridgeBundle_of_derivBridge (h x hx))

/-- **Headline (conditional on `DerivBridgeData` per critical point and
`IsClosed criticalSet`).** Critical set is finite. -/
theorem criticalSet_finite_of_derivBridge
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : Jacobians.Discharge.MeromorphicNonzero X)
    (h_closed : IsClosed f.criticalSet)
    (h : ∀ x ∈ f.criticalSet, DerivBridgeData f x) :
    f.criticalSet.Finite :=
  Jacobians.Discharge.MeromorphicNonzero.criticalSet_finite_of_witness f
    (criticalSetWitness_of_derivBridge h_closed h)

/-- **Headline (corollary): critical values finite.** -/
theorem criticalValues_finite_of_derivBridge
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : Jacobians.Discharge.MeromorphicNonzero X)
    (h_closed : IsClosed f.criticalSet)
    (h : ∀ x ∈ f.criticalSet, DerivBridgeData f x) :
    f.criticalValues.Finite :=
  Jacobians.Discharge.MeromorphicNonzero.criticalValues_finite_of_criticalSet_finite f
    (criticalSet_finite_of_derivBridge f h_closed h)

end Manifold

end Jacobians.Discharge

end

end
