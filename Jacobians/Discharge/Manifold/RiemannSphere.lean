/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.HasGroupoid
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

set_option autoImplicit true


/-! # The Riemann sphere — carrier, topology, and two-chart atlas

This file declares the **Riemann sphere** as the type abbreviation
`RiemannSphere := OnePoint ℂ`, records the inherited compactness/Hausdorff/
connectedness instances, and constructs an explicit two-chart atlas on it
giving a `ChartedSpace ℂ RiemannSphere` instance.

## What ships

* `Jacobians.Discharge.RiemannSphere` — type abbreviation for `OnePoint ℂ`,
  carrying the one-point compactification topology.
* Inherited `CompactSpace`, `T2Space`, `ConnectedSpace` instances, recorded
  as `example` declarations so the file fails fast if mathlib's `OnePoint`
  API ever drops them.
* `RiemannSphere.chartN : OpenPartialHomeomorph RiemannSphere ℂ` — the
  "north" chart `(some z) ↦ z`, defined on the open set `{x ≠ ∞}`.
  Built as `(IsOpenEmbedding.toOpenPartialHomeomorph ...).symm` so its
  source equals `Set.range (↑) = {∞}ᶜ` (via `OnePoint.compl_infty`) and
  its target equals `Set.univ`.
* `RiemannSphere.chartS : OpenPartialHomeomorph RiemannSphere ℂ` — the
  "south" chart sending `(some z) ↦ z⁻¹` for `z ≠ 0` and `∞ ↦ 0`, defined
  on the open set `{some 0}ᶜ` (open because `{some 0}` is closed in the T₁
  space `OnePoint ℂ`). Built directly via
  `OpenPartialHomeomorph.ofContinuousOpen` from a hand-written
  `PartialEquiv` whose left/right inverse equations are checked by an
  explicit `OnePoint.rec` case split.
* `instance : ChartedSpace ℂ RiemannSphere` — the two-chart atlas
  `{chartN, chartS}`, with `chartAt x = chartN` if `x ≠ ∞` and `chartS`
  otherwise. Decidability of `x = ∞` comes from the underlying
  `Option`/`OnePoint` decidable instance (Lean's `decEq` on `Option`
  delegates the first slot — `∞ = none` — without needing
  `DecidableEq ℂ`).

* `instance : IsManifold 𝓘(ℂ) ω RiemannSphere` — the analytic manifold
  structure. Proved via `isManifold_of_contDiffOn`, with a four-way case
  analysis on the atlas:
  - the diagonal cases `chartN.symm ≫ₕ chartN` and `chartS.symm ≫ₕ chartS`
    are handled uniformly by `symm_trans_mem_contDiffGroupoid`;
  - the off-diagonal cases `chartN.symm ≫ₕ chartS` and
    `chartS.symm ≫ₕ chartN` both reduce on their source `{z : ℂ | z ≠ 0}`
    to the analytic map `z ↦ z⁻¹`, via `analyticOnNhd_inv` from
    `Mathlib/Analysis/Analytic/Constructions.lean`. The model with corners
    is `modelWithCornersSelf ℂ ℂ`, so the conjugation `I ∘ · ∘ I.symm`
    collapses through `modelWithCornersSelf_coe[_symm]` and
    `ModelWithCorners.range_eq_univ`, leaving a pure analyticity check on
    `{z | z ≠ 0}`. The `ContDiffOn ℂ ω` upgrade uses
    `AnalyticOnNhd.contDiffOn_of_completeSpace` (since `ℂ` is complete). -/

open OnePoint Set Topology

open scoped Manifold

namespace Jacobians.Discharge

/-- The **Riemann sphere**: the one-point compactification of `ℂ`. As a type,
this is `Option ℂ` with the compactification topology making it compact,
Hausdorff, and connected. -/
abbrev RiemannSphere : Type := OnePoint ℂ

namespace RiemannSphere

/-- Compactness of the Riemann sphere — inherited from
`OnePoint.instCompactSpace`. -/
example : CompactSpace RiemannSphere := inferInstance

/-- Hausdorff property — inherited from `OnePoint`'s `T2Space` instance,
which applies because `ℂ` is weakly locally compact and Hausdorff. -/
example : T2Space RiemannSphere := inferInstance

/-- Connectedness — inherited because `ℂ` is preconnected and noncompact. -/
example : ConnectedSpace RiemannSphere := inferInstance

/-! ### The "north" chart `chartN`

This is the chart that "removes ∞" — it sends `(some z) ↦ z` and is defined
on the open complement of `{∞}`. We build it as the symmetric of the open
embedding `(↑) : ℂ → OnePoint ℂ`.

Concretely:

* source = `Set.range ((↑) : ℂ → OnePoint ℂ) = {∞}ᶜ` (via `compl_infty`)
* target = `Set.univ`
* `chartN (some z) = z`, `chartN.symm z = some z`. -/

/-- The "north" chart on the Riemann sphere: `(some z) ↦ z` on `{x ≠ ∞}`. -/
noncomputable def chartN : OpenPartialHomeomorph RiemannSphere ℂ :=
  (IsOpenEmbedding.toOpenPartialHomeomorph
      ((↑) : ℂ → OnePoint ℂ) OnePoint.isOpenEmbedding_coe).symm

@[simp] lemma chartN_source : chartN.source = {x : RiemannSphere | x ≠ ∞} := by
  -- `chartN.source = (toOpenPartialHomeomorph coe).target = range coe`,
  -- and `range coe = {∞}ᶜ = {x | x ≠ ∞}` via `compl_infty`.
  unfold chartN
  rw [OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target]
  ext x
  simp [← OnePoint.compl_infty, Set.mem_compl_iff, Set.mem_singleton_iff]

@[simp] lemma chartN_target : chartN.target = (Set.univ : Set ℂ) := by
  unfold chartN
  rw [OpenPartialHomeomorph.symm_target,
      IsOpenEmbedding.toOpenPartialHomeomorph_source]

/-! ### The "south" chart `chartS`

This chart "removes `0`" — it sends `(some z) ↦ z⁻¹` (for `z ≠ 0`) and
`∞ ↦ 0`, defined on the open complement of `{some 0}`. The complement is
open because `{some 0}` is a single coercion-image point, closed in the T₂
(hence T₁) space `OnePoint ℂ`.

We build it directly via `OpenPartialHomeomorph.ofContinuousOpen` from a
hand-written `PartialEquiv`. -/

/-- The underlying set function of `chartS`: `(some z) ↦ z⁻¹`, `∞ ↦ 0`. -/
noncomputable def chartSToFun : RiemannSphere → ℂ :=
  fun x => OnePoint.rec 0 (fun z => z⁻¹) x

/-- The set function inverse for `chartS`: `0 ↦ ∞`, `z ≠ 0 ↦ some z⁻¹`.
On `ℂ` we use `if z = 0 then ∞ else (some z⁻¹)`; since equality with `0` in
`ℂ` is decidable propositionally we use `Classical.dec` here. -/
noncomputable def chartSInvFun : ℂ → RiemannSphere :=
  fun z => if z = 0 then (∞ : RiemannSphere) else ((z⁻¹ : ℂ) : RiemannSphere)

@[simp] lemma chartSToFun_infty : chartSToFun ∞ = 0 := rfl

@[simp] lemma chartSToFun_coe (z : ℂ) : chartSToFun ((z : RiemannSphere)) = z⁻¹ := rfl

@[simp] lemma chartSInvFun_zero : chartSInvFun 0 = (∞ : RiemannSphere) := by
  simp [chartSInvFun]

lemma chartSInvFun_of_ne {z : ℂ} (hz : z ≠ 0) :
    chartSInvFun z = ((z⁻¹ : ℂ) : RiemannSphere) := by
  simp [chartSInvFun, hz]

/-- The underlying `PartialEquiv` of `chartS`. Source = `{some 0}ᶜ`,
target = `Set.univ`. -/
noncomputable def chartSPartialEquiv : PartialEquiv RiemannSphere ℂ where
  toFun := chartSToFun
  invFun := chartSInvFun
  source := {x : RiemannSphere | x ≠ ((0 : ℂ) : RiemannSphere)}
  target := Set.univ
  map_source' := by intro _ _; trivial
  map_target' := by
    intro z _
    show chartSInvFun z ≠ ((0 : ℂ) : RiemannSphere)
    by_cases hz : z = 0
    · subst hz
      rw [chartSInvFun_zero]
      exact OnePoint.infty_ne_coe (0 : ℂ)
    · rw [chartSInvFun_of_ne hz]
      have hzinv : z⁻¹ ≠ 0 := inv_ne_zero hz
      intro h
      exact hzinv (OnePoint.coe_injective h)
  left_inv' := by
    intro x hx
    -- `x ≠ some 0`. Cases on `x : OnePoint ℂ`.
    rcases x with _ | z
    · -- x = ∞: chartSToFun ∞ = 0; chartSInvFun 0 = ∞.
      show chartSInvFun (chartSToFun ∞) = ∞
      rw [chartSToFun_infty, chartSInvFun_zero]
    · -- x = some z. Membership says `some z ≠ some 0`, hence `z ≠ 0`.
      have hz : z ≠ 0 := by
        intro h
        apply hx
        show ((z : ℂ) : RiemannSphere) = ((0 : ℂ) : RiemannSphere)
        rw [h]
      have hzinv : z⁻¹ ≠ 0 := inv_ne_zero hz
      show chartSInvFun (chartSToFun ((z : RiemannSphere))) = (z : RiemannSphere)
      rw [chartSToFun_coe, chartSInvFun_of_ne hzinv, inv_inv]
  right_inv' := by
    intro z _
    by_cases hz : z = 0
    · subst hz
      show chartSToFun (chartSInvFun (0 : ℂ)) = 0
      rw [chartSInvFun_zero, chartSToFun_infty]
    · show chartSToFun (chartSInvFun z) = z
      rw [chartSInvFun_of_ne hz, chartSToFun_coe, inv_inv]

/-- Continuity of `chartSInvFun : ℂ → RiemannSphere`. The map is `0 ↦ ∞` and
`z ≠ 0 ↦ some z⁻¹`. We check continuity at every point: at `0` we use
`OnePoint.tendsto_nhds_infty` (closed-compact ball complement maps into a
neighborhood of `∞`); at `z ≠ 0` the map locally agrees with `(↑) ∘ (·⁻¹)`. -/
lemma continuous_chartSInvFun : Continuous chartSInvFun := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · -- ContinuousAt at 0, where chartSInvFun 0 = ∞.
    subst hz
    have h0 : chartSInvFun (0 : ℂ) = (∞ : RiemannSphere) := chartSInvFun_zero
    rw [ContinuousAt, h0, OnePoint.nhds_infty_eq]
    -- We must show `Tendsto chartSInvFun (𝓝 0) (map ↑ (coclosedCompact ℂ) ⊔ pure ∞)`.
    -- Strategy: show `Tendsto chartSInvFun (𝓝[≠] 0) (map ↑ (coclosedCompact ℂ))` and
    -- `Tendsto chartSInvFun (pure 0) (pure ∞)`, then combine.
    rw [show (𝓝 (0 : ℂ)) = 𝓝[≠] (0 : ℂ) ⊔ pure 0 from
      (nhdsNE_sup_pure (0 : ℂ)).symm]
    rw [Filter.tendsto_sup]
    refine ⟨?_, ?_⟩
    · -- On `𝓝[≠] 0`, chartSInvFun w = ↑ w⁻¹. We aim into the left summand
      -- `map ↑ (coclosedCompact ℂ)`.
      apply Filter.Tendsto.mono_right _ le_sup_left
      have hcongr : (fun w : ℂ => ((w⁻¹ : ℂ) : RiemannSphere))
          =ᶠ[𝓝[≠] (0 : ℂ)] chartSInvFun := by
        refine Filter.eventually_of_mem
          (self_mem_nhdsWithin (a := (0 : ℂ)) (s := {(0 : ℂ)}ᶜ)) ?_
        intro w hw
        exact (chartSInvFun_of_ne hw).symm
      refine Filter.Tendsto.congr' hcongr ?_
      -- Tendsto Inv.inv (𝓝[≠] 0) (cobounded ℂ) = (cocompact ℂ) ≤ coclosedCompact ℂ.
      have hinv : Filter.Tendsto (fun w : ℂ => w⁻¹) (𝓝[≠] (0 : ℂ))
          (Filter.coclosedCompact ℂ) := by
        refine (Filter.tendsto_inv₀_nhdsNE_zero (α := ℂ)).mono_right ?_
        rw [Metric.cobounded_eq_cocompact]
        exact Filter.cocompact_le_coclosedCompact
      -- Push forward through `(↑) : ℂ → RiemannSphere`.
      have hcoe : Filter.Tendsto ((↑) : ℂ → RiemannSphere)
          (Filter.coclosedCompact ℂ) (Filter.map (↑) (Filter.coclosedCompact ℂ)) :=
        Filter.tendsto_map
      exact hcoe.comp hinv
    · -- pure 0 ↦ pure ∞ ≤ map ↑ (coclosedCompact ℂ) ⊔ pure ∞.
      have h := Filter.tendsto_pure_pure chartSInvFun 0
      rw [chartSInvFun_zero] at h
      exact h.mono_right le_sup_right
  · -- ContinuousAt at z ≠ 0.
    have hloc : (chartSInvFun : ℂ → RiemannSphere)
        =ᶠ[𝓝 z] (fun w => ((w⁻¹ : ℂ) : RiemannSphere)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hz] with w hw
      exact chartSInvFun_of_ne hw
    rw [ContinuousAt]
    have hzval : chartSInvFun z = ((z⁻¹ : ℂ) : RiemannSphere) := chartSInvFun_of_ne hz
    rw [hzval]
    refine Filter.Tendsto.congr' (hloc.symm) ?_
    -- `(↑) ∘ (·⁻¹)` is continuous at z (since z ≠ 0).
    exact (OnePoint.continuous_coe.continuousAt).comp (continuousAt_inv₀ hz)

/-- The "south" chart on the Riemann sphere: `(some z) ↦ z⁻¹`, `∞ ↦ 0`,
on `{x ≠ some 0}`. We construct it directly via the
`OpenPartialHomeomorph` structure: forward continuity on the source is
proved point-wise; inverse continuity holds on all of `ℂ`
(`continuous_chartSInvFun`); both `source` and `target = Set.univ` are open. -/
noncomputable def chartS : OpenPartialHomeomorph RiemannSphere ℂ where
  toPartialEquiv := chartSPartialEquiv
  open_source := by
    -- `{x | x ≠ some 0}` is the complement of the closed point `{some 0}`.
    show IsOpen ({x : RiemannSphere | x ≠ ((0 : ℂ) : RiemannSphere)})
    rw [show ({x : RiemannSphere | x ≠ ((0 : ℂ) : RiemannSphere)} : Set RiemannSphere)
          = ({((0 : ℂ) : RiemannSphere)} : Set RiemannSphere)ᶜ from rfl]
    exact isClosed_singleton.isOpen_compl
  open_target := isOpen_univ
  continuousOn_toFun := by
    -- continuity of `chartSToFun` on `{x ≠ some 0}`
    apply continuousOn_of_forall_continuousAt
    intro x hx
    induction x using OnePoint.rec with
    | infty =>
      -- ContinuousAt at ∞.
      rw [OnePoint.continuousAt_infty]
      intro s hs
      -- `chartSToFun ∞ = 0` reduces by rfl, so `hs : s ∈ 𝓝 0`.
      rcases Metric.mem_nhds_iff.mp hs with ⟨r, hr_pos, hball⟩
      refine ⟨Metric.closedBall (0 : ℂ) r⁻¹, Metric.isClosed_closedBall,
              isCompact_closedBall 0 r⁻¹, ?_⟩
      intro z hz
      -- hz : z ∈ (closedBall 0 r⁻¹)ᶜ, i.e., r⁻¹ < ‖z‖.
      have hz' : r⁻¹ < ‖z‖ := by
        rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
        exact hz
      have hz_ne : z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz'
        exact absurd hz' (not_lt.mpr (by positivity))
      -- Goal: `(chartSToFun ∘ ↑) z ∈ s`, which reduces to `z⁻¹ ∈ s`.
      apply hball
      -- The goal after `apply hball` is `dist (chartSPartialEquiv ↑z)
      -- (chartSPartialEquiv ∞) < r`. The two chart applications reduce
      -- definitionally: `chartSPartialEquiv (some z) = z⁻¹` and
      -- `chartSPartialEquiv ∞ = 0`. Restate the goal explicitly so that
      -- `dist_zero_right` and `norm_inv` then take it to `‖z‖⁻¹ < r`.
      show dist (z⁻¹ : ℂ) (0 : ℂ) < r
      rw [dist_zero_right, norm_inv]
      -- Goal: `‖z‖⁻¹ < r`. Have `hz' : r⁻¹ < ‖z‖`, both sides positive.
      -- Use the one-over decreasing-monotonicity: `0 < a → a < b → 1/b < 1/a`.
      have h := one_div_lt_one_div_of_lt (inv_pos.mpr hr_pos) hz'
      -- `h : 1/‖z‖ < 1/r⁻¹`. Normalise: `1/x = x⁻¹` and `(r⁻¹)⁻¹ = r`.
      simpa [one_div, inv_inv] using h
    | coe z =>
      -- ContinuousAt at `(some z)` with `some z ≠ some 0`, hence `z ≠ 0`.
      have hz : z ≠ 0 := by
        intro h
        apply hx
        show ((z : ℂ) : RiemannSphere) = ((0 : ℂ) : RiemannSphere)
        rw [h]
      rw [OnePoint.continuousAt_coe]
      -- `chartSToFun ∘ (↑)` reduces to `Inv.inv` definitionally.
      exact continuousAt_inv₀ hz
  continuousOn_invFun := continuous_chartSInvFun.continuousOn

@[simp] lemma chartS_source :
    chartS.source = {x : RiemannSphere | x ≠ ((0 : ℂ) : RiemannSphere)} := rfl

@[simp] lemma chartS_target : chartS.target = (Set.univ : Set ℂ) := rfl

lemma chartS_apply_coe (z : ℂ) :
    chartS ((z : RiemannSphere)) = z⁻¹ := rfl

lemma chartS_apply_infty : chartS (∞ : RiemannSphere) = 0 := rfl

lemma chartS_symm_apply_zero : chartS.symm (0 : ℂ) = (∞ : RiemannSphere) :=
  chartSInvFun_zero

lemma chartS_symm_apply_of_ne {z : ℂ} (hz : z ≠ 0) :
    chartS.symm z = ((z⁻¹ : ℂ) : RiemannSphere) :=
  chartSInvFun_of_ne hz

lemma chartN_apply_coe (z : ℂ) :
    chartN ((z : RiemannSphere)) = z := by
  -- `chartN := (IsOpenEmbedding.toOpenPartialHomeomorph (↑) h).symm`, so the
  -- forward action `chartN (some z)` is recovered by the embedding's
  -- `toOpenPartialHomeomorph_left_inv`.
  unfold chartN
  exact OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph_left_inv
    ((↑) : ℂ → OnePoint ℂ)

lemma chartN_symm_apply (z : ℂ) :
    chartN.symm z = ((z : ℂ) : RiemannSphere) := by
  unfold chartN
  rfl

/-! ### The two-chart atlas

We give `RiemannSphere` a `ChartedSpace ℂ` instance with atlas `{chartN, chartS}`.
For a point `x : RiemannSphere`, we choose `chartN` if `x ≠ ∞` (so `x` lies in
`chartN.source`) and `chartS` if `x = ∞` (so `x` lies in `chartS.source`,
since `∞ ≠ some 0`). The choice is implemented via `OnePoint.rec` to avoid
needing `DecidableEq ℂ`. -/

/-- The chart selector: `chartN` for finite points, `chartS` for `∞`. -/
noncomputable def chartAt' : RiemannSphere → OpenPartialHomeomorph RiemannSphere ℂ :=
  fun x => OnePoint.rec chartS (fun _ => chartN) x

@[simp] lemma chartAt'_infty : chartAt' (∞ : RiemannSphere) = chartS := rfl

@[simp] lemma chartAt'_coe (z : ℂ) : chartAt' ((z : RiemannSphere)) = chartN := rfl

noncomputable instance : ChartedSpace ℂ RiemannSphere where
  atlas := {chartN, chartS}
  chartAt := chartAt'
  mem_chart_source := by
    intro x
    induction x using OnePoint.rec with
    | infty =>
      rw [chartAt'_infty]
      show (∞ : RiemannSphere) ≠ ((0 : ℂ) : RiemannSphere)
      exact OnePoint.infty_ne_coe (0 : ℂ)
    | coe z =>
      rw [chartAt'_coe]
      rw [chartN_source]
      exact OnePoint.coe_ne_infty z
  chart_mem_atlas := by
    intro x
    induction x using OnePoint.rec with
    | infty =>
      rw [chartAt'_infty]
      exact Set.mem_insert_of_mem _ rfl
    | coe z =>
      rw [chartAt'_coe]
      exact Set.mem_insert _ _

/-! ### Analytic chart transitions

The four chart transitions are:

* `chartN.symm ≫ₕ chartN` and `chartS.symm ≫ₕ chartS` — handled uniformly by
  `symm_trans_mem_contDiffGroupoid`, which says `e.symm ≫ₕ e ∈ contDiffGroupoid n I`
  for any open partial homeomorphism `e`.
* `chartN.symm ≫ₕ chartS` and `chartS.symm ≫ₕ chartN` — both reduce to the map
  `z ↦ z⁻¹` on `{z : ℂ | z ≠ 0}`, which is analytic via `analyticOnNhd_inv`.

For the off-diagonal cases we work directly with `mem_groupoid_of_pregroupoid`.
The model with corners is `𝓘(ℂ) = modelWithCornersSelf ℂ ℂ`, so the simp lemmas
`modelWithCornersSelf_coe` and `modelWithCornersSelf_coe_symm` collapse the
`I ∘ · ∘ I.symm` conjugation. -/

/-- `chartN.symm ≫ₕ chartS` has source `{z : ℂ | z ≠ 0}`. -/
lemma chartN_symm_trans_chartS_source :
    (chartN.symm.trans chartS).source = {z : ℂ | z ≠ 0} := by
  rw [OpenPartialHomeomorph.trans_source]
  ext z
  constructor
  · rintro ⟨_, hz⟩
    -- hz : chartN.symm z ∈ chartS.source = {x | x ≠ some 0}
    rw [Set.mem_preimage] at hz
    rw [chartN_symm_apply] at hz
    -- hz : ((z : ℂ) : RiemannSphere) ≠ ((0 : ℂ) : RiemannSphere)
    intro hz0
    apply hz
    rw [hz0]
  · intro hz
    refine ⟨?_, ?_⟩
    · -- chartN.symm.source = univ
      change z ∈ (chartN.symm.source : Set ℂ)
      rw [OpenPartialHomeomorph.symm_source, chartN_target]
      trivial
    · rw [Set.mem_preimage, chartN_symm_apply]
      change ((z : ℂ) : RiemannSphere) ≠ ((0 : ℂ) : RiemannSphere)
      intro h
      exact hz (OnePoint.coe_injective h)

/-- `chartS.symm ≫ₕ chartN` has source `{z : ℂ | z ≠ 0}`. -/
lemma chartS_symm_trans_chartN_source :
    (chartS.symm.trans chartN).source = {z : ℂ | z ≠ 0} := by
  rw [OpenPartialHomeomorph.trans_source]
  ext z
  constructor
  · rintro ⟨_, hz⟩
    rw [Set.mem_preimage] at hz
    -- hz : chartS.symm z ∈ chartN.source = {x | x ≠ ∞}
    rw [chartN_source] at hz
    intro hz0
    subst hz0
    rw [chartS_symm_apply_zero] at hz
    exact hz rfl
  · intro hz
    refine ⟨?_, ?_⟩
    · change z ∈ (chartS.symm.source : Set ℂ)
      rw [OpenPartialHomeomorph.symm_source, chartS_target]
      trivial
    · rw [Set.mem_preimage, chartS_symm_apply_of_ne hz, chartN_source]
      exact OnePoint.coe_ne_infty _

/-- `chartN.symm ≫ₕ chartS` agrees with `z ↦ z⁻¹` on its source `{z | z ≠ 0}`. -/
lemma chartN_symm_trans_chartS_eqOn :
    Set.EqOn (chartN.symm.trans chartS) (fun z : ℂ => z⁻¹)
      (chartN.symm.trans chartS).source := by
  intro z hz
  rw [chartN_symm_trans_chartS_source] at hz
  rw [OpenPartialHomeomorph.trans_apply, chartN_symm_apply, chartS_apply_coe]

/-- `chartS.symm ≫ₕ chartN` agrees with `z ↦ z⁻¹` on its source `{z | z ≠ 0}`. -/
lemma chartS_symm_trans_chartN_eqOn :
    Set.EqOn (chartS.symm.trans chartN) (fun z : ℂ => z⁻¹)
      (chartS.symm.trans chartN).source := by
  intro z hz
  rw [chartS_symm_trans_chartN_source] at hz
  rw [OpenPartialHomeomorph.trans_apply, chartS_symm_apply_of_ne hz, chartN_apply_coe]

/-- The transition `chartN.symm ≫ₕ chartS` is `C^ω` (analytic) when read through
the identity model `𝓘(ℂ) = modelWithCornersSelf ℂ ℂ`. -/
lemma contDiffOn_chartN_symm_trans_chartS :
    ContDiffOn ℂ ω (𝓘(ℂ) ∘ (chartN.symm.trans chartS) ∘ 𝓘(ℂ).symm)
      (𝓘(ℂ).symm ⁻¹' (chartN.symm.trans chartS).source ∩ Set.range 𝓘(ℂ)) := by
  -- The model is the identity; its `coe` and `symm` are `id`, `range id = univ`.
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ]
  -- It suffices to show the transition is analytic on its source.
  refine ContDiffOn.congr ?_ chartN_symm_trans_chartS_eqOn
  rw [chartN_symm_trans_chartS_source]
  exact analyticOnNhd_inv.contDiffOn_of_completeSpace

/-- The transition `chartS.symm ≫ₕ chartN` is `C^ω` (analytic) when read through
the identity model. -/
lemma contDiffOn_chartS_symm_trans_chartN :
    ContDiffOn ℂ ω (𝓘(ℂ) ∘ (chartS.symm.trans chartN) ∘ 𝓘(ℂ).symm)
      (𝓘(ℂ).symm ⁻¹' (chartS.symm.trans chartN).source ∩ Set.range 𝓘(ℂ)) := by
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ]
  refine ContDiffOn.congr ?_ chartS_symm_trans_chartN_eqOn
  rw [chartS_symm_trans_chartN_source]
  exact analyticOnNhd_inv.contDiffOn_of_completeSpace

/-- The Riemann sphere is a complex analytic manifold modelled on `ℂ`. -/
instance : IsManifold 𝓘(ℂ) ω RiemannSphere :=
  isManifold_of_contDiffOn _ _ _ <| by
    intro e e' he he'
    -- atlas = {chartN, chartS}; do four cases.
    rcases he with rfl | he
    · rcases he' with rfl | he'
      · -- chartN.symm ≫ₕ chartN
        have : chartN.symm.trans chartN ∈ contDiffGroupoid ω 𝓘(ℂ) :=
          symm_trans_mem_contDiffGroupoid chartN
        exact this.1
      · rw [Set.mem_singleton_iff] at he'; subst he'
        -- chartN.symm ≫ₕ chartS
        exact contDiffOn_chartN_symm_trans_chartS
    · rw [Set.mem_singleton_iff] at he; subst he
      rcases he' with rfl | he'
      · -- chartS.symm ≫ₕ chartN
        exact contDiffOn_chartS_symm_trans_chartN
      · rw [Set.mem_singleton_iff] at he'; subst he'
        -- chartS.symm ≫ₕ chartS
        have : chartS.symm.trans chartS ∈ contDiffGroupoid ω 𝓘(ℂ) :=
          symm_trans_mem_contDiffGroupoid chartS
        exact this.1

end RiemannSphere

/-! ### Homeomorphism with the unit 2-sphere in `ℝ³`

Mathlib provides
`onePointEquivSphereOfFinrankEq : OnePoint V ≃ₜ sphere (0 : EuclideanSpace ℝ ι) 1`
for any finite-dimensional real topological vector space `V` together with a
finite index type `ι` whose cardinality matches `finrank ℝ V + 1`.

For `V = ℂ` (real-rank `2`) and `ι = Fin 3` we get
`OnePoint ℂ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`.
This is the topological half of the genus-zero ↔ Riemann-sphere bridge
(challenge item 14, `genus_eq_zero_iff_homeo`). All the typeclass
prerequisites on `ℂ` (`AddCommGroup`, `Module ℝ`, `FiniteDimensional ℝ`,
`IsTopologicalAddGroup`, `ContinuousSMul ℝ`, `T2Space`) are inferred from
its normed-field structure; `finrank ℝ ℂ = 2` is `Complex.finrank_real_complex`
in `Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean`. -/

/-- The Riemann sphere is homeomorphic to the unit `2`-sphere in `ℝ³`,
viewed as `Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`. -/
noncomputable def RiemannSphere.toSphereHomeo :
    RiemannSphere ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by
    -- `finrank ℝ ℂ + 1 = 3 = Fintype.card (Fin 3)`.
    rw [Complex.finrank_real_complex, Fintype.card_fin])

end Jacobians.Discharge
