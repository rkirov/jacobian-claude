/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.Discharge.Manifold.RamificationIndex
import Jacobians.Discharge.Manifold.ContMDiffOmegaAnalytic
import Jacobians.Discharge.Manifold.PerChartNonConstancyReduction
import Mathlib.Analysis.Analytic.Order

set_option autoImplicit true


/-! # `manifoldRamificationIndex ≥ 1` at fibre points of non-constant `f`

For a `ContMDiff` non-constant map `f : X → Y` between compact connected
complex 1-manifolds and a fibre point `x : X` of `y : Y` (i.e., `f x = y`),
the chart-pullback `F = (chartAt ℂ y) ∘ f ∘ (chartAt ℂ x).symm` is
analytic at `(chartAt ℂ x) x` and not eventually equal to its value
there (otherwise `f` would be locally constant at `x`, hence globally
constant by the identity theorem on the connected manifold). Therefore
`analyticOrderAt (F - F z₀) z₀` is a finite natural number `≥ 1`, and so
`manifoldRamificationIndex f x ≥ 1`.

This is obligation **(A')** of the Riemann-Hurwitz total-weight proof
(see `HANDOFF_2026_05_08.md`): the manifold-side statement that the
ramification index is at least one at every fibre point. The actual
**(A)** is the k-fold lift, but it requires this positivity as input.

No `sorry`, no `axiom`. -/

@[expose] public section

open Set Filter Topology
open scoped Manifold Topology ContDiff

namespace Jacobians.Discharge

namespace Manifold

universe u v

/-- **Positivity of the ramification index at fibre points of a
non-constant map.** -/
theorem manifoldRamificationIndex_pos_at_fibre_of_perChartNonConstancy
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y]
    [ConnectedSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (H : Jacobians.Discharge.ContMDiff.Owed.degree.PerChartNonConstancyHypothesis X Y)
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnc : ¬ Jacobians.Discharge.IsConstantMap f)
    {x : X} {y : Y} (hxy : f x = y) :
    1 ≤ manifoldRamificationIndex f x := by
  -- The chart-pullback `F = (chartAt ℂ y) ∘ f ∘ (chartAt ℂ x).symm` at
  -- `z₀ = (chartAt ℂ x) x`. By non-constancy, F is not eventually equal
  -- to F z₀ at z₀, hence `analyticOrderAt (F - F z₀) z₀ < ⊤`, so its
  -- `.toNat` is at least 1 (orders 0 are excluded because F z₀ - F z₀ = 0).
  -- Set up F (using `f x` as the codomain chart base, which equals y).
  set z₀ : ℂ := (chartAt ℂ x) x with hz₀
  set F : ℂ → ℂ := (chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm with hF
  -- F is analytic at z₀.
  have hFA : AnalyticAt ℂ F z₀ :=
    Jacobians.Discharge.ContMDiff.Owed.degree.contMDiff_omega_analyticAt_chart_pullback hf x
  -- F z₀ = (chartAt ℂ (f x)) (f x). The (F z) - F z₀ shift vanishes at z₀.
  -- For analyticOrderAt of an analytic function at its zero:
  --   it equals ⊤ iff the function is eventually 0 in 𝓝 z₀
  --   it equals 0 iff the function is non-zero at z₀
  --   it equals (k : ℕ∞) for k ≥ 1 iff vanishes to order k.
  have hF_z₀ : (fun z => F z - F z₀) z₀ = 0 := by simp
  -- By non-constancy, `(F z - F z₀)` is NOT eventually 0 in 𝓝 z₀.
  have h_not_eventually_zero :
      ¬ (∀ᶠ z in 𝓝 z₀, F z - F z₀ = 0) := by
    -- Apply hypothesis H at the fibre point (x, y, hxy).
    -- H gives: for every V ∈ 𝓝 z₀, ∃ z ∈ V with F z ≠ F z₀.
    -- Hence not eventually F z = F z₀.
    intro hev
    -- hev : ∀ᶠ z, F z - F z₀ = 0, i.e. eventually F z = F z₀.
    -- Apply H at V := { z | F z = F z₀ } (which is in 𝓝 z₀ from hev).
    have hev' : ∀ᶠ z in 𝓝 z₀, F z = F z₀ := by
      exact hev.mono (fun z hz => sub_eq_zero.mp hz)
    -- Get a V ∈ 𝓝 z₀ with F = F z₀ on V.
    obtain ⟨V, hV_nhds, hV_eqOn⟩ := Filter.eventually_iff_exists_mem.mp hev'
    -- H at V gives ∃ z ∈ V with F z ≠ F z₀.
    have hH := H f hf hnc y x hxy V hV_nhds
    obtain ⟨z, hz_V, hz_ne⟩ := hH
    -- Contradiction: F z = F z₀ from hV_eqOn, but F z ≠ F z₀ from hz_ne.
    apply hz_ne
    -- Need to bridge F z₀ vs the form in H. H's conclusion uses
    -- `((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) z ≠ (chartAt ℂ (f x)) (f x)`.
    -- Note F = that composite, and F z₀ = (chartAt ℂ (f x)) (f x) by chart left-inv.
    have hFz₀_eq : F z₀ = (chartAt ℂ (f x)) (f x) := by
      have hx_src : x ∈ (chartAt ℂ x).source := mem_chart_source ℂ x
      have hsymm : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
        (chartAt ℂ x).left_inv hx_src
      show ((chartAt ℂ (f x)) ∘ f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
          = (chartAt ℂ (f x)) (f x)
      simp [Function.comp, hsymm]
    rw [← hFz₀_eq]
    exact hV_eqOn z hz_V
  -- analyticOrderAt is ⊤ iff eventually 0; not eventually 0 ⇒ not ⊤.
  have h_order_ne_top :
      analyticOrderAt (fun z => F z - F z₀) z₀ ≠ ⊤ := by
    intro h_top
    apply h_not_eventually_zero
    -- analyticOrderAt = ⊤ ⇒ eventually 0.
    have := analyticOrderAt_eq_top.mp h_top
    exact this
  -- analyticOrderAt is at least 1 because the function vanishes at z₀
  -- (which forces order ≠ 0).
  have h_order_ne_zero :
      analyticOrderAt (fun z => F z - F z₀) z₀ ≠ 0 := by
    intro h_zero
    -- analyticOrderAt = 0 ⇒ value at z₀ is nonzero (contradicting hF_z₀).
    have hF_an : AnalyticAt ℂ (fun z => F z - F z₀) z₀ :=
      hFA.sub (analyticAt_const)
    have hne : (fun z => F z - F z₀) z₀ ≠ 0 :=
      (hF_an.analyticOrderAt_eq_zero).mp h_zero
    exact hne hF_z₀
  -- Now: analyticOrderAt is some n : ℕ∞ with n ≠ 0 and n ≠ ⊤. So n is a
  -- positive nat. Its toNat is the same positive nat, hence ≥ 1.
  unfold manifoldRamificationIndex
  -- Goal: 1 ≤ (analyticOrderAt (F - F z₀) z₀).toNat
  set ord : ℕ∞ := analyticOrderAt (fun z => F z - F z₀) z₀ with hord_def
  -- ord ≠ 0 ∧ ord ≠ ⊤ ⇒ ord = (n : ℕ∞) for some n ≥ 1, so toNat = n ≥ 1.
  cases hord_eq : ord with
  | top => exact absurd hord_eq h_order_ne_top
  | coe n =>
    cases n with
    | zero =>
      have : ord = 0 := by rw [hord_eq]; rfl
      exact absurd this h_order_ne_zero
    | succ m =>
      show 1 ≤ ord.toNat
      rw [hord_eq]
      show 1 ≤ ((↑(m + 1) : ℕ∞)).toNat
      rw [ENat.toNat_coe]
      omega

end Manifold

end Jacobians.Discharge
