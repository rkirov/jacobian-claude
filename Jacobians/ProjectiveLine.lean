/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Jacobians.Genus

/-!
# The complex Riemann sphere `ℂℙ¹` as a compact complex 1-manifold

We model `ℂℙ¹` as the Alexandroff one-point compactification `OnePoint ℂ = ℂ ∪ {∞}`
(`RiemannSphere`). Mathlib provides the topology and all the point-set instances
(`CompactSpace`, `T2Space`, `ConnectedSpace`) for free, since `ℂ` is a proper —
hence weakly-locally-compact — Hausdorff, preconnected, noncompact space.

On top of that we build, by hand, the structure required by the Jacobians challenge
vocabulary (mirroring `Jacobians.Roadmap`):

* `ChartedSpace ℂ RiemannSphere` from the two standard charts
  `U₀` (the `ℂ`-affine chart, identity on `ℂ`, source `{∞}ᶜ`) and
  `U∞` (the chart at `∞`, the inversion `z ↦ 1/z`, source `{0}ᶜ`);
* `IsManifold 𝓘(ℂ) ω RiemannSphere` — the transition map between the two charts is
  the holomorphic inversion `z ↦ 1/z` on `ℂˣ`;
* a homeomorphism `RiemannSphere ≃ₜ S²` to the Euclidean 2-sphere (via Mathlib's
  `onePointEquivSphereOfFinrankEq`, since `ℂ ≃ ℝ²` has real dimension `2`);
* `genus RiemannSphere = 0` (the space of global holomorphic 1-forms is `⊥`), by
  Liouville: a global holomorphic 1-form pulls back to an entire function on the
  affine chart that extends holomorphically over `∞`, hence is bounded, hence
  constant, and the value at `∞` forces it to vanish.

## References

Forster, *Lectures on Riemann Surfaces*, §1, §5, §10 (`ℂℙ¹`, charts, `Ω(ℂℙ¹) = 0`).
Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. I.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open OnePoint Complex

namespace Jacobians

/-- The **Riemann sphere** `ℂℙ¹`, modelled as the one-point compactification
`OnePoint ℂ = ℂ ∪ {∞}`. -/
abbrev RiemannSphere : Type := OnePoint ℂ

namespace RiemannSphere

/-! ### Milestone 1 — the free point-set instances

All of these are found by `inferInstance` from Mathlib's `OnePoint` development;
we record them explicitly so the manifold vocabulary downstream can rely on them
being present (and to document that the model has them). -/

instance : TopologicalSpace RiemannSphere := inferInstance
instance : CompactSpace RiemannSphere := inferInstance
instance : T2Space RiemannSphere := inferInstance
instance : ConnectedSpace RiemannSphere := inferInstance
instance : Nonempty RiemannSphere := inferInstance

/-! ### Milestone 2a — the inversion homeomorphism `z ↦ z⁻¹`

The chart at `∞` is built from the inversion `z ↦ 1/z`, which we first package as a
self-homeomorphism of `OnePoint ℂ` swapping `0 ↔ ∞`. Continuity is checked via
`OnePoint.continuous_iff`:

* at `∞` (i.e. along `coclosedCompact ℂ = cobounded ℂ`), `z⁻¹ → 0` (`tendsto_inv₀_cobounded`);
* on the affine part, `z ↦ z⁻¹` is continuous away from `0`, and at `0` the value `∞` is the
  limit because `z⁻¹ → ∞` as `z → 0` (`tendsto_inv₀_nhdsNE_zero` + `tendsto_coe_infty`).

It is an involution, so the same proof serves for both `toFun` and `invFun`. -/

open Filter Bornology in
/-- The underlying point map of the inversion: `∞ ↦ 0`, `0 ↦ ∞`, and `z ↦ z⁻¹` otherwise. -/
def invMap : RiemannSphere → RiemannSphere :=
  fun p => p.elim (((0 : ℂ)) : RiemannSphere)
    (fun z => if z = 0 then (OnePoint.infty) else ((z⁻¹ : ℂ) : RiemannSphere))

@[simp] lemma invMap_infty : invMap OnePoint.infty = (((0 : ℂ)) : RiemannSphere) := rfl

lemma invMap_coe (z : ℂ) :
    invMap (z : RiemannSphere) =
      if z = 0 then (OnePoint.infty) else ((z⁻¹ : ℂ) : RiemannSphere) := rfl

@[simp] lemma invMap_coe_zero : invMap ((0 : ℂ) : RiemannSphere) = OnePoint.infty := by
  simp [invMap_coe]

lemma invMap_coe_of_ne {z : ℂ} (hz : z ≠ 0) :
    invMap (z : RiemannSphere) = ((z⁻¹ : ℂ) : RiemannSphere) := by
  simp [invMap_coe, hz]

lemma involutive_invMap : Function.Involutive invMap := by
  intro p
  induction p using OnePoint.rec with
  | infty => simp [invMap]
  | coe z =>
    by_cases hz : z = 0
    · subst hz; simp [invMap]
    · have hz' : (z⁻¹ : ℂ) ≠ 0 := inv_ne_zero hz
      simp only [invMap, OnePoint.elim_some, hz, if_false, hz', inv_inv]

open Filter Bornology Topology in
/-- The coercion `ℂ → OnePoint ℂ` tends to `∞` along `cobounded ℂ` (i.e. as `|z| → ∞`). -/
lemma tendsto_coe_cobounded_infty :
    Tendsto ((↑) : ℂ → RiemannSphere) (cobounded ℂ) (𝓝 OnePoint.infty) := by
  have := @OnePoint.tendsto_coe_infty ℂ _
  rwa [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact] at this

open Filter Bornology Topology in
lemma tendsto_invMap_infty :
    Tendsto (fun z : ℂ => invMap (z : RiemannSphere)) (coclosedCompact ℂ) (𝓝 (invMap OnePoint.infty)) := by
  rw [Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact, invMap_infty]
  have hcoe : Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : RiemannSphere)) (cobounded ℂ)
      (𝓝 ((0 : ℂ) : RiemannSphere)) :=
    (OnePoint.continuous_coe.tendsto _).comp tendsto_inv₀_cobounded
  refine hcoe.congr' ?_
  filter_upwards [eventually_ne_cobounded (0 : ℂ)] with z hz
  simp [invMap_coe, hz]

open Filter Bornology Topology in
/-- The affine restriction `z ↦ invMap z : ℂ → OnePoint ℂ` is continuous. -/
lemma continuous_invMap_coe : Continuous (fun z : ℂ => invMap (z : RiemannSphere)) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [continuousAt_iff_punctured_nhds, invMap_coe_zero]
    have key : Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : RiemannSphere)) (𝓝[≠] (0 : ℂ))
        (𝓝 OnePoint.infty) :=
      tendsto_coe_cobounded_infty.comp tendsto_inv₀_nhdsNE_zero
    refine key.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    simp [invMap_coe, hz]
  · have hev : (fun w : ℂ => invMap (w : RiemannSphere)) =ᶠ[𝓝 z]
        (fun w : ℂ => ((w⁻¹ : ℂ) : RiemannSphere)) := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      simp [invMap_coe, hw]
    refine ContinuousAt.congr ?_ hev.symm
    exact OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)

lemma continuous_invMap : Continuous invMap := by
  rw [OnePoint.continuous_iff]
  exact ⟨tendsto_invMap_infty, continuous_invMap_coe⟩

/-- Inversion `z ↦ z⁻¹` as a self-homeomorphism of the Riemann sphere, swapping `0 ↔ ∞`.
This is the change of coordinates between the two standard charts. -/
def inversionHomeomorph : RiemannSphere ≃ₜ RiemannSphere where
  toFun := invMap
  invFun := invMap
  left_inv := involutive_invMap
  right_inv := involutive_invMap
  continuous_toFun := continuous_invMap
  continuous_invFun := continuous_invMap

@[simp] lemma inversionHomeomorph_apply (p : RiemannSphere) : inversionHomeomorph p = invMap p := rfl

@[simp] lemma inversionHomeomorph_symm_apply (p : RiemannSphere) :
    inversionHomeomorph.symm p = invMap p := rfl

end RiemannSphere

end Jacobians
