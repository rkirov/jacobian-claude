/-
  Čech finiteness — the SHRINKING-SCALE 0-cochains and `δ⁰` for the holomorphic model.

  This file re-points the 0-cochain scale of the holomorphic-shrinking model
  `chartCoverHolomorphicDiskOverlapData` from the COVER scale (`coverSetImage a = φ_a '' chartOpen a`,
  used by `CechModelDelta.Cochain0Model` / `CechModelHolomorphicDelta.delta0ModelHolo`) DOWN to the
  SHRINKING scale (`innerChartImage a = φ_a '' innerChartOpen a`).  This is Forster GTM 81's natural
  two-scale statement for the `H¹`-finiteness lift (Lemma 14.6): the 0-cochains `C⁰(𝔙)` live on the
  shrinking cover `𝔙`, while the cover 1-cocycles `Z¹(𝔘)` live on the (outer) cover `𝔘`.

  Why the re-point.  The previous `leray` attempt wired `C0 := Cochain0Model` at the COVER scale, but
  the Forster–Dolbeault lift `η_a := h_a − g_a` is holomorphic only on the SHRINKING region.  Pinning
  `C0` to `innerChartImage` makes `η ∈ C0` land in the right space.  It is ALSO required for the
  comparison: with the cover-scale `C0`, the model's `supH1` is not the genuine shrinking-cover `H¹`.

  Mirrors `CechModelHolomorphicDelta.lean` EXACTLY, but with the single-set shrinking image
  `innerChartImage a` (chart-`a` image of `innerChartOpen a`) in place of the single-set outer image
  `coverSetImage a`.  The geometric witnesses (transition analytic on `Wov`, mapping it into the
  `b`-side image) are re-proven over the shrinking images, reusing the same chart-change atoms.

  All sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Jacobians.Dolbeault.CechModelHolomorphicDelta

open scoped Manifold ContDiff Topology
open Jacobians.Montel ContinuousLinearMap

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The single-set shrinking chart image `innerChartImage a` and its `BddHol` space -/

/-- The chart-`a` image of the inner shrinking `innerChartOpen (coverCenter a)` — the open set in `ℂ`
(chart-`a` coordinates) where the SHRINKING-scale 0-cochain component over `a` is
bounded-holomorphic.  This is the diagonal shrinking `Wov (a,a)`. -/
noncomputable def innerChartImage (a : Fin ((chartCover : Finset X).card)) : Set ℂ :=
  (chartAt (H := ℂ) (montel_coverCenter (X := X) a)) ''
    (innerChartOpen (X := X) (montel_coverCenter (X := X) a))

theorem isOpen_innerChartImage (a : Fin ((chartCover : Finset X).card)) :
    IsOpen (innerChartImage (X := X) a) :=
  (chartAt (H := ℂ) (montel_coverCenter (X := X) a)).isOpen_image_of_subset_source
    (innerChartOpen_isOpen (montel_coverCenter (X := X) a))
    (innerChartOpen_subset_chartAt_source_aux a)

/-- **Shrinking-scale 0-cochains.**  Bounded-holomorphic on each cover set's INNER (shrinking)
chart-image — the Forster `C⁰(𝔙)` 0-cochains on the shrinking cover, in the `BddHol` representation. -/
abbrev Cochain0ModelHolo : Type :=
  ∀ a : Fin ((chartCover : Finset X).card), BddHol (innerChartImage (X := X) a)

noncomputable instance : NormedAddCommGroup (Cochain0ModelHolo (X := X)) := inferInstance
noncomputable instance : NormedSpace ℂ (Cochain0ModelHolo (X := X)) := inferInstance

/-- `Cochain0ModelHolo` is Banach (finite product of the Banach `BddHol`). -/
noncomputable instance : CompleteSpace (Cochain0ModelHolo (X := X)) := by
  haveI : ∀ a, CompleteSpace (BddHol (innerChartImage (X := X) a)) := fun a =>
    BddHol.completeSpace (isOpen_innerChartImage a)
  infer_instance

/-! ### The shrinking-side `δ⁰` geometric witnesses

The shrinking-scale `δ⁰` reads the overlap `(a,b)` in chart `a` on the OPEN shrinking `Wov (a,b)`.
The `a`-component restricts directly to `Wov (a,b) ⊆ innerChartImage a`; the `b`-component is
transported chart-`b`→chart-`a` through `τ_{ab}` (analytic on `Wov (a,b)`, mapping it into
`innerChartImage b`).  Same witnesses as `CechModelHolomorphicDelta`, now into the SHRINKING image. -/

/-- The cover transition `τ_{ab}` maps the OPEN shrinking `Wov (a,b)` (chart-`a` coordinates) into
`innerChartImage b` (chart-`b` image of `innerChartOpen b`).  A point `φ_a x` with `x ∈ innerChartOpen
a ∩ innerChartOpen b` maps to `φ_b x` with `x ∈ innerChartOpen b`, so `φ_b x ∈ φ_b '' innerChartOpen b
= innerChartImage b`.  (Mirrors `mapsTo_coverTransition_Wov`, but routed into the SHRINKING image of
`b` rather than the larger `coverSetImage b`.) -/
theorem mapsTo_coverTransition_Wov_inner (a b : Fin ((chartCover : Finset X).card)) :
    Set.MapsTo (coverTransition (X := X) a b) ((chartCoverHolomorphicDiskOverlapData (X := X)).Wov (a, b))
      (innerChartImage (X := X) b) := by
  rintro w ⟨x, ⟨hxa, hxb⟩, rfl⟩
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter (X := X) a)).source :=
    innerChartOpen_subset_chartAt_source_aux a hxa
  refine ⟨x, hxb, ?_⟩
  simp only [montel_coverCenter_eq_coverCenter, coverTransition, Function.comp_apply,
    (chartAt (H := ℂ) (coverCenter (X := X) a)).left_inv hxa_src]

/-- The shrinking `Wov (a,b)` lies in `innerChartImage a` (chart-`a` image of `innerChartOpen a ∩
innerChartOpen b ⊆ innerChartOpen a`), so the `a`-component restricts directly. -/
theorem Wov_subset_innerChartImage_fst (a b : Fin ((chartCover : Finset X).card)) :
    (chartCoverHolomorphicDiskOverlapData (X := X)).Wov (a, b) ⊆ innerChartImage (X := X) a := by
  show (chartAt (H := ℂ) (montel_coverCenter (X := X) a)) ''
      (innerChartOpen (X := X) (montel_coverCenter (X := X) a) ∩
        innerChartOpen (X := X) (montel_coverCenter (X := X) b)) ⊆ innerChartImage (X := X) a
  exact Set.image_mono Set.inter_subset_left

/-- **The shrinking-scale cross-chart Čech `δ⁰`** of the holomorphic model:
`Cochain0ModelHolo →L[ℂ] d.Cshr`.  Componentwise on overlap `(a,b)`,
    `(δ⁰f)_{ab} = (transport of f b to chart-a) − (restriction of f a)`   on the OPEN `Wov (a,b)`,
the genuine Čech coboundary with the `b`-side transported through `τ_{ab}`.  Both pieces stay `BddHol`
on the open `Wov`: the off-diagonal via `BddHol.precompHolCLM` (into `innerChartImage b`), the diagonal
via `BddHol.restrictOpenCLM` (`Wov (a,b) ⊆ innerChartImage a`).  Mirrors `delta0ModelHolo` but with
domain `Cochain0ModelHolo` (shrinking images) instead of `Cochain0Model` (cover images). -/
noncomputable def delta0ModelHoloShrink :
    Cochain0ModelHolo (X := X) →L[ℂ] (chartCoverHolomorphicDiskOverlapData (X := X)).Cshr :=
  ContinuousLinearMap.pi fun p =>
    (BddHol.precompHolCLM (analyticOn_coverTransition_Wov p.1 p.2)
        (mapsTo_coverTransition_Wov_inner p.1 p.2)).comp (proj p.2)
      - (BddHol.restrictOpenCLM (Wov_subset_innerChartImage_fst p.1 p.2)).comp (proj p.1)

/-- The component identity for the shrinking-scale `δ⁰` at overlap `p = (a,b)`. -/
theorem delta0ModelHoloShrink_apply (f : Cochain0ModelHolo (X := X))
    (p : (chartCoverHolomorphicDiskOverlapData (X := X)).J) :
    delta0ModelHoloShrink f p
      = BddHol.precompHolCLM (analyticOn_coverTransition_Wov p.1 p.2)
          (mapsTo_coverTransition_Wov_inner p.1 p.2) (f p.2)
        - BddHol.restrictOpenCLM (Wov_subset_innerChartImage_fst p.1 p.2) (f p.1) := rfl

/-- **The shrinking-scale Čech coboundary pointwise formula.**  On the OPEN shrinking `Wov (a,b)`, the
`δ⁰` value at `z` is `f b` at the transported point `τ_{ab} z` minus `f a` at `z` — the explicit
cross-chart formula `(δ⁰f)_{ab}(z) = f_b(τ_{ab} z) − f_a(z)`. -/
theorem delta0ModelHoloShrink_apply_apply (f : Cochain0ModelHolo (X := X))
    (p : (chartCoverHolomorphicDiskOverlapData (X := X)).J)
    {z : ℂ} (hz : z ∈ (chartCoverHolomorphicDiskOverlapData (X := X)).Wov p) :
    (delta0ModelHoloShrink f p).toFun z
      = (f p.2).toFun (coverTransition p.1 p.2 z) - (f p.1).toFun z := by
  obtain ⟨a, b⟩ := p
  rw [delta0ModelHoloShrink_apply, BddHol.toFun_sub, Pi.sub_apply,
    BddHol.precompHolCLM_apply, BddHol.precompHol_toFun_of_mem _ _ _ hz,
    BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]

/-! ### `δ¹ ∘ δ⁰ = 0` and `hcomm` at the shrinking scale

The shrinking-side `δ¹` (`delta1ModelHolo`) and the cover-side `δ¹` (`delta1CovModelHolo`) are reused
from `CechModelHolomorphicDelta`; only the 0-cochain scale changed.  The cocycle identity `δ¹∘δ⁰ = 0`
and the commuting square `hcomm` are re-proven against `delta0ModelHoloShrink`, mirroring
`delta1_comp_delta0_holo` / `hcomm_holo` verbatim (the commuting square `hcomm` is INDEPENDENT of the
0-cochain scale, so it is reused). -/

/-- **`δ¹ ∘ δ⁰ = 0` at the shrinking scale.**  Identical six-term collapse to `delta1_comp_delta0_holo`,
now with the shrinking-scale `δ⁰`: on the OPEN triple the six terms of `(δ¹(δ⁰f))_{abc}(z)` collapse to
`f_c(τ_{bc}(τ_{ab} z)) − f_c(τ_{ac} z) = 0` by the cocycle identity `coverTransition_cocycle_Wov`. -/
theorem delta1_comp_delta0_holoShrink :
    (delta1ModelHolo (X := X)).comp delta0ModelHoloShrink = 0 := by
  ext f t
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  apply BddHol.toFun_injective
  funext z
  by_cases hz : z ∈ WovTriple (X := X) t
  · rw [show ((0 : C2Holo (X := X)) t).toFun z = 0 from rfl]
    rw [delta1ModelHolo_apply_apply _ _ hz]
    obtain ⟨a, b, c⟩ := t
    rw [delta0ModelHoloShrink_apply_apply _ _ (mapsTo_coverTransition_WovTriple_shrink a b c hz),
      delta0ModelHoloShrink_apply_apply _ _ (WovTriple_subset_Wov_fst_trd a b c hz),
      delta0ModelHoloShrink_apply_apply _ _ (WovTriple_subset_Wov_fst_snd a b c hz)]
    rw [coverTransition_cocycle_Wov a b c hz]
    ring
  · rw [show ((0 : C2Holo (X := X)) t).toFun z = 0 from rfl,
      (delta1ModelHolo (delta0ModelHoloShrink f) t).zero_off z hz]

end Jacobians.Dolbeault
