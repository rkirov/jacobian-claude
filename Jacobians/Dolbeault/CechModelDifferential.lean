/-
  Čech finiteness — the CROSS-CHART Čech `δ⁰` on the sup-norm `BddHol` cochains (piece (a) of
  `exists_cechModel`, Forster 14.9).

  `CechModelDelta.lean` built the sup-norm cochain SPACES (`Cochain0Model`, `Cochain2*Model`) and their
  Banach structure, and flagged the next gap as the CROSS-CHART differentials — the off-diagonal
  components of the Čech coboundary, transported between neighbouring chart-images through the
  holomorphic chart transitions `φ_a ∘ φ_b⁻¹`. THIS FILE builds the Čech `δ⁰ : Cochain0Model →L Cshr`
  for the chart-cover model `chartCoverOverlapData`.

  THE CROSS-CHART SUBTLETY (recap).  A 0-cochain `f` assigns each cover chart `a` a bounded-holomorphic
  function `f a` on its OWN chart-image `coverSetImage a` (chart-`a` coordinates).  The Čech `δ⁰` on the
  overlap `(a,b)`, read in the FIRST chart `a` (matching `chartCoverOverlapData`'s `Uov`/`Kov`), is
      `(δ⁰f)_{ab} = (f b ∘ φ_b ∘ φ_a⁻¹) − (f a)`     on the shrinking `Kov (a,b)`,
  i.e. `f a` restricts directly, but `f b` (living in chart-`b` coordinates) must be TRANSPORTED to
  chart-`a` coordinates through the holomorphic transition `τ_{ab} = φ_b ∘ φ_a⁻¹`.  The two
  geometric witnesses the transport needs — `τ_{ab}` continuous on `Kov (a,b)` and mapping it into
  `coverSetImage b` — come from the `ω`-manifold's chart change (`transition_analyticAt_of_mem`,
  `CechModelManifold`), and the functional-analysis transport `g ↦ g ∘ τ` is `BddHol.precompCLM`
  (`BddHol`).  `δ⁰` is then the per-overlap difference (off-diagonal transport `−` diagonal
  restriction), assembled by `ContinuousLinearMap.pi`.

  This is the genuine content of part (a) of the `exists_cechModel` model.  Sorry-free, axiom-clean
  `[propext, Classical.choice, Quot.sound]`.  (The shrinking-side `δ¹`, the cover-side `δ¹cov`, the
  `hδδ`/`hcomm` algebra, the `leray` disk-acyclicity field, and the `cechH1 ≃ supH1` comparison remain
  — see `CechFinitenessWiring.exists_cechModel` and `docs/cech_finiteness_research.md`.)
-/
import Jacobians.Dolbeault.CechModelDelta
import Jacobians.Dolbeault.CechModelManifold

open scoped Manifold ContDiff Topology
open Jacobians.Montel ContinuousLinearMap
open BoundedContinuousFunction

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The chart transition `τ_{ab} = φ_b ∘ φ_a⁻¹` and its geometric witnesses on `Kov (a,b)` -/

/-- **The cover chart transition** `τ_{ab} = φ_b ∘ φ_a⁻¹` (chart-`a` coordinates → chart-`b`
coordinates), for the cover charts indexed `a, b : Fin #chartCover`.  Used to transport the `b`-side
0-cochain component into chart-`a` coordinates for the Čech `δ⁰`. -/
noncomputable def coverTransition (a b : Fin ((chartCover : Finset X).card)) : ℂ → ℂ :=
  (chartAt (H := ℂ) (coverCenter b)) ∘ (chartAt (H := ℂ) (coverCenter a)).symm

/-- The transition `τ_{ab}` is continuous on the compact overlap-shrinking `Kov (a,b)` (chart-`a`
image of `innerShrunk a ∩ innerShrunk b`): at each point it is analytic (`transition_analyticAt_of_mem`,
both centres' sources containing the inner-shrunk overlap point), hence continuous. -/
theorem continuousOn_coverTransition_Kov (a b : Fin ((chartCover : Finset X).card)) :
    ContinuousOn (coverTransition (X := X) a b) ((chartCoverOverlapData (X := X)).Kov (a, b)) := by
  rintro w ⟨x, ⟨hxa, hxb⟩, rfl⟩
  apply ContinuousAt.continuousWithinAt
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter a)).source :=
    chartOpen_subset_chartAt_source (coverCenter a) (coverCenter_mem a)
      (innerShrunkChart_subset_chartOpen (coverCenter a) hxa)
  have hxb_src : x ∈ (chartAt (H := ℂ) (coverCenter b)).source :=
    chartOpen_subset_chartAt_source (coverCenter b) (coverCenter_mem b)
      (innerShrunkChart_subset_chartOpen (coverCenter b) hxb)
  exact (transition_analyticAt_of_mem hxa_src hxb_src).continuousAt

/-- The transition `τ_{ab}` maps the shrinking `Kov (a,b)` (chart-`a` coordinates) into `coverSetImage
b` (chart-`b` image of `chartOpen b`), where the `b`-component of a 0-cochain is bounded-holomorphic.
A point `φ_a x` with `x ∈ innerShrunk a ∩ innerShrunk b` maps to `φ_b x ∈ φ_b '' (innerShrunk b) ⊆ φ_b
'' (chartOpen b) = coverSetImage b`. -/
theorem mapsTo_coverTransition_Kov (a b : Fin ((chartCover : Finset X).card)) :
    Set.MapsTo (coverTransition (X := X) a b) ((chartCoverOverlapData (X := X)).Kov (a, b))
      (coverSetImage (X := X) b) := by
  rintro w ⟨x, ⟨hxa, hxb⟩, rfl⟩
  have hxa_src : x ∈ (chartAt (H := ℂ) (coverCenter a)).source :=
    chartOpen_subset_chartAt_source (coverCenter a) (coverCenter_mem a)
      (innerShrunkChart_subset_chartOpen (coverCenter a) hxa)
  exact ⟨x, innerShrunkChart_subset_chartOpen (coverCenter b) hxb, by
    simp only [coverTransition, Function.comp_apply,
      (chartAt (H := ℂ) (coverCenter a)).left_inv hxa_src]⟩

/-! ### The off-diagonal transport and the diagonal restriction (the two pieces of `δ⁰`) -/

/-- **The off-diagonal transport CLM.**  The `b`-component `f b : BddHol (coverSetImage b)`,
transported to chart-`a` coordinates through `τ_{ab}` and read on the compact shrinking `Kov (a,b)`, as
a bounded-continuous function there.  This is the `+` half of `(δ⁰f)_{ab}` (the cross-chart piece),
built from `BddHol.precompCLM` with the two transition witnesses. -/
noncomputable def transportComp (a b : Fin ((chartCover : Finset X).card)) :
    BddHol (coverSetImage (X := X) b) →L[ℂ] ((chartCoverOverlapData (X := X)).Kov (a, b) →ᵇ ℂ) :=
  BddHol.precompCLM (continuousOn_coverTransition_Kov a b) (mapsTo_coverTransition_Kov a b)

/-- The shrinking `Kov (a,b)` lies in `coverSetImage a` (chart-`a` image of `innerShrunk a ∩ innerShrunk
b ⊆ chartOpen a`), so the `a`-component restricts directly. -/
theorem Kov_subset_coverSetImage_fst (a b : Fin ((chartCover : Finset X).card)) :
    (chartCoverOverlapData (X := X)).Kov (a, b) ⊆ coverSetImage (X := X) a := by
  show (chartAt (H := ℂ) (coverCenter a)) ''
      (innerShrunkChart (X := X) (coverCenter a) ∩ innerShrunkChart (X := X) (coverCenter b))
    ⊆ coverSetImage (X := X) a
  unfold coverSetImage
  exact Set.image_mono
    (Set.inter_subset_left.trans (innerShrunkChart_subset_chartOpen (coverCenter a)))

/-- **The diagonal restriction CLM.**  The `a`-component `f a : BddHol (coverSetImage a)`, restricted to
the shrinking `Kov (a,b) ⊆ coverSetImage a`, as a bounded-continuous function there.  This is the `−`
half of `(δ⁰f)_{ab}` (the same-chart piece), built from `BddHol.restrictCLM`. -/
noncomputable def restrictComp (a b : Fin ((chartCover : Finset X).card)) :
    BddHol (coverSetImage (X := X) a) →L[ℂ] ((chartCoverOverlapData (X := X)).Kov (a, b) →ᵇ ℂ) :=
  BddHol.restrictCLM (Kov_subset_coverSetImage_fst a b)

/-! ### The cross-chart Čech `δ⁰ : Cochain0Model →L Cshr` -/

/-- **The cross-chart Čech `δ⁰`** of the chart-cover sup-norm model: `Cochain0Model →L[ℂ] Cshr`
(`chartCoverOverlapData`'s shrinking 1-cochains).  Componentwise on overlap `(a,b)`,
    `(δ⁰f)_{ab} = (transport of f b to chart-a) − (restriction of f a)`   on `Kov (a,b)`,
the genuine Čech coboundary with the `b`-side transported through the holomorphic transition `τ_{ab}`.
Assembled by `ContinuousLinearMap.pi` over the off-diagonal transport `transportComp` and diagonal
restriction `restrictComp`. -/
noncomputable def delta0Model : Cochain0Model (X := X) →L[ℂ] (chartCoverOverlapData (X := X)).Cshr :=
  ContinuousLinearMap.pi fun p =>
    (transportComp p.1 p.2).comp (proj p.2) - (restrictComp p.1 p.2).comp (proj p.1)

/-- The component identity for `δ⁰` at overlap `p = (a,b)`: the off-diagonal transport of `f b` minus
the diagonal restriction of `f a`. -/
theorem delta0Model_apply (f : Cochain0Model (X := X)) (p : (chartCoverOverlapData (X := X)).J) :
    delta0Model f p = transportComp p.1 p.2 (f p.2) - restrictComp p.1 p.2 (f p.1) := rfl

/-- **The Čech coboundary pointwise formula.**  On the shrinking `Kov (a,b)`, the `δ⁰` value at a point
`z` is `f b` evaluated at the transported point `τ_{ab} z` minus `f a` at `z` — the explicit
cross-chart Čech `δ⁰` formula `(δ⁰f)_{ab}(z) = f_b(τ_{ab} z) − f_a(z)`. -/
theorem delta0Model_apply_apply (f : Cochain0Model (X := X))
    (p : (chartCoverOverlapData (X := X)).J) (z : (chartCoverOverlapData (X := X)).Kov p) :
    delta0Model f p z = (f p.2).toFun (coverTransition p.1 p.2 z.1) - (f p.1).toFun z.1 := by
  have h : (delta0Model f p) z
      = (transportComp p.1 p.2 (f p.2)) z - (restrictComp p.1 p.2 (f p.1)) z := by
    rw [delta0Model_apply]; rfl
  rw [h, transportComp, restrictComp, BddHol.precompCLM_apply, BddHol.precompBcf_apply,
    BddHol.restrictCLM_apply, BddHol.restrict_apply]

end Jacobians.Dolbeault
