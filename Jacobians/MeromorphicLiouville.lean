/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Abel

/-!
# Compact Liouville for meromorphic functions (non-Dolbeault)

A non-constant meromorphic function on a compact connected Riemann surface must have a pole.
This is the meromorphic corollary of holomorphic Liouville
(`MDifferentiable.exists_eq_const_of_compactSpace`): if `f` had no pole, then in every chart its
order is `≥ 0`, so `f` is (a removable-singularity repair of) a holomorphic function; on a compact
connected manifold that forces it to be constant, whence its order is `≡ 0`, contradicting
non-constancy.

## The removable-singularity repair

The repo's `MeromorphicFunction.toFun : X → ℂ` is only pinned up to its germ off each point: at an
isolated removable singularity it may carry an arbitrary "junk" value. Mathlib's order-based limit
theory (`tendsto_nhds_of_meromorphicOrderAt_nonneg`) shows that wherever the order is `≥ 0` the
function has a genuine limit along the punctured neighborhood. We therefore work with the
**limit repair**

  `holoRepr f x := limUnder (𝓝[≠] x) f.toFun`,

which discards the junk: it agrees with the normal-form representative
(`toMeromorphicNFAt`) in every chart, hence is analytic in every chart, hence globally
`MDifferentiable`. No manual gluing of per-chart germs is needed — the single global definition
`holoRepr` is analytic at every point by a per-chart computation.

## References

* Forster, *Lectures on Riemann Surfaces*, §§2, 10 (Liouville).
* Mathlib `Mathlib/Analysis/Meromorphic/Order.lean`, `Mathlib/Analysis/Meromorphic/NormalForm.lean`.
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Topology
open Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Order bridge: `ℤ`-order nonneg ↔ `WithTop ℤ`-order nonneg -/

/-- The integer order `.untop₀` is `≥ 0` iff the raw `WithTop ℤ` order is `≥ 0`. (`⊤ ↦ 0 ≥ 0`.) -/
theorem untop₀_nonneg_iff {α : WithTop ℤ} : (0 : ℤ) ≤ α.untop₀ ↔ 0 ≤ α := by
  cases α with
  | top => simp
  | coe n => simp [WithTop.untop₀_coe]

/-! ### The limit repair of a meromorphic function -/

/-- The **limit repair** of `f`: at each point, the limit of `f` along the punctured neighborhood.
Where the order of `f` is `≥ 0` this is a genuine value (Mathlib
`tendsto_nhds_of_meromorphicOrderAt_nonneg`), and it discards removable-singularity junk that
`f.toFun` may carry. -/
noncomputable def MeromorphicFunction.holoRepr (f : MeromorphicFunction X) (x : X) : ℂ :=
  limUnder (𝓝[≠] x) f.toFun

/-! ### A chart-independent characterization of "order `≥ 0`"

`orderAtPoint f x` is *defined* via the chart `chartAt x`, so comparing it to the order of the
pullback `f.toFun ∘ φ.symm` in a different chart `φ` needs chart-invariance of the order. We avoid
the (currently unproved) `orderAtPoint_chart_invariant` by characterizing nonnegativity of the order
in a manifestly chart-independent way: **`f` has a limit along the punctured neighborhood `𝓝[≠] x`**
(Mathlib `tendsto_nhds_iff_meromorphicOrderAt_nonneg`). Transferring a `Tendsto` statement through a
chart homeomorphism is elementary. -/

/-- An open partial homeomorphism carries the punctured neighborhood of a source point to the
punctured neighborhood of its image: `Tendsto φ (𝓝[≠] x) (𝓝[≠] (φ x))` for `x ∈ φ.source`.
(Continuity gives the unpunctured limit; injectivity on the source removes the center.) -/
theorem _root_.OpenPartialHomeomorph.tendsto_nhdsNE {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] (φ : OpenPartialHomeomorph Y Z) {x : Y} (hx : x ∈ φ.source) :
    Tendsto φ (𝓝[{x}ᶜ] x) (𝓝[{φ x}ᶜ] (φ x)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact (φ.continuousAt hx).continuousWithinAt
  · have hev : ∀ᶠ y in 𝓝 x, y ∈ φ.source := φ.open_source.mem_nhds hx
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hev] with y hy hys
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    exact fun hcontra => hy (φ.injOn hys hx hcontra)

/-- The order of `f` at `x` is `≥ 0` iff `f.toFun` has a limit along the punctured neighborhood of
`x` — a manifestly chart-independent statement. -/
theorem MeromorphicFunction.orderAtPoint_nonneg_iff_tendsto
    (f : MeromorphicFunction X) (x : X) :
    0 ≤ f.orderAtPoint x ↔ ∃ c, Tendsto f.toFun (𝓝[≠] x) (𝓝 c) := by
  set φ := chartAt (H := ℂ) x with hφ
  have hxs : x ∈ φ.source := mem_chart_source ℂ x
  have hmero : MeromorphicAt (f.toFun ∘ φ.symm) (φ x) := f.meromorphic x
  -- bridge ℤ-order to WithTop-order, then to the punctured-limit of the pullback
  rw [show f.orderAtPoint x = (meromorphicOrderAt (f.toFun ∘ φ.symm) (φ x)).untop₀ from rfl,
    untop₀_nonneg_iff, ← tendsto_nhds_iff_meromorphicOrderAt_nonneg hmero]
  constructor
  · rintro ⟨c, hc⟩
    -- pullback has a limit at φ x  ⟹  f.toFun has a limit at x.
    -- Compose `f.toFun ∘ φ.symm` (limit at φx) with the forward chart `φ` (𝓝[≠]x → 𝓝[≠]φx).
    refine ⟨c, ?_⟩
    have htfwd : Tendsto φ (𝓝[≠] x) (𝓝[≠] (φ x)) := φ.tendsto_nhdsNE hxs
    have hcomp : Tendsto (f.toFun ∘ φ.symm ∘ φ) (𝓝[≠] x) (𝓝 c) := hc.comp htfwd
    refine hcomp.congr' ?_
    have hev : ∀ᶠ y in 𝓝 x, y ∈ φ.source := φ.open_source.mem_nhds hxs
    filter_upwards [mem_nhdsWithin_of_mem_nhds hev] with y hy
    simp [Function.comp, φ.left_inv hy]
  · rintro ⟨c, hc⟩
    -- f.toFun has a limit at x ⟹ pullback has a limit at φ x.
    -- Compose `f.toFun` (limit at x) with the inverse chart `φ.symm` (𝓝[≠]φx → 𝓝[≠]x).
    refine ⟨c, ?_⟩
    have hwt : φ x ∈ φ.target := φ.map_source hxs
    have htsymm : Tendsto φ.symm (𝓝[≠] (φ x)) (𝓝[≠] x) := by
      have := φ.symm.tendsto_nhdsNE (x := φ x) (by simpa using hwt)
      simpa [φ.left_inv hxs] using this
    exact hc.comp htsymm

end Jacobians
