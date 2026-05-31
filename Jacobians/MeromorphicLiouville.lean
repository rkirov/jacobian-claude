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

end Jacobians
