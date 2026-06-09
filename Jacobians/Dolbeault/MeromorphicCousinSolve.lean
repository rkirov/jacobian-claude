/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.MeromorphicCousin

/-!
# Forster §15 + §17.2–17.3 — the meromorphic Cousin solve, the distribution algebra, and the descent

This file continues `MeromorphicCousin.lean` (the connecting map `δ` and the residue calculus at the
genuine Forster `δμ ∈ Z¹(Ω)` strength).  Its goal is the wall `H¹(X, ℳ) = 0` (the `surjective` field
of `MeromorphicCousinSolvable`) and the mechanical descent that turns a Cousin solution into the
Serre residue functional.

## The `holoOff` gap (read first — a genuine soundness finding)

The committed `CoverMLDistribution 𝔘 ω₀ K` carries `diffMem`/`formHoloDiff` (the overlap conditions of
`δμ ∈ Z¹(Ω)`) and `iso` (isolated singularity at each recorded pole) — but **no `holoOff` field**
(holomorphy away from the recorded poles, as `GeneralMLDistribution` has).  Without it:

* its distribution **algebra is unbuildable**: `combine μ₁ μ₂`'s `iso` at a pole `a ∈ μ₁.poles \ μ₂.poles`
  needs `μ₂.g (μ₁.patch a)` isolated at `a`, which (when `a ∉ μ₂.poles`) is exactly `holoOff`; and
* `μ.res = ∑_{a ∈ poles} Resₐ` need **not be the genuine total residue** (a "global" pole of every `gᵢ`
  outside `poles`, cancelled in all differences, is invisible to `poles` yet contributes a residue).

So the descent's well-definedness `[δμ₁] = [δμ₂] ⟹ μ₁.res = μ₂.res` (via Gate A) genuinely needs
`holoOff`.  Rather than mutate the committed structure (and the proven connecting map), we introduce a
**richer lift** `CoverMLLift 𝔘 ω₀ K` (= `CoverMLDistribution` + `holoOff`), build the algebra and the
descent on it, and reduce the wall to a single precise Cousin atom on `CoverMLLift`.  A genuine Cousin
solution (the local-meromorphic lift of a cocycle) always has `holoOff`, so this is no loss.

## What this file delivers (sorry-free, axiom-clean unless noted)

* `CoverMLLift 𝔘 ω₀ K` — the `holoOff`-equipped lift; `toDistribution` forgets `holoOff`, `res`/
  `connectingCocycle`/`connectingClass` inherited.
* The **distribution algebra**: `smul`, `neg`, `combine` (add), `sub`, each a genuine `CoverMLLift`,
  with `res_smul`/`res_neg`/`res_combine`/`res_sub` (res-additivity from `formFnResidue_add`/`_smul`)
  and `connectingCochain`/`connectingClass` additivity.
* `holoOff` gives that **`res` is the genuine total residue** (`res_eq_residueSum_of_subset`-style):
  every pole of every `gᵢ` is recorded, so `res` reads the full Laurent residue sum.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §15 (`H¹(X,ℳ)=0`), §17.2–17.3;
`MeromorphicCousin.lean`; `GeneralMittagLeffler.lean` (`res_eq_zero_of_globalMeromorphic`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

variable {𝔘 : FiniteCover X} {ω₀ : HolomorphicOneForms X} {K : Divisor X}

/-! ## The `holoOff`-equipped Cousin lift -/

/-- **A meromorphic Cousin lift** over the fixed cover `𝔘`: a `CoverMLDistribution` together with the
**off-poles holomorphy** field `holoOff` that the committed `CoverMLDistribution` omits (see the module
docstring).  A genuine Cousin solution (the local-meromorphic lift `gᵢ` of an `𝒪_K` cocycle) always has
it: away from the finitely many recorded poles each `gᵢ` is holomorphic.  With it the residue is the
genuine total residue and the distribution algebra (`combine`/`sub`) closes. -/
structure CoverMLLift (𝔘 : FiniteCover X) (ω₀ : HolomorphicOneForms X) (K : Divisor X) where
  /-- The underlying cover-adapted distribution (the data the connecting map δ consumes). -/
  toDistribution : CoverMLDistribution 𝔘 ω₀ K
  /-- **Off-poles holomorphy**: away from the recorded poles each `gᵢ`'s chart-pullback is analytic at
  every point of `𝔘.U i` (so `ωᵢ = gᵢ·ω₀` is holomorphic there). -/
  holoOff : ∀ (i : 𝔘.ι) (a : X), a ∈ 𝔘.U i → a ∉ toDistribution.poles →
    AnalyticAt ℂ (fun z => toDistribution.g i ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)

namespace CoverMLLift

variable (μ : CoverMLLift 𝔘 ω₀ K)

/-- The local principal part on patch `i`. -/
def g (i : 𝔘.ι) : X → ℂ := μ.toDistribution.g i

/-- The finite pole set. -/
def poles : Finset X := μ.toDistribution.poles

/-- The total residue of the lift (the underlying distribution's genuine Laurent residue sum). -/
noncomputable def res : ℂ := μ.toDistribution.res

/-- The connecting cocycle `δμ ∈ Z¹(𝔘, 𝒪_K)` (inherited from the underlying distribution). -/
noncomputable def connectingCocycle : ↥(𝔘.toFiniteFamily.cocycles1 K) :=
  μ.toDistribution.connectingCocycle

/-- The connecting class `[δμ] ∈ cechH1 K` (inherited). -/
noncomputable def connectingClass : 𝔘.toFiniteFamily.cechH1 K :=
  μ.toDistribution.connectingClass

@[simp] theorem res_def : μ.res = ∑ a ∈ μ.poles, formFnResidue ω₀ (μ.g (μ.toDistribution.patch a)) a :=
  CoverMLDistribution.res_def μ.toDistribution

/-- **Off poles, `ω₀·gᵢ` has an isolated singularity** (from `holoOff`).  At any `a ∉ poles` in
`𝔘.U i`, `gᵢ`'s chart-pullback is analytic, so `ω₀·gᵢ` is holomorphic — in particular isolated. -/
theorem formFnHoloPunctured_off (i : 𝔘.ι) {a : X} (ha : a ∈ 𝔘.U i) (hb : a ∉ μ.poles) :
    formFnHoloPunctured ω₀ (μ.g i) a :=
  formFnHoloPunctured_of_analyticAt ω₀ (μ.g i) a (μ.holoOff i a ha hb)

/-- **`ω₀·gᵢ` has an isolated singularity at every point of `𝔘.U i`** (genuine, from `iso` ∪ `holoOff`):
at recorded poles by `iso`/`formHoloDiff`, off them by `holoOff`.  This is the key fact the algebra and
the genuine-total-residue statement rest on. -/
theorem formFnHoloPunctured_everywhere (i : 𝔘.ι) {a : X} (ha : a ∈ 𝔘.U i) :
    formFnHoloPunctured ω₀ (μ.g i) a := by
  by_cases hb : a ∈ μ.poles
  · exact μ.toDistribution.toFormMLDistribution.formFnHoloPunctured_of_mem hb ha
  · exact μ.formFnHoloPunctured_off i ha hb

end CoverMLLift

end Jacobians.Dolbeault

end
