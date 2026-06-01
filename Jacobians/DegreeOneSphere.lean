/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.ProjectiveLine
import Jacobians.Degree
import Jacobians.Abel

/-!
# Degree-one ⟹ sphere endgame

Let `X` be a compact connected Riemann surface and `f : X → ℂ` a meromorphic
function with a **single simple pole** at `P` (`orderAtPoint P = -1` and
`0 ≤ orderAtPoint x` for `x ≠ P`).  Then `X` is homeomorphic to the Euclidean
`2`-sphere `S² ⊆ ℝ³`.

This is the classical "a degree-one map of compact Riemann surfaces is a
biholomorphism" run in the special case of `f : X → ℂℙ¹`, cashing in the
`ℂℙ¹`-shim built in `Jacobians.ProjectiveLine`:

1. **Build the map** `F : X → RiemannSphere` (`= OnePoint ℂ`): `F x = (f x : ℂℙ¹)`
   for `x ≠ P`, `F P = ∞`.  `F` is holomorphic (`ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω`): off `P`
   it is `coe ∘ f`; at `P`, read in `chartInfty` it is `z ↦ 1/f`, which is
   holomorphic with value `0` because the pole is simple.
2. **Degree 1**: `F⁻¹(∞) = {P}`, and `∞` is a regular value with one preimage, so
   `degreeFiber F _ = 1`.
3. **Degree-1 ⟹ homeomorphism**: a non-constant degree-1 holomorphic map between
   compact connected Riemann surfaces is bijective and a local biholomorphism,
   hence a homeomorphism `X ≃ₜ RiemannSphere`.
4. **Compose** with `RiemannSphere.homeoSphere : RiemannSphere ≃ₜ S²`.

## References

* Forster, *Lectures on Riemann Surfaces*, §§4–5 (proper holomorphic maps, the
  degree, degree-one ⟹ biholomorphism).
* Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. II §4.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open OnePoint Complex

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The simple-pole predicate

We define the predicate inline (the goal theorem must not depend on
`Jacobians.Roadmap`).  A meromorphic function `f` has a *single simple pole* at
`P` when its order at `P` is `-1` and its order is `≥ 0` everywhere else. -/

/-- `f` has a **single simple pole** at `P`: order `-1` at `P` and order `≥ 0`
elsewhere. -/
def MeromorphicFunction.HasSingleSimplePole
    (f : MeromorphicFunction X) (P : X) : Prop :=
  f.orderAtPoint P = -1 ∧ ∀ x, x ≠ P → 0 ≤ f.orderAtPoint x

/-! ### Step 1 — the map to the Riemann sphere -/

open Classical in
/-- The map `X → ℂℙ¹` associated with a meromorphic function `f` and a chosen
pole `P`: send finite points through `f` (composed with `ℂ ↪ ℂℙ¹`) and `P` to
`∞`.  (We send *only* `P` to `∞`; with a single simple pole at `P` this is the
honest "graph" of `f`.) -/
def MeromorphicFunction.toSphere (f : MeromorphicFunction X) (P : X) :
    X → RiemannSphere :=
  fun x => if x = P then OnePoint.infty else ((f.toFun x : ℂ) : RiemannSphere)

@[simp] lemma MeromorphicFunction.toSphere_pole (f : MeromorphicFunction X) (P : X) :
    f.toSphere P P = OnePoint.infty := by
  simp [MeromorphicFunction.toSphere]

lemma MeromorphicFunction.toSphere_of_ne (f : MeromorphicFunction X) {P x : X}
    (hx : x ≠ P) :
    f.toSphere P x = ((f.toFun x : ℂ) : RiemannSphere) := by
  simp [MeromorphicFunction.toSphere, hx]

/-- Preimage of `∞` under `toSphere` is exactly `{P}` (since `coe` never hits `∞`
and we send only `P` to `∞`). -/
lemma MeromorphicFunction.toSphere_preimage_infty (f : MeromorphicFunction X) (P : X) :
    f.toSphere P ⁻¹' {OnePoint.infty} = {P} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    rw [f.toSphere_of_ne hne] at hx
    exact (OnePoint.coe_ne_infty _) hx
  · rintro rfl
    simp

/-- **Holomorphy of `toSphere`** (Step 1).  Off `P`, `toSphere = coe ∘ f`, which
is holomorphic where `f` is holomorphic (and `f` is holomorphic away from its
poles).  At `P`, reading in `chartInfty`, `toSphere` is `z ↦ 1/f`, which is
holomorphic with value `0` because the pole is simple (`orderAtPoint P = -1`).

The supporting facts needed here are:
* `f` is `MDifferentiable`/analytic on `{x | 0 ≤ orderAtPoint x}` (away from
  poles), giving holomorphy of `coe ∘ f` off `P`;
* `1/f` extends holomorphically over a simple pole with value `0`
  (`MeromorphicLiouville`-style local normal form), giving holomorphy in the
  `∞`-chart at `P`.

These are exactly the "meromorphic ⇒ holomorphic chart representative" bridges
isolated elsewhere in this development; we leave the analytic content as a single
documented sorry at this interface. -/
theorem MeromorphicFunction.contMDiff_toSphere (f : MeromorphicFunction X) {P : X}
    (hP : f.HasSingleSimplePole P) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (f.toSphere P) := by
  sorry

/-- `toSphere` is non-constant: it takes the value `∞` (at `P`) and finite values
(at any `x ≠ P`, which exist because removing a point from a connected — hence,
here, infinite — surface leaves something). -/
theorem MeromorphicFunction.toSphere_not_isConstant (f : MeromorphicFunction X)
    {P : X} (hP : f.HasSingleSimplePole P) :
    ¬ IsConstantMap (f.toSphere P) := by
  sorry

/-! ### Step 2 — degree one -/

/-- **Degree one** (Step 2).  `∞` is a regular value of `F = toSphere f P` with a
single preimage `P`, so the fibre-cardinality degree is `1`.  Uses
`degreeFiber_eq_card_of_regularWitness` with the witness at `∞`:
`F⁻¹(∞) = {P}` has cardinality `1`. -/
theorem MeromorphicFunction.degreeFiber_toSphere_eq_one (f : MeromorphicFunction X)
    {P : X} (hP : f.HasSingleSimplePole P)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (f.toSphere P)) :
    degreeFiber (f.toSphere P) hF = 1 := by
  sorry

/-! ### Step 3 — degree one ⟹ homeomorphism -/

/-- **Degree-one ⟹ homeomorphism** (Step 3, the crux).  A non-constant degree-one
holomorphic map `F : X → Y` between compact connected Riemann surfaces is
bijective and a local biholomorphism, hence a homeomorphism.

Sketch:
* **Surjective** — a non-constant holomorphic map between compact connected
  Riemann surfaces is open (`isOpenMap_of_nonconstant`) and closed (compact ⇒
  closed image into Hausdorff), so its image is clopen and nonempty, hence all of
  `Y` by connectedness (`surjective_of_nonconstant`).
* **Injective** — every fibre is finite, and for a degree-one map the generic
  fibre has one point; combined with no-branching-drop this forces every fibre to
  be a singleton.
* **Continuous inverse** — a continuous bijection from a compact space to a
  Hausdorff space is a homeomorphism (`Continuous.homeoOfEquivCompactToT2` /
  `Homeomorph.homeoOfContinuousOpen`).

The §3 cover/IFT machinery (`surjective_of_nonconstant`,
`isOpenMap_of_nonconstant`, local-inverse / fibre-finiteness) lives in
`Jacobians.TracePullback` / `Jacobians.ManifoldIFT`; assembling the
degree-one-forces-injective step from it is the substantive remaining work, left
as a single documented sorry. -/
theorem degreeOne_homeo {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω Y]
    (F : X → Y) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hnc : ¬ IsConstantMap F)
    (hdeg : degreeFiber F hF = 1) :
    Nonempty (X ≃ₜ Y) := by
  sorry

/-! ### The endgame theorem -/

/-- **Degree-one ⟹ sphere.**  If a meromorphic function `f` on a compact
connected Riemann surface `X` has a single simple pole at some `P`, then `X` is
homeomorphic to the Euclidean `2`-sphere `S² ⊆ ℝ³`.

Proof: `F := f.toSphere P : X → ℂℙ¹` is holomorphic (Step 1), non-constant, and
has degree `1` because `F⁻¹(∞) = {P}` (Step 2).  A degree-one holomorphic map of
compact connected Riemann surfaces is a homeomorphism (Step 3), so `X ≃ₜ ℂℙ¹`,
and `ℂℙ¹ ≃ₜ S²` via `RiemannSphere.homeoSphere` (Step 4). -/
theorem nonempty_homeo_sphere_of_singleSimplePole
    (f : MeromorphicFunction X) {P : X} (hP : f.HasSingleSimplePole P) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  -- Step 1: the holomorphic map to ℂℙ¹.
  have hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (f.toSphere P) := f.contMDiff_toSphere hP
  have hnc : ¬ IsConstantMap (f.toSphere P) := f.toSphere_not_isConstant hP
  -- Step 2: degree one.
  have hdeg : degreeFiber (f.toSphere P) hF = 1 :=
    f.degreeFiber_toSphere_eq_one hP hF
  -- Step 3: degree-one ⟹ homeomorphism X ≃ₜ ℂℙ¹.
  obtain ⟨e⟩ := degreeOne_homeo (f.toSphere P) hF hnc hdeg
  -- Step 4: compose with ℂℙ¹ ≃ₜ S².
  exact ⟨e.trans RiemannSphere.homeoSphere⟩

end Jacobians
