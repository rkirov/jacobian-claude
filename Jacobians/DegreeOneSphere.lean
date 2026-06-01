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

set_option linter.unusedSectionVars false in
/-- Every charted space over `ℂ` is nontrivial at each point: there is always a
second point.  Proof: the chart `e` at `P` is an open embedding into `ℂ`; its
target is a nonempty open set, which cannot be the singleton `{e P}` (singletons
are not open in `ℂ`), so it contains some `w ≠ e P`, whose preimage `e.symm w`
differs from `P`. -/
theorem exists_ne_of_chartedSpace_complex (P : X) : ∃ x : X, x ≠ P := by
  set e := chartAt ℂ P with he
  have hPsrc : P ∈ e.source := mem_chart_source ℂ P
  have hPtgt : e P ∈ e.target := e.map_source hPsrc
  have hne : e.target ≠ {e P} := by
    intro hsingle
    exact (not_isOpen_singleton (e P)) (hsingle ▸ e.open_target)
  obtain ⟨w, hw, hwne⟩ : ∃ w ∈ e.target, w ≠ e P := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    exact hne (Set.eq_singleton_iff_unique_mem.mpr ⟨hPtgt, hcon⟩)
  refine ⟨e.symm w, fun hcontra => hwne ?_⟩
  have : e (e.symm w) = e P := by rw [hcontra]
  rwa [e.right_inv hw] at this

/-- `toSphere` is non-constant: it takes the value `∞` (at `P`) and a finite value
`coe (f x)` at any `x ≠ P` (such an `x` exists by
`exists_ne_of_chartedSpace_complex`), and `coe (f x) ≠ ∞`.  This uses the genuine
`IsConstantMap` predicate (`∃ c, ∀ x, f x = c`), which is non-vacuous since `X` is
nonempty. -/
theorem MeromorphicFunction.toSphere_not_isConstant (f : MeromorphicFunction X)
    {P : X} (_hP : f.HasSingleSimplePole P) :
    ¬ IsConstantMap (f.toSphere P) := by
  rintro ⟨c, hc⟩
  obtain ⟨x, hx⟩ := exists_ne_of_chartedSpace_complex (X := X) P
  -- `f.toSphere P x = c` and `f.toSphere P P = c`, so `coe (f x) = ∞`, impossible.
  have hxv : f.toSphere P x = ((f.toFun x : ℂ) : RiemannSphere) := f.toSphere_of_ne hx
  have key : ((f.toFun x : ℂ) : RiemannSphere) = OnePoint.infty := by
    rw [← hxv, hc x, ← f.toSphere_pole P, hc P]
  exact (OnePoint.coe_ne_infty _) key

/-! ### Step 2 — degree one -/

/-- **The pole is a regular point of `F = toSphere f P`** (Step 2's analytic core,
and the genuine consumer of *simplicity*).  Reading `F` near `P` in the `∞`-chart,
`F` is `z ↦ 1/f` whose derivative at `P` is nonzero **precisely because the pole is
simple** (`orderAtPoint P = -1`): a double pole would give a vanishing derivative
here (chart-pullback `z ↦ z²`-shaped), so its fibre-degree would be `2`, not `1`.
This is the chart-pullback-derivative-nonzero certificate the regular-witness
bundle (`RegularValueWitnessReg.is_regular`) requires at the unique preimage `P` of
`∞`.

This is the same analytic local-normal-form content as `contMDiff_toSphere`, here
specialized to the first-derivative non-vanishing at the simple pole; isolated as a
single documented residual. -/
theorem MeromorphicFunction.toSphere_regular_at_pole (f : MeromorphicFunction X)
    {P : X} (hP : f.HasSingleSimplePole P) :
    ∀ x ∈ (f.toSphere P) ⁻¹' {OnePoint.infty},
      deriv ((chartAt ℂ (OnePoint.infty : RiemannSphere)) ∘ (f.toSphere P) ∘
          (chartAt ℂ x).symm) ((chartAt ℂ x) x) ≠ 0 := by
  sorry

/-- **Degree one** (Step 2).  `∞` is a regular value of `F = toSphere f P` with the
single preimage `P` (`toSphere_preimage_infty`), and `P` is a regular point
(`toSphere_regular_at_pole`, consuming pole simplicity).  Packaging this as a
`RegularValueWitnessReg` whose fibre `{P}` has cardinality `1`, witness-independence
of the fibre degree (`degreeFiber_eq_card_of_regularWitness`) gives
`degreeFiber F hF = 1`.

Note the genuine use of simplicity: the `RegularValueWitnessReg.is_regular`
certificate fed in here is `toSphere_regular_at_pole`, which *fails* for a higher-
order pole.  A double pole has the same singleton preimage `{P}` but is a critical
point, so it would not yield a regular witness — and indeed its topological degree
is `2`, not `1`. -/
theorem MeromorphicFunction.degreeFiber_toSphere_eq_one (f : MeromorphicFunction X)
    {P : X} (hP : f.HasSingleSimplePole P)
    (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (f.toSphere P)) :
    degreeFiber (f.toSphere P) hF = 1 := by
  classical
  -- The regular-value witness at `∞`, with fibre `{P}` and the simplicity certificate.
  set F := f.toSphere P with hFdef
  have hfib : F ⁻¹' {OnePoint.infty} = {P} := f.toSphere_preimage_infty P
  have hfin : (F ⁻¹' {OnePoint.infty}).Finite := by rw [hfib]; exact Set.finite_singleton P
  -- underlying cardinality-bearing witness
  let w₀ : RegularValueWitness F :=
    { value := OnePoint.infty, fiber_finite := hfin }
  -- promote to a regular witness using the simple-pole regularity certificate
  let w : RegularValueWitnessReg F :=
    w₀.toRegular (f.toSphere_regular_at_pole hP)
  -- non-constancy
  have hnc : ¬ IsConstantMap F := f.toSphere_not_isConstant hP
  -- witness independence pins the degree to this witness's card …
  have hdeg : degreeFiber F hF = w.card :=
    degreeFiber_eq_card_of_regularWitness F hF hnc w
  rw [hdeg]
  -- … and that card is `(F⁻¹{∞}).ncard = |{P}| = 1`.
  show (Jacobians.Discharge.ContMDiff.RegularValueWitnessReg.card w) = 1
  have hcard : w.card = (F ⁻¹' {OnePoint.infty}).ncard :=
    w₀.card_eq_ncard
  rw [show (Jacobians.Discharge.ContMDiff.RegularValueWitnessReg.card w) = w.card from rfl,
    hcard, hfib, Set.ncard_singleton]

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

/-! ### The challenge theorem `genus_eq_zero_iff_homeo`

Declared in the **root namespace** (matching `genus`, which lives in root namespace in `Genus.lean`),
so the challenge-conformance file resolves the bare name. Lives in this module — not `Genus.lean` —
because its forward direction needs the degree-one endgame, which sits downstream of `Genus` (via
`ProjectiveLine → Genus`); declaring it here breaks the import cycle. Both directions rest on isolated
analytic inputs (the `sorry`s below). `Nonempty X` is supplied for free by `[ConnectedSpace X]`
(`ConnectedSpace.toNonempty`), so the signature matches the spec exactly. -/

open scoped Manifold ContDiff in
/-- **[INPUT — Riemann–Roch consequence `l(P) = 2`].** Genus `0` yields a meromorphic function with a
single simple pole (Forster §16: `l(P) = deg P + 1 − g + l(K−P) = 1 + 1 − 0 + 0 = 2`). The genuine RR
content, resting on the Dolbeault/Serre wall. -/
theorem exists_singleSimplePole_of_genus_zero {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (h : genus X = 0) :
    ∃ (P : X) (f : Jacobians.MeromorphicFunction X), f.HasSingleSimplePole P :=
  sorry

open scoped Manifold ContDiff in
/-- **[INPUT — `Ω(ℂℙ¹) = 0`, the backward half].** A surface homeomorphic to `S²` has genus `0`.
Genus is `Module.finrank ℂ (HolomorphicOneForms X)`; for the sphere this vanishes
(`ProjectiveLine.holomorphicOneForm_eq_zero`), and the value is an invariant of the complex
structure. -/
theorem genus_zero_of_nonempty_homeo_sphere {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    genus X = 0 :=
  sorry

open scoped Manifold ContDiff in
/-- A compact Riemann surface has genus `0` iff it is homeomorphic to the `2`-sphere — the challenge
theorem (the "anti-hack" constraint preventing `∀ X, genus X = 0`).

The **forward** direction is the genuine content: genus `0` ⟹ a single-simple-pole meromorphic
function (`exists_singleSimplePole_of_genus_zero`, Riemann–Roch) ⟹ a degree-1 map `X → ℂℙ¹` ⟹
`X ≃ₜ S²` (`Jacobians.nonempty_homeo_sphere_of_singleSimplePole`, the degree-one endgame). The
**backward** direction is `Ω(ℂℙ¹) = 0` (`genus_zero_of_nonempty_homeo_sphere`). -/
theorem genus_eq_zero_iff_homeo {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  ⟨fun h => by
    obtain ⟨P, f, hP⟩ := exists_singleSimplePole_of_genus_zero h
    exact Jacobians.nonempty_homeo_sphere_of_singleSimplePole f hP,
   genus_zero_of_nonempty_homeo_sphere⟩
