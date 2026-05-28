/-
Ported from `JacobianChallenge.Manifold.Degree` of
<https://github.com/Brsanch/jacobian-lean-challenge> (MIT license,
Copyright (c) 2026 Bryan Sanchez), commit pushed 2026-05-27 at
Mathlib pin `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`.

Audit: `#print axioms JacobianChallenge.ContMDiff.degreeFiber` =
`[propext, Classical.choice, Quot.sound]` (kernel-clean); see
`docs/EXTERNAL_AUDIT.md`. This file is a minimal narrow port of the
structures and the definition itself — none of the auxiliary
`Owed.*` statements or structural-reduction lemmas are ported; they
live in the source repo for anyone who wants the full discharge
chain (16 files, ~4k LOC).
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# Degree of a holomorphic map between compact Riemann surfaces

Provides `Jacobians.degreeFiber f hf : ℕ`, a fibre-cardinality candidate
for `ContMDiff.degree`. Returns:

* `0` for constant maps;
* the cardinality of *some* regular fibre (extracted via `Classical.choice`
  on `Nonempty (RegularValueWitnessReg f)`) for non-constant maps;
* `0` again as fallback if no `RegularValueWitnessReg` instance is in scope.

At this Mathlib pin no proof of `Nonempty (RegularValueWitnessReg f)`
for non-constant analytic `f` is supplied — discharging it requires
the chart-local identity theorem + fibres-finite + regular-value-exists
chain (Forster §I.7), which is ~4k LOC of analytic infrastructure.
Until that lands, `degreeFiber f hf` evaluates to `0` for every input,
matching the old `ContMDiff.degree := 0` placeholder *in value* but
with the correct *shape*, so callers (`pushforward_pullback`,
`ambientPhi_ambientPsi_eq`) now state the right trace identity rather
than a vacuous `0 • P` one.
-/

namespace Jacobians

open scoped Manifold ContDiff

universe u v

/-- `f` is constant if every output equals some fixed `y`. Inlined from
`JacobianChallenge.IsConstantMap`. -/
def IsConstantMap {X : Type u} {Y : Type v} (f : X → Y) : Prop := ∃ y, ∀ x, f x = y

/-- A `RegularValueWitness f` packages a chosen value `y₀ : Y` together
with a proof that the fibre `f ⁻¹' {y₀}` is finite.

For a non-constant holomorphic map between compact connected Riemann
surfaces, existence of such a witness is a classical theorem (identity
theorem ⇒ discrete fibres ⇒ finite by compactness). The witness itself
carries no analytic content beyond the fibre-finiteness. -/
structure RegularValueWitness {X : Type u} {Y : Type v} (f : X → Y) where
  /-- Chosen value in the codomain. -/
  value : Y
  /-- The fibre over the chosen value is finite. -/
  fiber_finite : (f ⁻¹' {value}).Finite

/-- Cardinality of the chosen finite fibre. -/
noncomputable def RegularValueWitness.card {X : Type u} {Y : Type v} {f : X → Y}
    (w : RegularValueWitness f) : ℕ :=
  w.fiber_finite.toFinset.card

/-- A **regular** regular-value witness for `f`: a `RegularValueWitness`
whose chosen value `y₀` is *not* a branch value, recorded as a
chart-pullback-derivative-nonzero certificate at every preimage point.

Cardinality of the fibre over a regular value equals the degree of `f`
(classical: at a regular value the local normal form `z ↦ z` makes every
preimage simple, so the fibre cardinality is the topological degree).
At a critical value the cardinality drops, so any "fibre cardinality is
the degree" statement quantifying over plain `RegularValueWitness` is
false — the regularity certificate is what makes it correct.

(In the source repo this structure is `RegularValueWitnessReg`, named
to distinguish it from the regularity-free `RegularValueWitness` above
that an earlier version of `degreeFiber` used.) -/
structure RegularValueWitnessReg
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (f : X → Y) where
  /-- Underlying (cardinality-bearing) witness. -/
  toWitness : RegularValueWitness f
  /-- The chosen value is regular: at every preimage point the
  chart-pullback of `f` has nonzero derivative. -/
  is_regular : ∀ x ∈ f ⁻¹' {toWitness.value},
    deriv ((chartAt ℂ toWitness.value) ∘ f ∘ (chartAt ℂ x).symm)
      ((chartAt ℂ x) x) ≠ 0

/-- Cardinality of the chosen finite fibre of a regular witness. -/
noncomputable def RegularValueWitnessReg.card
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (w : RegularValueWitnessReg f) : ℕ :=
  w.toWitness.card

/-- The chosen regular value. -/
def RegularValueWitnessReg.value
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    {f : X → Y} (w : RegularValueWitnessReg f) : Y :=
  w.toWitness.value

/-- The **degree** of an analytic map `f : X → Y` between compact
Riemann surfaces, as a fibre cardinality at a regular value.

* Constant `f` ⇒ `0`.
* Non-constant `f`, regular witness available ⇒ cardinality from the
  witness via `Classical.choice`.
* Non-constant `f`, no witness in scope ⇒ `0` (fallback). At the
  current Mathlib pin no witness-existence theorem is supplied, so this
  branch fires in practice — `degreeFiber f hf = 0` always for now.

Well-definedness (independence of the chosen witness) is classical and
not proved here. -/
noncomputable def degreeFiber
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    (f : X → Y) (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  open Classical in
  if IsConstantMap f then 0
  else
    if h : Nonempty (RegularValueWitnessReg f) then
      (Classical.choice h).card
    else 0

/-- `degreeFiber` matches the convention of returning `0` on constant
maps. -/
lemma degreeFiber_const
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hconst : IsConstantMap f) :
    degreeFiber f hf = 0 := by
  unfold degreeFiber
  simp [hconst]

/-- `degreeFiber` falls back to `0` when no regular witness is
classically available — matching the old `ContMDiff.degree := 0`
behaviour at the current Mathlib pin. -/
lemma degreeFiber_eq_zero_of_no_witness
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    {f : X → Y} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hwitness : IsEmpty (RegularValueWitnessReg f)) :
    degreeFiber f hf = 0 := by
  unfold degreeFiber
  by_cases hconst : IsConstantMap f
  · simp [hconst]
  · simp [hconst, not_nonempty_iff.mpr hwitness]

end Jacobians
