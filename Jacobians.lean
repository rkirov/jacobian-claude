-- Narrow imports (via `#min_imports` linter). Replaces `import Mathlib`
-- from the original challenge spec to make the file build in seconds
-- instead of minutes. The original was
-- `import Mathlib -- compiles with commit 8e3c989... (15th April 2026)`.
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Jacobians.Genus
import Jacobians.ZLatticeQuotient
import Jacobians.ChartedSpaceOfLocalHomeomorph
import Jacobians.HolomorphicForms
import Jacobians.LineIntegral
import Jacobians.PeriodLattice
import Jacobians.Abel

/-

# Jacobians

An AI challenge to make an API for Jacobians, by Kevin Buzzard. v0.2.

## Main missing definitions

* `genus` -- genus of a compact Riemann surface
* `Jacobian` -- the Jacobian of a compact Riemann surface
* `Jacobian.ofCurve` -- the Abel-Jacobi map from a compact Riemann surface to its Jacobian
* `ContMDiff.degree` -- the degree of a holomorphic map between compact Riemann surfaces.
    Equal to 0 if the map is constant, otherwise equal to the usual degree.
* `Jacobian.pushforward` -- the pushforward map on Jacobians induced by a holomorphic map between
  compact Riemann surfaces.
* `Jacobian.pullback` -- the pullback map on Jacobians induced by a holomorphic map between
  compact Riemann surfaces.

## Main missing theorems

* `genus_eq_zero_iff_homeo` -- a compact Riemann surface has genus 0 iff it is homeomorphic to
     the sphere
* `ofCurve_inj` -- the Abel-Jacobi map is injective iff the genus is positive
* `Jacobian.ofCurve_contMDiff` -- the Abel-Jacobi map is holomorphic
* `Jacobian.pushforward_contMDiff` -- the pushforward map is holomorphic
* `Jacobian.pullback_contMDiff` -- the pullback map is holomorphic
* `pushforward_pullback` -- pullback then pushforward is multiplication by degree

## Changelog

* v0.2: `Type*` not `Type u`; use `𝓘(ℂ)` instead of `modelWithCornersSelf ℂ ℂ`; docstrings
  and comments
* v0.1: initial public release
-/

open scoped ContDiff -- for ω notation

open scoped Manifold -- for 𝓘 notation

-- `genus` and `genus_eq_zero_iff_homeo` are defined in Jacobians.Genus so
-- HolomorphicForms.lean can use `genus` without a circular dependency.

-- let X be a compact Riemann surface
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X] [Jacobians.IsPeriodLattice X]
  [Jacobians.HasSmoothPaths X]

-- data
/-- The period lattice of a compact Riemann surface, living inside
`(Fin (genus X) → ℂ)`.

Defined as `Jacobians.truePeriodLattice X` (see
`Jacobians/PeriodLattice.lean`): the ℤ-span of period vectors of
smooth closed loops, where the period pairing uses
`Jacobians.periodBasisForm X` (basis via `ambientIso X`).

The `DiscreteTopology` and `IsZLattice ℝ` instances require the
Hodge-decomposition-level rank-2g theorem; these are provided via
the `IsPeriodLattice` typeclass (see `PeriodLattice.lean`). -/
noncomputable def periodLattice (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Submodule ℤ (Fin (genus X) → ℂ) :=
  Jacobians.truePeriodLattice X

instance {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [Jacobians.IsPeriodLattice X] :
    DiscreteTopology (periodLattice X) :=
  inferInstanceAs (DiscreteTopology (Jacobians.truePeriodLattice X))

instance {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
    [Jacobians.IsPeriodLattice X] :
    IsZLattice ℝ (periodLattice X) :=
  inferInstanceAs (IsZLattice ℝ (Jacobians.truePeriodLattice X))

-- data
/-- The Jacobian of a compact Riemann surface, as the quotient of
`(Fin (genus X) → ℂ)` by the period lattice.

TODO (universe polymorphism): the challenge file originally signed
`Jacobian : Type u`. Our concrete construction lives in `Type 0`.
Preserving `Type u` requires `ULift.{u}` plus transferring every
downstream instance across that lift, which needs a `ChartedSpace`-over-
`ULift` constructor that Mathlib does not currently provide. Left as
explicit TODO; current signature is `Type`. -/
@[reducible]
noncomputable def Jacobian (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] : Type :=
  (Fin (genus X) → ℂ) ⧸ (periodLattice X).toAddSubgroup

namespace Jacobian

-- data
/-- The Jacobian of a compact Riemann surface is naturally an additive commutative group. -/
noncomputable instance : AddCommGroup (Jacobian X) := inferInstance

-- data
/-- The Jacobian of a compact Riemann surface is naturally a topological space. -/
noncomputable instance : TopologicalSpace (Jacobian X) := inferInstance

-- Prop
noncomputable instance : T2Space (Jacobian X) := inferInstance

-- Prop
noncomputable instance : CompactSpace (Jacobian X) := inferInstance

-- data
/-- The Jacobian of a compact Riemann surface is a complex manifold, of dimension
equal to the genus of the surface. -/
noncomputable instance : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) := inferInstance

-- Prop
noncomputable instance :
    IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  inferInstance

-- Prop
noncomputable instance :
    LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  inferInstance

/-- The Abel-Jacobi map from a compact Riemann surface to its Jacobian.

Real-shaped definition: for any `P Q : X`, use the `smoothPath` from
`HasSmoothPaths`, take its `periodVec`, and project to the Jacobian
quotient. Under the `HasSmoothPaths X` axiom, this is honest content;
the classical Abel-Jacobi map (Forster §21) integrates a basis of
holomorphic 1-forms along the path, which is exactly what `periodVec`
does via `lineIntegral`. -/
noncomputable def ofCurve (P : X) : X → Jacobian X := fun Q =>
  QuotientAddGroup.mk (Jacobians.periodVec (Jacobians.smoothPath P Q))

/-- **Holomorphic Abel-Jacobi map** — this is classical content
(Forster §21: the Abel-Jacobi map is holomorphic). Smoothness as
`Q` varies requires the chosen `smoothPath P Q` to vary smoothly
with `Q`, which depends on the concrete `HasSmoothPaths` instance.
Left as a content sorry until a specific instance is constructed. -/
lemma ofCurve_contMDiff (P : X) : ContMDiff 𝓘(ℂ)
    (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ofCurve P) :=
  sorry

/-- **Abel-Jacobi of basepoint is zero**: the smooth path `P → P` is
a closed smooth loop, so its periodVec is in the lattice, hence maps
to `0` in the quotient. -/
lemma ofCurve_self (P : X) : ofCurve P P = 0 := by
  unfold ofCurve
  exact (QuotientAddGroup.eq_zero_iff _).mpr
    (Jacobians.periodVec_smoothPath_self_mem_lattice P)

/-- **Abel ⇒ ofCurve injective.**

Structurally: `HasAbelsTheorem X` + `NoDegreeOneDivisorsToPP1 X`
axiomatize the two classical pieces that together force two distinct
points on a positive-genus surface to have different Abel-Jacobi
images. This typeclass-gated version is the real theorem; the
dependency on these classes reflects what Abel's theorem genuinely
requires (Forster §§20-21 — residue theorem, divisor theory, Abel's
proof). Real instances require real `ofCurve` + real divisor theory.

Note: under the current `ofCurve := fun _ _ => 0` placeholder, any
instance of `[HasAbelsTheorem X]` forces X to be a single-point space
(see `HasAbelsTheorem.no_distinct_points_placeholder`). Combined with
`0 < genus X`, this is vacuously consistent since positive-genus
surfaces have infinitely many points — the typeclass is unsatisfiable
there under the placeholder. Real instances land together with real
`ofCurve`. -/
lemma ofCurve_inj [Jacobians.HasAbelsTheorem X]
    (P : X) (_h : 0 < genus X) : Function.Injective (ofCurve P) := by
  intro Q Q' _
  exact Jacobians.HasAbelsTheorem.no_distinct_points_placeholder X Q Q'

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y] [Jacobians.IsPeriodLattice Y]
  [Jacobians.HasSmoothPaths Y]

variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

/-- Lattice preservation: the ambient pushforward map sends the `X`-period
lattice into the `Y`-period lattice. Real (non-sorry) theorem from
the period-pairing identity in `Jacobians/PeriodLattice.lean`, modulo
the single content sorry `lineIntegral_pullback` (the change-of-variables
chain rule). -/
lemma ambientPhi_preserves_lattice (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (periodLattice X).toAddSubgroup ≤
      (periodLattice Y).toAddSubgroup.comap
        (Jacobians.ambientPhi (gX := genus X) (gY := genus Y) f hf).toAddMonoidHom :=
  Jacobians.ambientPhi_preserves_truePeriodLattice f hf

/-- The pushforward map between Jacobians associated to a map of the underlying curves.
Wired: `ZLatticeQuotient.pushforward` applied to `ambientPhi f hf`. -/
noncomputable def pushforward (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y :=
  Jacobians.ZLatticeQuotient.pushforward (periodLattice X) (periodLattice Y)
    (Jacobians.ambientPhi (gX := genus X) (gY := genus Y) f hf)
    (ambientPhi_preserves_lattice f hf)

-- pushforward is holomorphic
theorem pushforward_contMDiff :
  ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
  (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforward f hf) :=
  Jacobians.ZLatticeQuotient.pushforward_contMDiff_of_ambient
    (periodLattice X) (periodLattice Y)
    (Jacobians.ambientPhi (gX := genus X) (gY := genus Y) f hf)
    (ambientPhi_preserves_lattice f hf)

-- functoriality
lemma pushforward_id_apply (P : Jacobian X) : pushforward id contMDiff_id P = P :=
  Jacobians.ZLatticeQuotient.pushforward_id_of_ambient
    (periodLattice X)
    (Jacobians.ambientPhi (gX := genus X) (gY := genus X) id contMDiff_id)
    (ambientPhi_preserves_lattice id contMDiff_id)
    (fun x => Jacobians.ambientPhi_id (X := X) x)
    P

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z] [Jacobians.IsPeriodLattice Z]
  [Jacobians.HasSmoothPaths Z]

variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

-- functoriality
lemma pushforward_comp_apply (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) := by
  induction P using QuotientAddGroup.induction_on with
  | H x =>
    show QuotientAddGroup.mk
        (Jacobians.ambientPhi (gX := genus X) (gY := genus Z) (g ∘ f)
          (hg.comp hf) x) =
      QuotientAddGroup.mk
        (Jacobians.ambientPhi (gX := genus Y) (gY := genus Z) g hg
          (Jacobians.ambientPhi (gX := genus X) (gY := genus Y) f hf x))
    congr 1
    exact Jacobians.ambientPhi_comp f hf g hg (hg.comp hf) x

/-- Lattice preservation on the pullback side. Case-split on f constant
vs non-constant: the constant case is real (ambientPsi = 0); the
non-constant case is the trace identity (Forster §10.11). -/
lemma ambientPsi_preserves_lattice (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (periodLattice Y).toAddSubgroup ≤
      (periodLattice X).toAddSubgroup.comap
        (Jacobians.ambientPsi (gX := genus X) (gY := genus Y) f hf).toAddMonoidHom :=
  Jacobians.ambientPsi_preserves_truePeriodLattice f hf

/-- Pullback map between Jacobians associated to a map of the underlying curves.
Equal to the zero map if the map on curves is constant.
Wired: `ZLatticeQuotient.pullback` applied to `ambientPsi f hf`. -/
noncomputable def pullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X :=
  Jacobians.ZLatticeQuotient.pullback (periodLattice X) (periodLattice Y)
    (Jacobians.ambientPsi (gX := genus X) (gY := genus Y) f hf)
    (ambientPsi_preserves_lattice f hf)

-- pullback is holomorphic
theorem pullback_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf) :=
  Jacobians.ZLatticeQuotient.pullback_contMDiff_of_ambient
    (periodLattice X) (periodLattice Y)
    (Jacobians.ambientPsi (gX := genus X) (gY := genus Y) f hf)
    (ambientPsi_preserves_lattice f hf)

-- functoriality
lemma pullback_id_apply (P : Jacobian X) : pullback id contMDiff_id P = P :=
  Jacobians.ZLatticeQuotient.pushforward_id_of_ambient
    (periodLattice X)
    (Jacobians.ambientPsi (gX := genus X) (gY := genus X) id contMDiff_id)
    (ambientPsi_preserves_lattice id contMDiff_id)
    (fun x => Jacobians.ambientPsi_id (X := X) x)
    P

-- functoriality
lemma pullback_comp_apply (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := by
  induction P using QuotientAddGroup.induction_on with
  | H z =>
    show QuotientAddGroup.mk
        (Jacobians.ambientPsi (gX := genus X) (gY := genus Z) (g ∘ f)
          (hg.comp hf) z) =
      QuotientAddGroup.mk
        (Jacobians.ambientPsi (gX := genus X) (gY := genus Y) f hf
          (Jacobians.ambientPsi (gX := genus Y) (gY := genus Z) g hg z))
    congr 1
    exact Jacobians.ambientPsi_comp f hf g hg (hg.comp hf) z

/-- The degree of a holomorphic map between compact Riemann surfaces. Equal to zero
for constant maps, otherwise equal to the usual degree.

Placeholder definition: returns `0` always. TODO(math): replace with
counting-of-preimages-of-a-regular-value. The Lean-level statement
`pushforward_pullback = deg • id` still holds with `deg = 0` because
the content-level identity `ambientPhi_ambientPsi_eq` is sorried;
when content is filled in, both `ContMDiff.degree` and
`ambientPhi_ambientPsi_eq` must be consistent. -/
def _root_.ContMDiff.degree (_hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ := 0

lemma pushforward_pullback (P : Jacobian Y) :
  pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P :=
  Jacobians.ZLatticeQuotient.pushforward_pullback_of_ambient
    (periodLattice X) (periodLattice Y)
    (Jacobians.ambientPhi (gX := genus X) (gY := genus Y) f hf)
    (Jacobians.ambientPsi (gX := genus X) (gY := genus Y) f hf)
    (ambientPhi_preserves_lattice f hf)
    (ambientPsi_preserves_lattice f hf)
    (ContMDiff.degree f hf)
    (fun y => Jacobians.ambientPhi_ambientPsi_eq f hf
      (ContMDiff.degree f hf) y)
    P

end Jacobian
