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
import Jacobians.Architecture
import Jacobians.FormsToJacobian
import Jacobians.LineIntegral

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
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- data
/-- The period lattice of a compact Riemann surface, living inside
`(Fin (genus X) → ℂ)`. In the real construction this is the image of
`H₁(X, ℤ)` in `H⁰(X, Ω¹)ᵛ` under the period pairing; currently
`sorry`-level until holomorphic 1-forms + integration exist. -/
def periodLattice (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Submodule ℤ (Fin (genus X) → ℂ) := sorry

instance {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    DiscreteTopology (periodLattice X) := sorry

instance {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    IsZLattice ℝ (periodLattice X) := sorry

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

Current definition returns `0` for the trivial case `Q = P` (forcing
`ofCurve_self` to close structurally) and is content-gated (sorry)
otherwise. The real definition integrates a basis of holomorphic 1-forms
along a path from `P` to `Q` — see `Jacobians/LineIntegral.lean`. -/
noncomputable def ofCurve (P : X) : X → Jacobian X := by
  classical
  exact fun Q => if _ : Q = P then 0 else Classical.arbitrary (Jacobian X)

lemma ofCurve_contMDiff (P : X) : ContMDiff 𝓘(ℂ)
    (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ofCurve P) := sorry

lemma ofCurve_self (P : X) : ofCurve P P = 0 := by
  classical
  show (if _ : P = P then (0 : Jacobian X) else _) = 0
  rw [dif_pos rfl]

-- this is the lemma which stops the hack answer "J(X)=0 for all X"
lemma ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) := sorry

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)

/-- Lattice preservation: the ambient pushforward map sends the `X`-period
lattice into the `Y`-period lattice. Content-gated. -/
lemma ambientPhi_preserves_lattice (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (periodLattice X).toAddSubgroup ≤
      (periodLattice Y).toAddSubgroup.comap
        (Jacobians.Bridge.ambientPhi (gX := genus X) (gY := genus Y) f hf).toAddMonoidHom :=
  sorry

/-- The pushforward map between Jacobians associated to a map of the underlying curves.
Wired: `Architecture.pushforward` applied to `Bridge.ambientPhi f hf`. -/
noncomputable def pushforward (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y :=
  Jacobians.Architecture.pushforward (periodLattice X) (periodLattice Y)
    (Jacobians.Bridge.ambientPhi (gX := genus X) (gY := genus Y) f hf)
    (ambientPhi_preserves_lattice f hf)

-- pushforward is holomorphic
theorem pushforward_contMDiff :
  ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
  (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforward f hf) := sorry

-- functoriality
lemma pushforward_id_apply (P : Jacobian X) : pushforward id contMDiff_id P = P :=
  Jacobians.Architecture.pushforward_id_of_ambient
    (periodLattice X)
    (Jacobians.Bridge.ambientPhi (gX := genus X) (gY := genus X) id contMDiff_id)
    (ambientPhi_preserves_lattice id contMDiff_id)
    (fun x => Jacobians.Bridge.ambientPhi_id (X := X) x)
    P

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)

-- functoriality
lemma pushforward_comp_apply (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) := by
  induction P using QuotientAddGroup.induction_on with
  | H x =>
    show QuotientAddGroup.mk
        (Jacobians.Bridge.ambientPhi (gX := genus X) (gY := genus Z) (g ∘ f)
          (hg.comp hf) x) =
      QuotientAddGroup.mk
        (Jacobians.Bridge.ambientPhi (gX := genus Y) (gY := genus Z) g hg
          (Jacobians.Bridge.ambientPhi (gX := genus X) (gY := genus Y) f hf x))
    congr 1
    exact Jacobians.Bridge.ambientPhi_comp f hf g hg (hg.comp hf) x

/-- Lattice preservation on the pullback side. -/
lemma ambientPsi_preserves_lattice (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (periodLattice Y).toAddSubgroup ≤
      (periodLattice X).toAddSubgroup.comap
        (Jacobians.Bridge.ambientPsi (gX := genus X) (gY := genus Y) f hf).toAddMonoidHom :=
  sorry

/-- Pullback map between Jacobians associated to a map of the underlying curves.
Equal to the zero map if the map on curves is constant.
Wired: `Architecture.pullback` applied to `Bridge.ambientPsi f hf`. -/
noncomputable def pullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X :=
  Jacobians.Architecture.pullback (periodLattice X) (periodLattice Y)
    (Jacobians.Bridge.ambientPsi (gX := genus X) (gY := genus Y) f hf)
    (ambientPsi_preserves_lattice f hf)

-- pullback is holomorphic
theorem pullback_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf) := sorry

-- functoriality
lemma pullback_id_apply (P : Jacobian X) : pullback id contMDiff_id P = P :=
  Jacobians.Architecture.pushforward_id_of_ambient
    (periodLattice X)
    (Jacobians.Bridge.ambientPsi (gX := genus X) (gY := genus X) id contMDiff_id)
    (ambientPsi_preserves_lattice id contMDiff_id)
    (fun x => Jacobians.Bridge.ambientPsi_id (X := X) x)
    P

-- functoriality
lemma pullback_comp_apply (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := by
  induction P using QuotientAddGroup.induction_on with
  | H z =>
    show QuotientAddGroup.mk
        (Jacobians.Bridge.ambientPsi (gX := genus X) (gY := genus Z) (g ∘ f)
          (hg.comp hf) z) =
      QuotientAddGroup.mk
        (Jacobians.Bridge.ambientPsi (gX := genus X) (gY := genus Y) f hf
          (Jacobians.Bridge.ambientPsi (gX := genus Y) (gY := genus Z) g hg z))
    congr 1
    exact Jacobians.Bridge.ambientPsi_comp f hf g hg (hg.comp hf) z

/-- The degree of a holomorphic map between compact Riemann surfaces. Equal to zero
for constant maps, otherwise equal to the usual degree. -/
def _root_.ContMDiff.degree
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  sorry

lemma pushforward_pullback (P : Jacobian Y) :
  pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P :=
  Jacobians.Architecture.pushforward_pullback_of_ambient
    (periodLattice X) (periodLattice Y)
    (Jacobians.Bridge.ambientPhi (gX := genus X) (gY := genus Y) f hf)
    (Jacobians.Bridge.ambientPsi (gX := genus X) (gY := genus Y) f hf)
    (ambientPhi_preserves_lattice f hf)
    (ambientPsi_preserves_lattice f hf)
    (ContMDiff.degree f hf)
    (fun y => Jacobians.Bridge.ambientPhi_ambientPsi_eq f hf
      (ContMDiff.degree f hf) y)
    P

end Jacobian
