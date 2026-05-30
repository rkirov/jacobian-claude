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
import Jacobians.SmoothPathCore
import Jacobians.ManifoldIFT
import Jacobians.PeriodLattice
import Jacobians.TracePullback
import Jacobians.Abel
import Jacobians.Degree
import Jacobians.OfCurveAnalyticitySkeleton

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

set_option linter.unusedSectionVars false

open scoped ContDiff -- for ω notation

open scoped Manifold -- for 𝓘 notation

-- `genus` and `genus_eq_zero_iff_homeo` are defined in Jacobians.Genus so
-- HolomorphicForms.lean can use `genus` without a circular dependency.

-- let X be a compact Riemann surface
variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

-- data
/-- The period lattice of a compact Riemann surface, living inside
`(Fin (genus X) → ℂ)`.

Defined as `Jacobians.truePeriodLattice X` (see
`Jacobians/PeriodLattice.lean`): the ℤ-span of period vectors of
smooth closed loops, where the period pairing uses
`Jacobians.periodBasisForm X` (basis via `ambientIso X`).

The `DiscreteTopology` and `IsZLattice ℝ` instances require the
Hodge / Riemann-bilinear rank-2g theorem (Forster §§19–20, not yet in
Mathlib); they are supplied as unconditional `sorry` instances (S2/S3) in
`PeriodLattice.lean`, so the Jacobian-as-complex-torus structure rests on
them. -/
noncomputable def periodLattice (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] : Submodule ℤ (Fin (genus X) → ℂ) :=
  Jacobians.truePeriodLattice X

instance {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    DiscreteTopology (periodLattice X) :=
  inferInstanceAs (DiscreteTopology (Jacobians.truePeriodLattice X))

instance {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
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

/-- **Holomorphic Abel-Jacobi map** (Forster §21): `ofCurve P : X → Jacobian X`
is holomorphic.

**Proof structure (local-to-global via `localLift_contMDiffAt`).**
At each `Q₀ : X`:

* The vector-valued local lift `localLift Q₀ (periodVec (smoothPath P
  Q₀))` is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω` at `Q₀`
  (`Jacobians.OfCurveSkeleton.localLift_contMDiffAt`, PROVEN via the
  Morera-primitive + FTC + `AnalyticAt.contDiffAt` +
  `ContDiffAt.comp_contMDiffAt` chain).
* Composing with the smooth quotient projection
  `Jacobians.ZLatticeQuotient.contMDiff_mk`, this lands in
  `Jacobian X` as `ContMDiffAt`.
* On a chart neighborhood of `Q₀`, the quotient of the local lift
  agrees with `ofCurve P` (the
  `localLift_quotient_eq_ofCurve_eventually` sorry — classical path
  algebra via `periodVec_concat` + path-difference-is-closed-loop in
  the quotient).
* By `ContMDiffAt.congr_of_eventuallyEq`, `ofCurve P` is `ContMDiffAt`
  at `Q₀`.
* `ContMDiff = ∀ Q, ContMDiffAt` (Mathlib definitional). -/
lemma ofCurve_contMDiff (P : X) : ContMDiff 𝓘(ℂ)
    (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ofCurve P) := by
  intro Q₀
  -- Local lift at `Q₀` with `constants = periodVec(smoothPath P Q₀)`.
  have h_local : ContMDiffAt 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
      (Jacobians.OfCurveSkeleton.localLift (X := X) Q₀
        (Jacobians.periodVec (Jacobians.smoothPath P Q₀))) Q₀ :=
    Jacobians.OfCurveSkeleton.localLift_contMDiffAt Q₀ _
  -- Smooth quotient projection.
  have h_mk : ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
      (QuotientAddGroup.mk :
        (Fin (genus X) → ℂ) →
        (Fin (genus X) → ℂ) ⧸ (periodLattice X).toAddSubgroup) :=
    Jacobians.ZLatticeQuotient.contMDiff_mk (𝕜 := ℂ) (E := Fin (genus X) → ℂ)
      (Λ := periodLattice X) (n := ω)
  -- Composition: quotient of the local lift, ContMDiffAt at Q₀.
  have h_local_quotient : ContMDiffAt 𝓘(ℂ)
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
      (fun Q => (QuotientAddGroup.mk
        (Jacobians.OfCurveSkeleton.localLift (X := X) Q₀
          (Jacobians.periodVec (Jacobians.smoothPath P Q₀)) Q) :
        (Fin (genus X) → ℂ) ⧸ (periodLattice X).toAddSubgroup)) Q₀ :=
    (h_mk _).comp Q₀ h_local
  -- Local agreement with `ofCurve P` (via path algebra in the quotient).
  -- `periodLattice X = Jacobians.truePeriodLattice X` is definitionally
  -- the same submodule (see `Jacobians.lean:periodLattice` definition).
  have h_eventually :
      (fun Q => (QuotientAddGroup.mk
        (Jacobians.OfCurveSkeleton.localLift (X := X) Q₀
          (Jacobians.periodVec (Jacobians.smoothPath P Q₀)) Q) :
        (Fin (genus X) → ℂ) ⧸ (periodLattice X).toAddSubgroup))
      =ᶠ[nhds Q₀] (ofCurve P) := by
    have h_id := Jacobians.OfCurveSkeleton.localLift_quotient_eq_ofCurve_eventually
      (X := X) P Q₀
    filter_upwards [h_id] with Q hQ
    exact hQ
  exact h_local_quotient.congr_of_eventuallyEq h_eventually.symm

/-- **Abel-Jacobi of basepoint is zero**: the smooth path `P → P` is
a closed smooth loop, so its periodVec is in the lattice, hence maps
to `0` in the quotient. -/
lemma ofCurve_self (P : X) : ofCurve P P = 0 := by
  unfold ofCurve
  exact (QuotientAddGroup.eq_zero_iff _).mpr
    (Jacobians.periodVec_smoothPath_self_mem_lattice P)

/-- **Basepoint change for `ofCurve`**: shifting the basepoint from
`P` to `P₀` adds the constant `ofCurve P₀ P` (the image of the old
basepoint under the new).

**Proof strategy:**
1. Let `γ₁ = sp(P₀, A)` and `γ₂ = concat(sp(P₀, P), sp(P, A))`. Both
   go from P₀ to A.
2. Apply `mk_periodVec_eq_of_endpoints`: their mk(periodVec) are
   equal in the Jacobian quotient.
3. By `periodVec_concat`, `periodVec γ₂ = periodVec (sp(P₀, P)) +
   periodVec (sp(P, A))`.
4. Rearrange via `QuotientAddGroup.mk_add`: `ofCurve P₀ A = ofCurve
   P₀ P + ofCurve P A`.

Proven here via `smoothPath_basepoint_change`, which is the second
conjunct of `exists_smoothPath_family` (sorry S1) extracted by
`choose_spec`. So this lemma is genuine modulo S1 — no separate sorry. -/
lemma ofCurve_basepoint_change (P P₀ A : X) :
    ofCurve P₀ A = ofCurve P A + ofCurve P₀ P := by
  unfold ofCurve
  exact Jacobians.smoothPath_basepoint_change P P₀ A

/-- **Abel ⇒ ofCurve injective** (THE main challenge theorem).

This is a *real* proof chain, not a placeholder. `ofCurve` is the
path-integrated Abel–Jacobi map and `abelJacobi` is the genuine
divisor map; they connect via the proven
`abelJacobi_twoPointDivisor : abelJacobi (twoPointDivisor Q' Q) =
ofCurve P₀ Q' - ofCurve P₀ Q`. The chain:
  ofCurve P Q = ofCurve P Q'
   → (basepoint change, `ofCurve_basepoint_change`) ofCurve P₀ Q' = ofCurve P₀ Q
   → abelJacobi (twoPointDivisor Q' Q) = 0
   → contradicts `abelJacobi_twoPoint_ne_zero` when Q ≠ Q' and 0 < genus X.

The only remaining math gap is the leaf `abelJacobi_twoPoint_ne_zero`
(sorry S7 = Abel's theorem + Riemann–Hurwitz, `Abel.lean`); everything
above it here is proven. The basepoint-change step also rests on
`smoothPath_basepoint_change`, extracted from sorry S1
(`exists_smoothPath_family`). -/
lemma ofCurve_inj
    (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) := by
  intro Q Q' h_eq
  by_contra h_ne
  -- Abel's theorem chain: abelJacobi (twoPointDivisor Q' Q) ≠ 0 when Q' ≠ Q.
  have h_nonzero := Jacobians.abelJacobi_twoPoint_ne_zero h (Ne.symm h_ne)
  apply h_nonzero
  -- Compute abelJacobi (twoPointDivisor Q' Q) = mk(sp(P₀,Q')) - mk(sp(P₀,Q))
  rw [Jacobians.abelJacobi_twoPointDivisor _ _ (Ne.symm h_ne)]
  -- Let P₀ = Classical.arbitrary X. Show mk(sp(P₀,Q')) = mk(sp(P₀,Q)).
  -- Via basepoint change: ofCurve P₀ A = ofCurve P A + ofCurve P₀ P.
  -- Since ofCurve P Q = ofCurve P Q' (hypothesis), subtract gives:
  -- ofCurve P₀ Q - ofCurve P₀ Q' = ofCurve P Q - ofCurve P Q' = 0.
  show ofCurve (Classical.arbitrary X) Q' - ofCurve (Classical.arbitrary X) Q = 0
  rw [ofCurve_basepoint_change P (Classical.arbitrary X) Q',
    ofCurve_basepoint_change P (Classical.arbitrary X) Q,
    h_eq]
  abel

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

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
  [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]

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

/-- Lattice preservation on the pullback side: the genuine Jacobian pullback
`ambientPullbackJac` (= `Tᵀ`, the trace transpose) maps the `Y`-period lattice
into the `X`-period lattice, because `Tᵀ(periodVec δ) = periodVec(preimage
cycle of δ)` (projection formula) and the preimage cycle is an `X`-cycle.

Discharged by the S4 §3 preimage-cycle construction
(`ambientPullbackJac_preserves_truePeriodLattice`, PeriodLattice.lean) — itself
modulo the §3 `exists_preimageCycle` lift. Replaces the misformalized
`ambientPsi`-as-pullback, whose preservation rested on the false `ambientPsi`
trace identity. -/
lemma ambientPullbackJac_preserves_lattice
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (periodLattice Y).toAddSubgroup ≤
      (periodLattice X).toAddSubgroup.comap
        (Jacobians.ambientPullbackJac (gX := genus X) (gY := genus Y) f hf).toAddMonoidHom :=
  Jacobians.ambientPullbackJac_preserves_truePeriodLattice f hf

/-- Pullback map between Jacobians associated to a map of the underlying curves.
Equal to the zero map if the map on curves is constant.
Wired: `ZLatticeQuotient.pullback` applied to the genuine Jacobian pullback
`ambientPullbackJac f hf` (= `Tᵀ`). -/
noncomputable def pullback (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X :=
  Jacobians.ZLatticeQuotient.pullback (periodLattice X) (periodLattice Y)
    (Jacobians.ambientPullbackJac (gX := genus X) (gY := genus Y) f hf)
    (ambientPullbackJac_preserves_lattice f hf)

-- pullback is holomorphic
theorem pullback_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf) :=
  Jacobians.ZLatticeQuotient.pullback_contMDiff_of_ambient
    (periodLattice X) (periodLattice Y)
    (Jacobians.ambientPullbackJac (gX := genus X) (gY := genus Y) f hf)
    (ambientPullbackJac_preserves_lattice f hf)

-- functoriality
lemma pullback_id_apply
    (P : Jacobian X) : pullback id contMDiff_id P = P :=
  Jacobians.ZLatticeQuotient.pushforward_id_of_ambient
    (periodLattice X)
    (Jacobians.ambientPullbackJac (gX := genus X) (gY := genus X) id contMDiff_id)
    (ambientPullbackJac_preserves_lattice id contMDiff_id)
    (fun x => Jacobians.ambientPullbackJac_id (X := X) x)
    P

-- functoriality
lemma pullback_comp_apply
    (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := by
  induction P using QuotientAddGroup.induction_on with
  | H z =>
    show QuotientAddGroup.mk
        (Jacobians.ambientPullbackJac (gX := genus X) (gY := genus Z) (g ∘ f)
          (hg.comp hf) z) =
      QuotientAddGroup.mk
        (Jacobians.ambientPullbackJac (gX := genus X) (gY := genus Y) f hf
          (Jacobians.ambientPullbackJac (gX := genus Y) (gY := genus Z) g hg z))
    congr 1
    exact Jacobians.ambientPullbackJac_comp f hf g hg (hg.comp hf) z

/-- The degree of a holomorphic map between compact Riemann surfaces.
Equal to zero for constant maps, otherwise equal to the cardinality of
a regular fibre (Forster §4).

**Implementation.** Delegates to `Jacobians.degreeFiber`, a port of
`JacobianChallenge.ContMDiff.degreeFiber` from Bryan Sanchez's
`jacobian-lean-challenge` (`#print axioms`-verified clean per
`docs/EXTERNAL_AUDIT.md`). For non-constant `f`, `degreeFiber` returns
the cardinality of the fibre over a `RegularValueWitnessReg`-supplied
regular value via `Classical.choice`. The witness existence
`Nonempty (RegularValueWitnessReg f)` *is* supplied unconditionally
(`Jacobians.regularValueWitnessReg_nonempty_of_nonConstantMap`,
`#print axioms`-clean), so for non-constant `f` the `else 0` fallback
does **not** fire and the degree is a genuine regular-fibre cardinality.

Remaining gaps (do not affect soundness of the *shape* `= deg • P` in
`pushforward_pullback`, but matter for its quantitative meaning):
(a) *positivity* — `degreeFiber f hf > 0` for non-constant `f` (needs
surjectivity of proper non-constant holomorphic maps); (b)
*well-definedness* — independence of the chosen regular value. -/
noncomputable def _root_.ContMDiff.degree (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : ℕ :=
  Jacobians.degreeFiber f hf

/-- **Ambient degree identity** (`f_* ∘ f^* = deg(f) • id`; Griffiths–Harris
Ch. 2 §2.7 — the trace map for forms): the genuine pushforward `ambientPhi`
(= `Mᵀ`, dual to pullback-of-forms) composed with the genuine pullback
`ambientPullbackJac` (= `Tᵀ`, transpose of the geometric trace `traceForm`) is
multiplication by the degree, in ambient coordinates.

`Mᵀ Tᵀ = (T M)ᵀ = (deg • I)ᵀ = deg • I`, where `T M = deg • I` is the trace
identity `traceForm ∘ pullbackForm = deg • id` (G&H §2.7).

**[open, honest]** Now a *true* statement (no longer the false `MᵀM = deg·I` of
the old `ambientPhi_ambientPsi_eq`, which used the wrong pullback). Discharged in
Phase 4 from the S4 §3 preimage cycle + the proven `periodVec_pushforward` + S3
spanning: `ambientPhi(periodVec Γ) = periodVec(f∘Γ) = deg·periodVec δ` and
`periodVec Γ = ambientPullbackJac(periodVec δ)`, extended off the lattice by
full-rank (S3). See `docs/S8_TRACE_PLAN.md`. -/
theorem ambientPhi_ambientPullback_eq (y : Fin (genus Y) → ℂ) :
    Jacobians.ambientPhi (gX := genus X) (gY := genus Y) f hf
      (Jacobians.ambientPullbackJac (gX := genus X) (gY := genus Y) f hf y) =
      (ContMDiff.degree f hf) • y :=
  sorry

/-- **Connection keystone (S4 §3 ⟹ S8, on periods).** If the preimage cycle of a
loop `δ` is realised by closed smooth loops `loops` with integer `coeffs`
satisfying the two cycle identities —
* `h_pullback`: `Tᵀ·periodVec δ = ∑ coeffs·periodVec loopsᵢ` (projection formula),
* `h_pushforward`: `∑ coeffs·periodVec(f∘loopsᵢ) = deg·periodVec δ` (i.e. `f∘Γ = deg·δ`)
— then the degree identity `ambientPhi(ambientPullbackJac(periodVec δ)) = deg·periodVec δ`
holds on `periodVec δ`.

This is the meet-in-the-middle linchpin: it consumes the (upstream) §3 preimage
cycle and the **proven** `periodVec_pushforward`, and yields
`ambientPhi_ambientPullback_eq` *restricted to period vectors* — proving that the
§3 construction will discharge S8 (no throwaway). The full identity then follows
by S3 (the period lattice spans `Fin gY → ℂ`). No new sorry. See
`docs/S8_TRACE_PLAN.md`. -/
lemma ambientPhi_ambientPullback_periodVec_of_cycle
    {n : ℕ} (loops : Fin n → ℝ → X)
    (loops_smooth : ∀ i, Jacobians.IsClosedSmoothLoop (loops i))
    (coeffs : Fin n → ℤ) (δ : ℝ → Y)
    (h_pullback : Jacobians.ambientPullbackJac (gX := genus X) (gY := genus Y) f hf
        (Jacobians.periodVec δ) = ∑ i, coeffs i • Jacobians.periodVec (loops i))
    (h_pushforward : ∑ i, coeffs i • Jacobians.periodVec (f ∘ loops i) =
        (ContMDiff.degree f hf) • Jacobians.periodVec δ) :
    Jacobians.ambientPhi (gX := genus X) (gY := genus Y) f hf
        (Jacobians.ambientPullbackJac (gX := genus X) (gY := genus Y) f hf
          (Jacobians.periodVec δ)) =
      (ContMDiff.degree f hf) • Jacobians.periodVec δ := by
  rw [h_pullback, map_sum, ← h_pushforward]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, Jacobians.periodVec_pushforward f hf (loops i) (loops_smooth i).cont
    (loops_smooth i).diff (loops_smooth i).integrable]

lemma pushforward_pullback
    (P : Jacobian Y) :
    pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P :=
  Jacobians.ZLatticeQuotient.pushforward_pullback_of_ambient
    (periodLattice X) (periodLattice Y)
    (Jacobians.ambientPhi (gX := genus X) (gY := genus Y) f hf)
    (Jacobians.ambientPullbackJac (gX := genus X) (gY := genus Y) f hf)
    (ambientPhi_preserves_lattice f hf)
    (ambientPullbackJac_preserves_lattice f hf)
    (ContMDiff.degree f hf)
    (fun y => ambientPhi_ambientPullback_eq f hf y)
    P

end Jacobian
