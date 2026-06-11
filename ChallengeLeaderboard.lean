/-
# Lean AI formalization leaderboard conformance check

Verifies that this repository's declarations satisfy the challenge statement as published on the
Lean leaderboard problem page

  https://lean-lang.org/eval/problems/jacobian_challenge_diffgeo/

**exactly as spelled there**: `modelWithCornersSelf ℂ ℂ` (the leaderboard page's spelling
of `𝓘(ℂ)`),
the `[Nonempty X]` hypothesis present in the page's binder lists, the bundled `→ₜ+` homomorphisms,
and the bare `degree` name. Each `example` below restates a leaderboard signature verbatim and
discharges it by our declaration, so this file compiling is a machine check that the implementation
conforms to the leaderboard form of the challenge (the sibling `ChallengeConformance.lean` checks
the v0.4 spec form).

Run: `lake env lean ChallengeLeaderboard.lean`  (expects no errors)

The whole file is a `noncomputable section`; we only check that the *types* are inhabited by our
declarations. `Jacobian` is genuinely `Type u` (universe-polymorphic), matching the page.
-/
import Jacobians

open scoped ContDiff -- for ω notation
open scoped Manifold

universe u

noncomputable section

-- `genus`
example (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : ℕ :=
  genus X

-- let X be a compact Riemann surface, with the page's `[Nonempty X]` included
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [Nonempty X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

-- `genus_eq_zero_iff_homeo`
example :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  genus_eq_zero_iff_homeo

-- `Jacobian`
example (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : Type u :=
  Jacobian X

namespace Jacobian

-- `instAddCommGroup` … `instLieAddGroup`: the seven instances
example : AddCommGroup (Jacobian X) := inferInstance
example : TopologicalSpace (Jacobian X) := inferInstance
example : T2Space (Jacobian X) := inferInstance
example : CompactSpace (Jacobian X) := inferInstance
example : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) := inferInstance
example : IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  inferInstance
example : LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  inferInstance

-- `ofCurve`, `ofCurve_contMDiff`, `ofCurve_self`, `ofCurve_inj`
example (P : X) : X → Jacobian X := ofCurve P
example (P : X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω
      (ofCurve P) :=
  ofCurve_contMDiff P
example (P : X) : ofCurve P P = 0 := ofCurve_self P
example (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) := ofCurve_inj P h

variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)

-- `pushforward`, `pushforward_contMDiff`, `pushforward_id_apply`, `pushforward_comp_apply`
example : Jacobian X →ₜ+ Jacobian Y := pushforward f hf
example :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforward f hf) :=
  pushforward_contMDiff f hf
example (P : Jacobian X) : pushforward id contMDiff_id P = P := pushforward_id_apply P

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold (modelWithCornersSelf ℂ ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g)

example (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) := by
  apply pushforward_comp_apply

-- `pullback`, `pullback_contMDiff`, `pullback_id_apply`, `pullback_comp_apply`
example : Jacobian Y →ₜ+ Jacobian X := pullback f hf
example :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf) :=
  pullback_contMDiff f hf
example (P : Jacobian X) : pullback id contMDiff_id P = P := pullback_id_apply P
example (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := by
  apply pullback_comp_apply

-- `degree` (the page's bare name for the repo's `ContMDiff.degree`)
example : ℕ := ContMDiff.degree f hf

-- `pushforward_pullback`
example (P : Jacobian Y) :
    pushforward f hf (pullback f hf P) = (ContMDiff.degree f hf) • P := by
  apply pushforward_pullback

end Jacobian

end
