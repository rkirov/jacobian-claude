-- In-repo validation of the leaderboard Submission.lean shim: identical content,
-- except the real Submission.lean imports Submission.Root instead of Jacobians.
--
-- The shim is deliberately *not* `@[reducible]`: the problem file's
-- `Solution.lean` wrappers elaborate their statements in an environment where
-- the shim is imported, and a reducible `Jacobian` would let instance search
-- see through to the concrete `ULift (JacobianTorus X)`, picking Mathlib's
-- generic `ULift` instances instead of the named challenge instances and
-- changing the elaborated statements comparator checks. With the
-- lean-eval generator now emitting `noncomputable` delegations
-- (https://github.com/leanprover/lean-eval/pull/422), the shim can use honest
-- `noncomputable def`s with no `@[implemented_by]`/`unsafeCast` stubs.
import Jacobians

open scoped ContDiff

namespace Submission

namespace JacobianChallenge

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

noncomputable def genus (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : ℕ :=
  _root_.genus X

theorem genus_eq_zero_iff_homeo :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  _root_.genus_eq_zero_iff_homeo

noncomputable def Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : Type u :=
  _root_.Jacobian X

namespace Jacobian

noncomputable instance instAddCommGroup : AddCommGroup (Jacobian X) :=
  inferInstanceAs (AddCommGroup (_root_.Jacobian X))

noncomputable instance instTopologicalSpace : TopologicalSpace (Jacobian X) :=
  inferInstanceAs (TopologicalSpace (_root_.Jacobian X))

instance instT2Space : T2Space (Jacobian X) :=
  inferInstanceAs (T2Space (_root_.Jacobian X))

instance instCompactSpace : CompactSpace (Jacobian X) :=
  inferInstanceAs (CompactSpace (_root_.Jacobian X))

noncomputable instance instChartedSpace : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) :=
  inferInstanceAs (ChartedSpace (Fin (_root_.genus X) → ℂ) (_root_.Jacobian X))

instance instIsManifold :
    IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  inferInstanceAs (IsManifold (modelWithCornersSelf ℂ (Fin (_root_.genus X) → ℂ)) ω
    (_root_.Jacobian X))

instance instLieAddGroup :
    LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  inferInstanceAs (LieAddGroup (modelWithCornersSelf ℂ (Fin (_root_.genus X) → ℂ)) ω
    (_root_.Jacobian X))

noncomputable def ofCurve (P : X) : X → Jacobian X := _root_.Jacobian.ofCurve P

theorem ofCurve_contMDiff (P : X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (ofCurve P) :=
  _root_.Jacobian.ofCurve_contMDiff P

theorem ofCurve_self (P : X) : ofCurve P P = 0 := _root_.Jacobian.ofCurve_self P

theorem ofCurve_inj (P : X) (h : 0 < genus X) : Function.Injective (ofCurve P) :=
  _root_.Jacobian.ofCurve_inj P h

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)

noncomputable def pushforward (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    Jacobian X →ₜ+ Jacobian Y :=
  _root_.Jacobian.pushforward f hf

theorem pushforward_contMDiff (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ)) ω (pushforward f hf) :=
  _root_.Jacobian.pushforward_contMDiff f hf

theorem pushforward_id_apply (P : Jacobian X) :
    pushforward id contMDiff_id P = P :=
  _root_.Jacobian.pushforward_id_apply P

variable {Z : Type w} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold (modelWithCornersSelf ℂ ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g)

theorem pushforward_comp_apply (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g)
    (P : Jacobian X) :
    pushforward (g ∘ f) (hg.comp hf) P = pushforward g hg (pushforward f hf P) := by
  apply _root_.Jacobian.pushforward_comp_apply

noncomputable def pullback (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    Jacobian Y →ₜ+ Jacobian X :=
  _root_.Jacobian.pullback f hf

theorem pullback_contMDiff (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (genus Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (pullback f hf) :=
  _root_.Jacobian.pullback_contMDiff f hf

theorem pullback_id_apply (P : Jacobian X) :
    pullback id contMDiff_id P = P :=
  _root_.Jacobian.pullback_id_apply P

theorem pullback_comp_apply (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g)
    (P : Jacobian Z) :
    pullback (g.comp f) (hg.comp hf) P = pullback f hf (pullback g hg P) := by
  apply _root_.Jacobian.pullback_comp_apply

/-- The challenge's `degree` only auto-binds `[TopologicalSpace _]` and
`[ChartedSpace ℂ _]` on each surface (all that its signature mentions), so the
shim must take exactly those binders or the `Solution.lean` wrapper pulls the
extra section variables into its signature and the statements applying
`degree` stop matching the challenge. `ContMDiff.degree` unfolds to
`degreeFiber`, whose body needs only these instances, so we inline that body;
`degree f hf` is definitionally `ContMDiff.degree f hf`. -/
noncomputable def degree {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : X → Y)
    (_hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) : ℕ :=
  open Classical in
  if _root_.Jacobians.IsConstantMap f then 0
  else
    if h : Nonempty (_root_.Jacobians.RegularValueWitnessReg f) then
      (Classical.choice h).card
    else 0

theorem pushforward_pullback (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (P : Jacobian Y) :
    pushforward f hf (pullback f hf P) = (degree f hf) • P := by
  apply _root_.Jacobian.pushforward_pullback

end Jacobian

end JacobianChallenge

end Submission
