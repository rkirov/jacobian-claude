-- In-repo validation of the leaderboard Submission.lean shim: identical content,
-- except the real Submission.lean imports Submission.Root instead of Jacobians.
import Jacobians

open scoped ContDiff

noncomputable section

namespace JacobianChallenge

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

def genus (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : ℕ :=
  _root_.genus X

theorem genus_eq_zero_iff_homeo :
    genus X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :=
  _root_.genus_eq_zero_iff_homeo

def Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : Type u :=
  _root_.Jacobian X

namespace Jacobian

instance instAddCommGroup : AddCommGroup (Jacobian X) :=
  inferInstanceAs (AddCommGroup (_root_.Jacobian X))

instance instTopologicalSpace : TopologicalSpace (Jacobian X) :=
  inferInstanceAs (TopologicalSpace (_root_.Jacobian X))

instance instT2Space : T2Space (Jacobian X) :=
  inferInstanceAs (T2Space (_root_.Jacobian X))

instance instCompactSpace : CompactSpace (Jacobian X) :=
  inferInstanceAs (CompactSpace (_root_.Jacobian X))

instance instChartedSpace : ChartedSpace (Fin (genus X) → ℂ) (Jacobian X) :=
  inferInstanceAs (ChartedSpace (Fin (_root_.genus X) → ℂ) (_root_.Jacobian X))

instance instIsManifold :
    IsManifold (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  inferInstanceAs (IsManifold (modelWithCornersSelf ℂ (Fin (_root_.genus X) → ℂ)) ω
    (_root_.Jacobian X))

instance instLieAddGroup :
    LieAddGroup (modelWithCornersSelf ℂ (Fin (genus X) → ℂ)) ω (Jacobian X) :=
  inferInstanceAs (LieAddGroup (modelWithCornersSelf ℂ (Fin (_root_.genus X) → ℂ)) ω
    (_root_.Jacobian X))

def ofCurve (P : X) : X → Jacobian X := _root_.Jacobian.ofCurve P

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

def pushforward (f : X → Y)
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

def pullback (f : X → Y)
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

def degree (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) : ℕ :=
  ContMDiff.degree f hf

theorem pushforward_pullback (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (P : Jacobian Y) :
    pushforward f hf (pullback f hf P) = (degree f hf) • P := by
  apply _root_.Jacobian.pushforward_pullback

end Jacobian

end JacobianChallenge

end
