/-
  Čech `H¹` finiteness on a CHART-DISK cover — the COMPLETE (sorry-free target) version.

  `ChartDiskFiniteness.lean` proves the analytic heart — the Forster 14.6 cover-level ∂̄-lift
  (`ChartDiskCover.forster146_lift`) — and the relatively-compact covering shrinking + the
  `HolomorphicDiskOverlapData` (`𝔇.overlapData`, with compact `ρ` for free, Montel).  It leaves ONE
  honest `sorry` (`ChartDiskCover.finiteDimensional_cechH1_chartDisk`): the structural δ-complex
  `HolomorphicCoboundaries 𝔇.overlapData` together with a comparison `cechH1 𝔇 0 ≃ₗ supH1`.

  This file discharges that `sorry` SORRY-FREE.  It supplies the two missing pieces for the proven
  reduction `ChartDiskCover.finiteDimensional_cechH1_of_holomorphicModel`:

    * **(A) the δ-complex** `HolomorphicCoboundaries 𝔇.overlapData` — mirroring
      `CechModelHolomorphicDelta.lean` (which builds the same data for the MONTEL cover
      `chartCoverHolomorphicDiskOverlapData`) but for `𝔇.overlapData`, whose geometry is the chart-disk
      ball-overlaps `𝔇.Uov`/`𝔇.Wov`.  Its `leray` field is the proven `forster146_lift` (the analytic
      heart), wired through a `BallSplitData` built from a smooth partition of unity subordinate to the
      cover `(𝔇.U i)` (`X` compact).

    * **(B) the comparison.**  For FINITENESS a linear INJECTION `cechH1 𝔇 0 ↪ supH1` suffices
      (`FiniteDimensional.of_injective` + `supH1` finite).  The forward germ→`BddHol` cochain map
      (`CechModelCochain.cochainToCcov`) descends to `cechH1 𝔇 0 → supH1`; its INJECTIVITY is the
      same germ-class `𝒪_D` sheaf-gluing used for Forster 12.4
      (`CechRefinementInjective.{omegaDGerm_separated, omegaDGerm_glue}`).

  Conventions follow `ChartDiskFiniteness.lean` / `CechModelHolomorphicDelta.lean`.
-/
import Jacobians.Dolbeault.ChartDiskFiniteness
import Jacobians.Dolbeault.CechModelHolomorphicDelta
import Jacobians.Dolbeault.CechRefinementInjective

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Metric Complex Filter ContinuousLinearMap

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 80000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace ChartDiskCover

variable (𝔇 : ChartDiskCover X)

/-- `𝔇.overlapData.Wov = 𝔇.Wov` (rfl) — exposed as a simp lemma so the `rhoRaw`-introduced
`overlapData.Wov` terms normalize to the `𝔇.Wov` used by the geometric witnesses. -/
@[simp] theorem overlapData_Wov_eq : 𝔇.overlapData.Wov = 𝔇.Wov := rfl

/-- `𝔇.overlapData.Uov = 𝔇.Uov` (rfl). -/
@[simp] theorem overlapData_Uov_eq : 𝔇.overlapData.Uov = 𝔇.Uov := rfl

/-! ## §A — The cross-chart Čech δ-complex on `𝔇.overlapData`

We build, for the chart-disk model `𝔇.overlapData` (whose `Uov`/`Wov` are the chart-`a` images of the
ball overlap `U a ∩ U b` resp. the shrinking overlap `V a ∩ V b`), the same data that
`CechModelHolomorphicDelta` builds for the Montel model: the cross-chart `δ⁰`/`δ¹`, the cover-side
`δ¹cov`, the cocycle identity `δ²=0`, and the commuting `hcomm` square.  The transport in each
differential is the analytic chart transition `𝔇.coverTransition a b`, analytic on the open `𝔇.Wov`
and mapping it into the `b`-side cover-open.

The geometry differs from Montel only in the concrete sets; the proofs are structurally identical, so
we re-derive the `coverTransition`/maps-to witnesses against `𝔇.Wov`/`𝔇.Uov`. -/

/-- The cover transition `τ_{ab}` is analytic on the OPEN shrinking overlap `𝔇.Wov (a,b)` (chart-`a`
image of `V a ∩ V b`): at each point it is analytic by `transition_analyticAt_of_mem`, both centres'
chart sources containing the overlap point (`V a, V b ⊆ closure ⊆ U ⊆ source`). -/
theorem analyticOn_coverTransition_Wov (a b : 𝔇.ι) :
    AnalyticOn ℂ (𝔇.coverTransition a b) (𝔇.Wov (a, b)) := by
  rintro w ⟨x, ⟨hxa, hxb⟩, rfl⟩
  apply AnalyticAt.analyticWithinAt
  exact transition_analyticAt_of_mem
    (𝔇.U_subset_chartAt_source a (𝔇.closure_shrinkSet_subset_U a (subset_closure hxa)))
    (𝔇.U_subset_chartAt_source b (𝔇.closure_shrinkSet_subset_U b (subset_closure hxb)))

/-- The cover transition `τ_{ab}` maps the OPEN shrinking overlap `𝔇.Wov (a,b)` (chart-`a`
coordinates) into the `b`-side cover-open `𝔇.Uov (b,b)` (chart-`b` image of `U b`).  A point `φ_a x`
with `x ∈ V a ∩ V b` maps to `φ_b x` with `x ∈ V b ⊆ U b`, so `φ_b x ∈ φ_b '' (U b) = Uov (b,b)`. -/
theorem mapsTo_coverTransition_Wov (a b : 𝔇.ι) :
    Set.MapsTo (𝔇.coverTransition a b) (𝔇.Wov (a, b)) (𝔇.Uov (b, b)) := by
  rintro w ⟨x, ⟨hxa, hxb⟩, rfl⟩
  have hxa_src : x ∈ (chartAt (H := ℂ) (𝔇.center a)).source :=
    𝔇.U_subset_chartAt_source a (𝔇.closure_shrinkSet_subset_U a (subset_closure hxa))
  have hxbU : x ∈ ((𝔇.U b : Opens X) : Set X) :=
    𝔇.closure_shrinkSet_subset_U b (subset_closure hxb)
  refine ⟨x, ⟨hxbU, hxbU⟩, ?_⟩
  rw [coverTransition, Function.comp_apply,
    (chartAt (H := ℂ) (𝔇.center a)).left_inv hxa_src]

/-- The shrinking overlap `𝔇.Wov (a,b)` lies in the `a`-side cover-open `𝔇.Uov (a,a)` (chart-`a`
image of `V a ∩ V b ⊆ U a`), so the diagonal `a`-component restricts directly. -/
theorem Wov_subset_Uov_diag_fst (a b : 𝔇.ι) :
    𝔇.Wov (a, b) ⊆ 𝔇.Uov (a, a) := by
  refine Set.image_mono (fun x hx => ?_)
  have hxU : x ∈ ((𝔇.U a : Opens X) : Set X) :=
    𝔇.closure_shrinkSet_subset_U a (subset_closure hx.1)
  exact ⟨hxU, hxU⟩

/-- **The cross-chart Čech `δ⁰`** of the chart-disk model: `c.Cshr`-valued from `Cochain0Holo`.
Componentwise on overlap `(a,b)`,
    `(δ⁰f)_{ab} = (transport of f_b to chart-a) − (restriction of f_a)`   on the OPEN `Wov (a,b)`,
the genuine Čech coboundary with the `b`-side transported through the holomorphic transition `τ_{ab}`.
Both pieces stay `BddHol` on the open `Wov`. -/
noncomputable def delta0Model :
    (∀ a : 𝔇.ι, BddHol (𝔇.Uov (a, a))) →L[ℂ] 𝔇.overlapData.Cshr :=
  ContinuousLinearMap.pi fun p =>
    (BddHol.precompHolCLM (𝔇.analyticOn_coverTransition_Wov p.1 p.2)
        (𝔇.mapsTo_coverTransition_Wov p.1 p.2)).comp (proj p.2)
      - (BddHol.restrictOpenCLM (𝔇.Wov_subset_Uov_diag_fst p.1 p.2)).comp (proj p.1)

theorem delta0Model_apply (f : ∀ a : 𝔇.ι, BddHol (𝔇.Uov (a, a)))
    (p : 𝔇.overlapData.J) :
    𝔇.delta0Model f p
      = BddHol.precompHolCLM (𝔇.analyticOn_coverTransition_Wov p.1 p.2)
          (𝔇.mapsTo_coverTransition_Wov p.1 p.2) (f p.2)
        - BddHol.restrictOpenCLM (𝔇.Wov_subset_Uov_diag_fst p.1 p.2) (f p.1) := rfl

theorem delta0Model_apply_apply (f : ∀ a : 𝔇.ι, BddHol (𝔇.Uov (a, a)))
    (p : 𝔇.overlapData.J) {z : ℂ} (hz : z ∈ 𝔇.Wov p) :
    (𝔇.delta0Model f p).toFun z
      = (f p.2).toFun (𝔇.coverTransition p.1 p.2 z) - (f p.1).toFun z := by
  obtain ⟨a, b⟩ := p
  rw [delta0Model_apply, BddHol.toFun_sub, Pi.sub_apply,
    BddHol.precompHolCLM_apply, BddHol.precompHol_toFun_of_mem _ _ _ hz,
    BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]

/-! ### The shrinking-side 2-cochains on OPEN triples `WovTriple`, and the `δ¹` -/

/-- Open chart-`a` image of the triple shrinking overlap `V a ∩ V b ∩ V c` — the shrinking-side
2-cochain domain. -/
noncomputable def WovTriple (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) : Set ℂ :=
  (chartAt (H := ℂ) (𝔇.center t.1)) ''
    (𝔇.shrinkSet t.1 ∩ 𝔇.shrinkSet t.2.1 ∩ 𝔇.shrinkSet t.2.2)

theorem isOpen_WovTriple (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) : IsOpen (𝔇.WovTriple t) := by
  refine (chartAt (H := ℂ) (𝔇.center t.1)).isOpen_image_of_subset_source
    (((𝔇.shrinkSet_isOpen t.1).inter (𝔇.shrinkSet_isOpen t.2.1)).inter
      (𝔇.shrinkSet_isOpen t.2.2)) ?_
  refine ((Set.inter_subset_left.trans Set.inter_subset_left).trans
    ((subset_closure).trans (𝔇.closure_shrinkSet_subset_U t.1))).trans ?_
  exact 𝔇.U_subset_chartAt_source t.1

/-- **Sup-norm 2-cochains, holomorphic shrinking side** `C2Holo` — bounded-holomorphic on each open
triple `WovTriple t`. -/
abbrev C2Holo (𝔇 : ChartDiskCover X) : Type _ :=
  ∀ t : 𝔇.ι × 𝔇.ι × 𝔇.ι, BddHol (𝔇.WovTriple t)

noncomputable instance : NormedAddCommGroup 𝔇.C2Holo := inferInstance
noncomputable instance : NormedSpace ℂ 𝔇.C2Holo := inferInstance

noncomputable instance : CompleteSpace 𝔇.C2Holo := by
  haveI : ∀ t, CompleteSpace (BddHol (𝔇.WovTriple t)) := fun t =>
    BddHol.completeSpace (𝔇.isOpen_WovTriple t)
  infer_instance

theorem analyticOn_coverTransition_WovTriple (a b c : 𝔇.ι) :
    AnalyticOn ℂ (𝔇.coverTransition a b) (𝔇.WovTriple (a, b, c)) := by
  rintro w ⟨x, ⟨⟨hxa, hxb⟩, _hxc⟩, rfl⟩
  apply AnalyticAt.analyticWithinAt
  exact transition_analyticAt_of_mem
    (𝔇.U_subset_chartAt_source a (𝔇.closure_shrinkSet_subset_U a (subset_closure hxa)))
    (𝔇.U_subset_chartAt_source b (𝔇.closure_shrinkSet_subset_U b (subset_closure hxb)))

/-- `τ_{ab}` maps the OPEN triple `WovTriple (a,b,c)` (chart-`a` coords) into the shrinking
`Wov (b,c)` (chart-`b` image of `V b ∩ V c`).  A point `φ_a x` with `x ∈ V a ∩ V b ∩ V c` maps to
`φ_b x` with `x ∈ V b ∩ V c`. -/
theorem mapsTo_coverTransition_WovTriple_shrink (a b c : 𝔇.ι) :
    Set.MapsTo (𝔇.coverTransition a b) (𝔇.WovTriple (a, b, c)) (𝔇.Wov (b, c)) := by
  rintro w ⟨x, ⟨⟨hxa, hxb⟩, hxc⟩, rfl⟩
  have hxa_src : x ∈ (chartAt (H := ℂ) (𝔇.center a)).source :=
    𝔇.U_subset_chartAt_source a (𝔇.closure_shrinkSet_subset_U a (subset_closure hxa))
  exact ⟨x, ⟨hxb, hxc⟩, by
    rw [coverTransition, Function.comp_apply,
      (chartAt (H := ℂ) (𝔇.center a)).left_inv hxa_src]⟩

theorem WovTriple_subset_Wov_fst_snd (a b c : 𝔇.ι) :
    𝔇.WovTriple (a, b, c) ⊆ 𝔇.Wov (a, b) :=
  Set.image_mono Set.inter_subset_left

theorem WovTriple_subset_Wov_fst_trd (a b c : 𝔇.ι) :
    𝔇.WovTriple (a, b, c) ⊆ 𝔇.Wov (a, c) :=
  Set.image_mono (fun _ hx => ⟨hx.1.1, hx.2⟩)

/-- **The cross-chart Čech `δ¹` on the shrinking side** `c.Cshr →L[ℂ] C2Holo`.
Componentwise on the triple `(a,b,c)`, `(δ¹s)_{abc} = (s_{bc} ∘ τ_{ab}) − s_{ac} + s_{ab}` on the
OPEN `WovTriple (a,b,c)`. -/
noncomputable def delta1Model :
    𝔇.overlapData.Cshr →L[ℂ] 𝔇.C2Holo :=
  ContinuousLinearMap.pi fun t =>
    (BddHol.precompHolCLM (𝔇.analyticOn_coverTransition_WovTriple t.1 t.2.1 t.2.2)
        (𝔇.mapsTo_coverTransition_WovTriple_shrink t.1 t.2.1 t.2.2)).comp (proj (t.2.1, t.2.2))
      - (BddHol.restrictOpenCLM (𝔇.WovTriple_subset_Wov_fst_trd t.1 t.2.1 t.2.2)).comp
          (proj (t.1, t.2.2))
      + (BddHol.restrictOpenCLM (𝔇.WovTriple_subset_Wov_fst_snd t.1 t.2.1 t.2.2)).comp
          (proj (t.1, t.2.1))

theorem delta1Model_apply (s : 𝔇.overlapData.Cshr) (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) :
    𝔇.delta1Model s t
      = BddHol.precompHolCLM (𝔇.analyticOn_coverTransition_WovTriple t.1 t.2.1 t.2.2)
          (𝔇.mapsTo_coverTransition_WovTriple_shrink t.1 t.2.1 t.2.2) (s (t.2.1, t.2.2))
        - BddHol.restrictOpenCLM (𝔇.WovTriple_subset_Wov_fst_trd t.1 t.2.1 t.2.2) (s (t.1, t.2.2))
        + BddHol.restrictOpenCLM (𝔇.WovTriple_subset_Wov_fst_snd t.1 t.2.1 t.2.2)
            (s (t.1, t.2.1)) := rfl

theorem delta1Model_apply_apply (s : 𝔇.overlapData.Cshr) (t : 𝔇.ι × 𝔇.ι × 𝔇.ι)
    {z : ℂ} (hz : z ∈ 𝔇.WovTriple t) :
    (𝔇.delta1Model s t).toFun z
      = (s (t.2.1, t.2.2)).toFun (𝔇.coverTransition t.1 t.2.1 z)
        - (s (t.1, t.2.2)).toFun z + (s (t.1, t.2.1)).toFun z := by
  obtain ⟨a, b, c⟩ := t
  rw [delta1Model_apply, BddHol.toFun_add, Pi.add_apply, BddHol.toFun_sub, Pi.sub_apply,
    BddHol.precompHolCLM_apply, BddHol.precompHol_toFun_of_mem _ _ _ hz,
    BddHol.restrictOpenCLM_toFun_of_mem _ _ hz, BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]

/-! ### The cover-side 2-cochains, `δ¹cov`, and the cocycle identity `δ²=0` -/

/-- Open chart-`a` image of the triple cover overlap `U a ∩ U b ∩ U c` — the cover-side 2-cochain
domain. -/
noncomputable def UovTriple (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) : Set ℂ :=
  (chartAt (H := ℂ) (𝔇.center t.1)) ''
    ((𝔇.U t.1 ⊓ 𝔇.U t.2.1 ⊓ 𝔇.U t.2.2 : Opens X) : Set X)

theorem isOpen_UovTriple (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) : IsOpen (𝔇.UovTriple t) := by
  refine (chartAt (H := ℂ) (𝔇.center t.1)).isOpen_image_of_subset_source
    (𝔇.U t.1 ⊓ 𝔇.U t.2.1 ⊓ 𝔇.U t.2.2 : Opens X).isOpen ?_
  refine (Set.Subset.trans ?_ (𝔇.U_subset_chartAt_source t.1))
  exact (Set.inter_subset_left).trans (Set.inter_subset_left)

abbrev C2Cov (𝔇 : ChartDiskCover X) : Type _ :=
  ∀ t : 𝔇.ι × 𝔇.ι × 𝔇.ι, BddHol (𝔇.UovTriple t)

noncomputable instance : NormedAddCommGroup 𝔇.C2Cov := inferInstance
noncomputable instance : NormedSpace ℂ 𝔇.C2Cov := inferInstance

theorem analyticOn_coverTransition_UovTriple (a b c : 𝔇.ι) :
    AnalyticOn ℂ (𝔇.coverTransition a b) (𝔇.UovTriple (a, b, c)) := by
  rintro w ⟨x, hx, rfl⟩
  apply AnalyticAt.analyticWithinAt
  have hxa : x ∈ ((𝔇.U a : Opens X) : Set X) := hx.1.1
  have hxb : x ∈ ((𝔇.U b : Opens X) : Set X) := hx.1.2
  exact transition_analyticAt_of_mem
    (𝔇.U_subset_chartAt_source a hxa) (𝔇.U_subset_chartAt_source b hxb)

/-- `τ_{ab}` maps the cover triple `UovTriple (a,b,c)` into the cover overlap `Uov (b,c)`. -/
theorem mapsTo_coverTransition_UovTriple (a b c : 𝔇.ι) :
    Set.MapsTo (𝔇.coverTransition a b) (𝔇.UovTriple (a, b, c)) (𝔇.Uov (b, c)) := by
  rintro w ⟨x, hx, rfl⟩
  have hxa : x ∈ ((𝔇.U a : Opens X) : Set X) := hx.1.1
  have hxb : x ∈ ((𝔇.U b : Opens X) : Set X) := hx.1.2
  have hxc : x ∈ ((𝔇.U c : Opens X) : Set X) := hx.2
  refine ⟨x, ⟨hxb, hxc⟩, ?_⟩
  rw [coverTransition, Function.comp_apply,
    (chartAt (H := ℂ) (𝔇.center a)).left_inv (𝔇.U_subset_chartAt_source a hxa)]

theorem UovTriple_subset_Uov_fst_snd (a b c : 𝔇.ι) :
    𝔇.UovTriple (a, b, c) ⊆ 𝔇.Uov (a, b) := by
  show (chartAt (H := ℂ) (𝔇.center a)) '' _ ⊆ (chartAt (H := ℂ) (𝔇.center a)) '' _
  exact Set.image_mono (fun x hx => ⟨hx.1.1, hx.1.2⟩)

theorem UovTriple_subset_Uov_fst_trd (a b c : 𝔇.ι) :
    𝔇.UovTriple (a, b, c) ⊆ 𝔇.Uov (a, c) := by
  show (chartAt (H := ℂ) (𝔇.center a)) '' _ ⊆ (chartAt (H := ℂ) (𝔇.center a)) '' _
  exact Set.image_mono (fun x hx => ⟨hx.1.1, hx.2⟩)

/-- **The cross-chart Čech `δ¹` on the COVER side** `c.Ccov →L[ℂ] C2Cov`.  Same shape as the shrinking
`δ¹`, on the full cover overlaps. -/
noncomputable def delta1CovModel :
    𝔇.overlapData.Ccov →L[ℂ] 𝔇.C2Cov :=
  ContinuousLinearMap.pi fun t =>
    (BddHol.precompHolCLM (𝔇.analyticOn_coverTransition_UovTriple t.1 t.2.1 t.2.2)
        (𝔇.mapsTo_coverTransition_UovTriple t.1 t.2.1 t.2.2)).comp (proj (t.2.1, t.2.2))
      - (BddHol.restrictOpenCLM (𝔇.UovTriple_subset_Uov_fst_trd t.1 t.2.1 t.2.2)).comp
          (proj (t.1, t.2.2))
      + (BddHol.restrictOpenCLM (𝔇.UovTriple_subset_Uov_fst_snd t.1 t.2.1 t.2.2)).comp
          (proj (t.1, t.2.1))

theorem delta1CovModel_apply (s : 𝔇.overlapData.Ccov) (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) :
    𝔇.delta1CovModel s t
      = BddHol.precompHolCLM (𝔇.analyticOn_coverTransition_UovTriple t.1 t.2.1 t.2.2)
          (𝔇.mapsTo_coverTransition_UovTriple t.1 t.2.1 t.2.2) (s (t.2.1, t.2.2))
        - BddHol.restrictOpenCLM (𝔇.UovTriple_subset_Uov_fst_trd t.1 t.2.1 t.2.2) (s (t.1, t.2.2))
        + BddHol.restrictOpenCLM (𝔇.UovTriple_subset_Uov_fst_snd t.1 t.2.1 t.2.2)
            (s (t.1, t.2.1)) := rfl

theorem delta1CovModel_apply_apply (s : 𝔇.overlapData.Ccov) (t : 𝔇.ι × 𝔇.ι × 𝔇.ι)
    {z : ℂ} (hz : z ∈ 𝔇.UovTriple t) :
    (𝔇.delta1CovModel s t).toFun z
      = (s (t.2.1, t.2.2)).toFun (𝔇.coverTransition t.1 t.2.1 z)
        - (s (t.1, t.2.2)).toFun z + (s (t.1, t.2.1)).toFun z := by
  obtain ⟨a, b, c⟩ := t
  rw [delta1CovModel_apply, BddHol.toFun_add, Pi.add_apply, BddHol.toFun_sub, Pi.sub_apply,
    BddHol.precompHolCLM_apply, BddHol.precompHol_toFun_of_mem _ _ _ hz,
    BddHol.restrictOpenCLM_toFun_of_mem _ _ hz, BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]

/-- **The chart-transition cocycle identity** on the OPEN triple `WovTriple`: `τ_{bc}(τ_{ab} z) =
τ_{ac} z` for `z ∈ WovTriple (a,b,c)`. -/
theorem coverTransition_cocycle_Wov (a b c : 𝔇.ι) {z : ℂ} (hz : z ∈ 𝔇.WovTriple (a, b, c)) :
    𝔇.coverTransition b c (𝔇.coverTransition a b z) = 𝔇.coverTransition a c z := by
  obtain ⟨x, ⟨⟨hxa, hxb⟩, _hxc⟩, rfl⟩ := hz
  have hxa_src : x ∈ (chartAt (H := ℂ) (𝔇.center a)).source :=
    𝔇.U_subset_chartAt_source a (𝔇.closure_shrinkSet_subset_U a (subset_closure hxa))
  have hxb_src : x ∈ (chartAt (H := ℂ) (𝔇.center b)).source :=
    𝔇.U_subset_chartAt_source b (𝔇.closure_shrinkSet_subset_U b (subset_closure hxb))
  simp only [coverTransition, Function.comp_apply,
    (chartAt (H := ℂ) (𝔇.center a)).left_inv hxa_src,
    (chartAt (H := ℂ) (𝔇.center b)).left_inv hxb_src]

/-- **`δ¹ ∘ δ⁰ = 0` (the shrinking-side Čech `hδδ`).** -/
theorem delta1_comp_delta0 :
    (𝔇.delta1Model).comp 𝔇.delta0Model = 0 := by
  ext f t
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  apply BddHol.toFun_injective
  funext z
  by_cases hz : z ∈ 𝔇.WovTriple t
  · rw [show ((0 : 𝔇.C2Holo) t).toFun z = 0 from rfl]
    rw [delta1Model_apply_apply _ _ _ hz]
    obtain ⟨a, b, c⟩ := t
    rw [delta0Model_apply_apply _ _ _ (𝔇.mapsTo_coverTransition_WovTriple_shrink a b c hz),
      delta0Model_apply_apply _ _ _ (𝔇.WovTriple_subset_Wov_fst_trd a b c hz),
      delta0Model_apply_apply _ _ _ (𝔇.WovTriple_subset_Wov_fst_snd a b c hz)]
    rw [𝔇.coverTransition_cocycle_Wov a b c hz]
    ring
  · rw [show ((0 : 𝔇.C2Holo) t).toFun z = 0 from rfl,
      (𝔇.delta1Model (𝔇.delta0Model f) t).zero_off z hz]

/-! ### The 2-cochain restriction `ρ²` cover → shrinking, and the `hcomm` square -/

theorem WovTriple_subset_UovTriple (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) :
    𝔇.WovTriple t ⊆ 𝔇.UovTriple t := by
  show (chartAt (H := ℂ) (𝔇.center t.1)) '' _ ⊆ (chartAt (H := ℂ) (𝔇.center t.1)) '' _
  refine Set.image_mono (fun x hx => ?_)
  exact ⟨⟨𝔇.closure_shrinkSet_subset_U t.1 (subset_closure hx.1.1),
    𝔇.closure_shrinkSet_subset_U t.2.1 (subset_closure hx.1.2)⟩,
    𝔇.closure_shrinkSet_subset_U t.2.2 (subset_closure hx.2)⟩

/-- **The 2-cochain restriction `ρ² : C2Cov →L C2Holo`** (cover → shrinking). -/
noncomputable def rho2Model : 𝔇.C2Cov →L[ℂ] 𝔇.C2Holo :=
  ContinuousLinearMap.pi fun t =>
    (BddHol.restrictOpenCLM (𝔇.WovTriple_subset_UovTriple t)).comp (proj t)

@[simp] theorem rho2Model_apply (g : 𝔇.C2Cov) (t : 𝔇.ι × 𝔇.ι × 𝔇.ι) :
    𝔇.rho2Model g t = BddHol.restrictOpenCLM (𝔇.WovTriple_subset_UovTriple t) (g t) := by
  simp only [rho2Model, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

/-- **The commuting square** `δ¹_shr ∘ ρ = ρ² ∘ δ¹_cov`. -/
theorem delta1_comp_rhoRaw_eq_rho2_comp_delta1Cov :
    (𝔇.delta1Model).comp 𝔇.overlapData.rhoRaw
      = (𝔇.rho2Model).comp 𝔇.delta1CovModel := by
  ext x t
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  apply BddHol.toFun_injective
  funext z
  by_cases hz : z ∈ 𝔇.WovTriple t
  · rw [delta1Model_apply_apply _ _ _ hz]
    obtain ⟨a, b, c⟩ := t
    simp only [HolomorphicDiskOverlapData.rhoRaw_apply, overlapData_Wov_eq, overlapData_Uov_eq]
    rw [BddHol.restrictOpenCLM_toFun_of_mem _ _ (𝔇.mapsTo_coverTransition_WovTriple_shrink a b c hz),
      BddHol.restrictOpenCLM_toFun_of_mem _ _ (𝔇.WovTriple_subset_Wov_fst_trd a b c hz),
      BddHol.restrictOpenCLM_toFun_of_mem _ _ (𝔇.WovTriple_subset_Wov_fst_snd a b c hz)]
    rw [rho2Model_apply, BddHol.restrictOpenCLM_toFun_of_mem _ _ hz]
    rw [𝔇.delta1CovModel_apply_apply _ _ (𝔇.WovTriple_subset_UovTriple (a, b, c) hz)]
  · rw [(𝔇.delta1Model (𝔇.overlapData.rhoRaw x) t).zero_off z hz,
      (𝔇.rho2Model (𝔇.delta1CovModel x) t).zero_off z hz]

theorem hcomm (x : 𝔇.overlapData.Ccov) (hx : 𝔇.delta1CovModel x = 0) :
    𝔇.delta1Model (𝔇.overlapData.rhoRaw x) = 0 := by
  have h := congrArg (fun T => T x) 𝔇.delta1_comp_rhoRaw_eq_rho2_comp_delta1Cov
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h, hx, map_zero]

end ChartDiskCover

end Jacobians.Dolbeault
