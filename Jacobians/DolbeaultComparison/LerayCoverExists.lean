
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The geometric core — a chart-ball-preimage is simply connected -/

/-- **A chart-preimage of a coordinate ball is simply connected.** Let
`e : OpenPartialHomeomorph X ℂ` be a chart and `ball cc r ⊆ e.target` a coordinate ball inside its
target. Then the open set `e.source ∩ e ⁻¹' (ball cc r)` (the chart-preimage of the ball — a
coordinate disk in `X`) is a `SimplyConnectedSpace`.

The chart restricted to this set is a homeomorphism onto `ball cc r ⊆ ℂ`
(`e.restr` has source the set and target `ball cc r`, by `e.right_inv` on the target;
`OpenPartialHomeomorph.toHomeomorphSourceTarget`).  The ball is contractible
(`Metric.contractibleSpace_ball`), contractibility transports across the homeomorphism
(`Homeomorph.contractibleSpace`), and a contractible space is simply connected
(`SimplyConnectedSpace.ofContractible`, an instance). -/
theorem simplyConnectedSpace_chartBallPreimage {X : Type*} [TopologicalSpace X]
    (e : OpenPartialHomeomorph X ℂ) (cc : ℂ) (r : ℝ)
    (hr : 0 < r) (hB : Metric.ball cc r ⊆ e.target) :
    SimplyConnectedSpace ↥(e.source ∩ e ⁻¹' Metric.ball cc r) := by
  set B := Metric.ball cc r with hBdef
  set U := e.source ∩ e ⁻¹' B with hUdef
  have hUopen : IsOpen U :=
    e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
  have hUsub : U ⊆ e.source := Set.inter_subset_left
  -- Restrict the chart to the OPEN set `U`; its source is `U`, its target is `B`.
  set e' := e.restr U with he'
  have hsrc : e'.source = U := by
    rw [he', e.restr_source' U hUopen, Set.inter_eq_right.mpr hUsub]
  have htgt : e'.target = B := by
    rw [he', OpenPartialHomeomorph.restr_target, hUopen.interior_eq]
    ext y
    simp only [Set.mem_inter_iff, Set.mem_preimage, hUdef]
    constructor
    · rintro ⟨hyt, _, hyB⟩
      rwa [e.right_inv hyt] at hyB
    · intro hyB
      have hyt : y ∈ e.target := hB hyB
      exact ⟨hyt, e.map_target hyt, by rwa [e.right_inv hyt]⟩
  -- Transport contractibility `ball → e'.target → e'.source = U`, then `ofContractible`.
  have hballC : ContractibleSpace ↥B := Metric.contractibleSpace_ball hr
  have htgtC : ContractibleSpace ↥(e'.target) := htgt ▸ hballC
  have hsrcC : ContractibleSpace ↥(e'.source) := e'.toHomeomorphSourceTarget.contractibleSpace
  rw [hsrc] at hsrcC
  haveI := hsrcC
  infer_instance

/-! ### Per-point chart-ball neighborhoods -/

/-- The radius of a coordinate ball around `(chartAt ℂ x) x` that fits inside the chart target.
Exists because `(chartAt ℂ x) x ∈ (chartAt ℂ x).target` and the target is open
(`Metric.isOpen_iff`). -/
noncomputable def chartBallRadius (x : X) : ℝ :=
  Classical.choose (Metric.isOpen_iff.mp (chartAt ℂ x).open_target ((chartAt ℂ x) x)
    ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))

theorem chartBallRadius_spec {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) :
    0 < chartBallRadius x ∧
      Metric.ball ((chartAt ℂ x) x) (chartBallRadius x) ⊆ (chartAt ℂ x).target :=
  Classical.choose_spec (Metric.isOpen_iff.mp (chartAt ℂ x).open_target ((chartAt ℂ x) x)
    ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))

theorem chartBallRadius_pos {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) :
    0 < chartBallRadius x := (chartBallRadius_spec x).1

theorem ball_chartBallRadius_subset_target {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) :
    Metric.ball ((chartAt ℂ x) x) (chartBallRadius x) ⊆ (chartAt ℂ x).target :=
  (chartBallRadius_spec x).2

/-- **`exists_lerayCover` from any cover with simply-connected sets.** Trivial repackaging — kept as
an alternative entry point. Subsumed by the unconditional `exists_lerayCover` (the canonical
chart-disk cover already has simply-connected sets); offered for an owner who would rather supply a
different good cover. -/
theorem exists_lerayCover_of_goodCover {X : Type*} [TopologicalSpace X]
    (hGood : ∃ 𝔘 : FiniteCover X, ∀ i, SimplyConnectedSpace ↥(𝔘.U i)) :
    ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray :=
  hGood

/-! ### A concrete chart-disk cover

The `chartBallCover` above is enough for `IsLeray`, but the downstream Dolbeault comparison and
skyscraper assembly want the stronger `ChartDiskCover` shape.  We obtain it by halving the radius:
the open ball around each point still contains the center, the family still covers by compactness,
and the closed ball of the half-radius lies inside the open ball used above. -/

/-- The radius of a smaller chart disk around `x`, chosen as half of `chartBallRadius x`. -/
noncomputable def chartDiskRadius (x : X) : ℝ :=
  chartBallRadius (X := X) x / 2

theorem chartDiskRadius_pos {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) :
    0 < chartDiskRadius (X := X) x := by
  dsimp [chartDiskRadius]
  simpa using (half_pos (chartBallRadius_pos (X := X) x))

theorem closedBall_chartDiskRadius_subset_target {X : Type*} [TopologicalSpace X]
    [ChartedSpace ℂ X] (x : X) :
    Metric.closedBall ((chartAt ℂ x) x) (chartDiskRadius (X := X) x) ⊆
      (chartAt ℂ x).target := by
  dsimp [chartDiskRadius]
  have hlt : chartBallRadius (X := X) x / 2 < chartBallRadius x := by
    simpa [chartDiskRadius] using (half_lt_self (chartBallRadius_pos (X := X) x))
  exact (Metric.closedBall_subset_ball hlt).trans (ball_chartBallRadius_subset_target (X := X) x)

/-- The smaller chart-disk neighborhood of `x`. This is the cover set that feeds the
`ChartDiskCover` API. -/
def chartDiskNbhd (x : X) : Set X :=
  (chartAt ℂ x).source ∩
    (chartAt ℂ x) ⁻¹' Metric.ball ((chartAt ℂ x) x) (chartDiskRadius (X := X) x)

theorem chartDiskNbhd_isOpen {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) :
    IsOpen (chartDiskNbhd (X := X) x) :=
  (chartAt ℂ x).continuousOn.isOpen_inter_preimage (chartAt ℂ x).open_source Metric.isOpen_ball

theorem mem_chartDiskNbhd {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] (x : X) :
    x ∈ chartDiskNbhd (X := X) x :=
  ⟨mem_chart_source ℂ x, by
    simp only [Set.mem_preimage]; exact Metric.mem_ball_self (chartDiskRadius_pos (X := X) x)⟩

theorem simplyConnectedSpace_chartDiskNbhd {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    (x : X) :
    SimplyConnectedSpace ↥(chartDiskNbhd (X := X) x) :=
  simplyConnectedSpace_chartBallPreimage (chartAt ℂ x) _ _ (chartDiskRadius_pos (X := X) x)
    (by
      intro z hz
      exact closedBall_chartDiskRadius_subset_target (X := X) x
        (by simpa [Metric.mem_closedBall] using le_of_lt hz))

theorem exists_finite_chartDiskNbhd_cover {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [CompactSpace X] :
    ∃ s : Finset X, (⋃ x ∈ s, chartDiskNbhd (X := X) x) = Set.univ := by
  have hcov : Set.univ ⊆ ⋃ x : X, chartDiskNbhd (X := X) x := fun y _ =>
    Set.mem_iUnion.mpr ⟨y, mem_chartDiskNbhd (X := X) y⟩
  obtain ⟨s, hs⟩ := IsCompact.elim_finite_subcover isCompact_univ
    (fun x : X => chartDiskNbhd (X := X) x) (fun x => chartDiskNbhd_isOpen (X := X) x) hcov
  exact ⟨s, Set.eq_univ_of_univ_subset hs⟩

/-- The finite set of centres of the canonical chart-disk cover. -/
noncomputable def chartDiskCenters : Finset X :=
  Classical.choose (exists_finite_chartDiskNbhd_cover (X := X))

theorem chartDiskCenters_cover {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
    [CompactSpace X] :
    (⋃ x ∈ (chartDiskCenters : Finset X), chartDiskNbhd (X := X) x) = Set.univ :=
  Classical.choose_spec (exists_finite_chartDiskNbhd_cover (X := X))

/-- The element of `X` indexed by `Fin (chartDiskCenters.card)`. -/
noncomputable def chartDiskCenter (i : Fin (chartDiskCenters (X := X)).card) : X :=
  ((chartDiskCenters (X := X)).equivFin.symm i : X)

/-- The canonical finite chart-disk cover of a compact Riemann surface. -/
noncomputable def chartDiskCover : ChartDiskCover X where
  ι := Fin (chartDiskCenters (X := X)).card
  U := fun i => ⟨chartDiskNbhd (chartDiskCenter i), chartDiskNbhd_isOpen (X := X) _⟩
  covers := by
    rw [← TopologicalSpace.Opens.coe_inj, TopologicalSpace.Opens.coe_iSup]
    show (⋃ i : Fin (chartDiskCenters (X := X)).card, chartDiskNbhd (chartDiskCenter i)) = _
    have hreindex :
        (⋃ i : Fin (chartDiskCenters (X := X)).card, chartDiskNbhd (chartDiskCenter i))
          = ⋃ j : {x // x ∈ (chartDiskCenters (X := X))}, chartDiskNbhd j.1 :=
      ((chartDiskCenters (X := X)).equivFin.symm.surjective).iUnion_comp
        (fun j : {x // x ∈ (chartDiskCenters (X := X))} => chartDiskNbhd j.1)
    rw [hreindex, Set.iUnion_subtype, chartDiskCenters_cover]
    rfl
  center := chartDiskCenter (X := X)
  radius := fun _ => chartDiskRadius (X := X) _
  radius_pos := fun i => chartDiskRadius_pos (X := X) _
  closedBall_subset_target := fun i => by
    simpa using closedBall_chartDiskRadius_subset_target (X := X) (chartDiskCenter i)
  isDisk := by
    intro i
    simp [chartDiskNbhd, chartDiskRadius, Set.inter_comm, mfld_simps]

@[simp] theorem chartDiskCover_U (i : (chartDiskCover (X := X)).ι) :
    ((chartDiskCover (X := X)).U i : Set X) = chartDiskNbhd (chartDiskCenter i) := rfl

/-- Every set of the canonical chart-disk cover is simply connected. -/
theorem chartDiskCover_simplyConnected (i : (chartDiskCover (X := X)).ι) :
    SimplyConnectedSpace ↥((chartDiskCover (X := X)).U i) :=
  simplyConnectedSpace_chartDiskNbhd (chartDiskCenter (X := X) i)

/-- A concrete chart-disk Leray cover exists. -/
theorem exists_chartDiskCover : ∃ 𝔇 : ChartDiskCover X, 𝔇.toFiniteCover.IsLeray :=
  ⟨chartDiskCover (X := X), chartDiskCover_simplyConnected (X := X)⟩

/-- **`exists_lerayCover` — UNCONDITIONAL.** `X` admits a finite Leray cover: the canonical
chart-disk cover `chartDiskCover`, whose sets are simply connected
(`chartDiskCover_simplyConnected`) — which is *all* `IsLeray` now requires (its overlap conjunct was
dropped as dead weight; for `H¹` Cartan needs only acyclic sets — see
`CechComplex.FiniteFamily.IsLeray` and `GoodCover`).

This is the statement that unlocks the ladder→headline wiring
(`RiemannRoch.exists_riemannRoch_divisor` via `DolbeaultLadder.riemannRoch_equality_of_ladder 𝔘 hL`
with this `𝔘 = chartDiskCover` and `hL` the produced `IsLeray`).  Previously gated on the good-cover
overlap-preconnectedness `hOverlaps` (a Mathlib-absent Whitney geodesic-convexity fact); that
hypothesis is now eliminated, so the wiring is unconditional. -/
theorem exists_lerayCover : ∃ 𝔘 : FiniteCover X, 𝔘.IsLeray :=
  ⟨(chartDiskCover (X := X)).toFiniteCover, by
    intro i
    simpa using chartDiskCover_simplyConnected (X := X) i⟩

end Jacobians.Dolbeault
