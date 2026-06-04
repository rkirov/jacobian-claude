/-
  Dolbeault ladder — discharging `HasChartAnalyticCorrectors 𝔙` for a **shared-chart disk cover**:
  the ball-solve that the `CechDiskAcyclicAssembly` chain reduced germ `H¹(disk, 𝒪) = 0` to.

  `CechDiskAcyclicAssembly` reduced germ-level `H¹(disk, 𝒪) = 0` sorry-free to the single honest
  predicate `HasChartAnalyticCorrectors 𝔙` (ambient chart-analytic correctors `H_i : X → ℂ` whose
  differences split the cocycle's analytic representatives `holoFn (s_{ij})` off a discrete set on
  each overlap), via `cechH1_subsingleton_of_chartAnalyticCorrectors`.  This file PRODUCES
  `HasChartAnalyticCorrectors 𝔙` for a cover all of whose sets live in a single chart `φ = chartAt ℂ c₀`
  and pull back to opens `Ω_i ⊆ ball ⊆ ℂ` covering the ball — STEP C of the obstruction map.

  ## Why PORT, not import the PoU machinery

  The PoU primitives (`cechPoU` / `primFn` / `cechTerm` and the real-smooth bridges
  `contMDiffAt_real_of_chart_analyticAt` / `contMDiffMul_real_complex`) live in
  `DolbeaultComparisonInverse`, but that file defines EIGHT declarations (`holoRep`, `holoFn`,
  `gextLimRep_chart_analyticAt`, …) whose names collide with `CechDiskAcyclicProof`'s re-derivation of
  the same toolkit, so the two cannot be imported together.  We therefore PORT the PoU machinery we
  need into this file (copying the proofs), importing the lighter clash-free `DolbeaultComparison`
  (forms / `proj01L`) rather than `DolbeaultComparisonInverse`, and REUSE by import
  `CechDiskAcyclicProof` (`holoFn` / `toGerm_holoFn` / `chartHoloRep*` / `ballSplit_glued` /
  `dbar_fun_sum`), `DbarDiskCohomology` (`dbar_solvable_ball`), and `ChartDiskCover`.

  NO `sorry` anywhere: everything not sorry-free is a hypothesis predicate or written prose.
-/
import Jacobians.Dolbeault.CechDiskAcyclicAssembly
import Jacobians.Dolbeault.DolbeaultComparison
import Jacobians.Dolbeault.DbarDiskCohomology
import Jacobians.Dolbeault.ChartDiskCover
import Mathlib.Geometry.Manifold.PartitionOfUnity

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Complex Metric Filter

-- Same permissive transparency as `DolbeaultComparison` (in force via that import for the hom-bundle
-- section instances; any `ContMDiffSection`/section-`ext` here needs it).
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## §0 — Ported partition-of-unity machinery (fallback rung (a))

`DolbeaultComparisonInverse` builds the PoU primitives (`cechPoU` / `rhoC` / `primFn` / `cechTerm`)
and the real-smooth bridges, but it cannot be imported here (it re-derives — under the same names —
the `holoRep`/`holoFn`/… toolkit that `CechDiskAcyclicProof`, imported here, also derives: eight
name clashes in `Jacobians.Dolbeault`).  So we PORT the pieces we need, copying the proofs verbatim,
over a generic `FiniteCover` (the originals are over `ChartDiskCover`; nothing here uses the disk
fields).  The lighter `DolbeaultComparison` (forms / `proj01L`) is clash-free and imported. -/

/-- `ℝ → ℂ` as a smooth map (for coercing the real-valued PoU functions to `SmoothCFunctions`).
Port of `DolbeaultComparisonInverse.ofRealCM`. -/
noncomputable def ofRealCM : ContMDiffMap (𝓘(ℝ)) (𝓘(ℝ, ℂ)) ℝ ℂ (⊤ : ℕ∞) :=
  ⟨Complex.ofReal, Complex.ofRealCLM.contMDiff⟩

variable [Nonempty X]

/-- A smooth partition of unity subordinate to a finite cover `𝔘`, over the real-manifold structure
`𝓘(ℝ, ℂ)` (a compact `T2` `ℂ`-manifold is a `σ`-compact finite-dim real manifold). Port of
`DolbeaultComparisonInverse.exists_smoothPartitionOfUnity_subordinate`. -/
theorem exists_smoothPartitionOfUnity_subordinate (𝔘 : FiniteCover X) :
    ∃ ρ : SmoothPartitionOfUnity 𝔘.ι 𝓘(ℝ, ℂ) X (Set.univ : Set X),
      ρ.IsSubordinate (fun i => (𝔘.U i : Set X)) := by
  have hcov : (Set.univ : Set X) ⊆ ⋃ i, (𝔘.U i : Set X) := by
    rw [Set.univ_subset_iff, ← TopologicalSpace.Opens.coe_iSup, 𝔘.covers]; rfl
  exact SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ
    (fun i => (𝔘.U i : Set X)) (fun i => (𝔘.U i).isOpen) hcov

/-- A fixed smooth partition of unity subordinate to the cover. Port of
`DolbeaultComparisonInverse.cechPoU`, over a generic `FiniteCover`. -/
noncomputable def coverPoU (𝔘 : FiniteCover X) :
    SmoothPartitionOfUnity 𝔘.ι 𝓘(ℝ, ℂ) X (Set.univ : Set X) :=
  (exists_smoothPartitionOfUnity_subordinate 𝔘).choose

theorem coverPoU_subordinate (𝔘 : FiniteCover X) :
    (coverPoU 𝔘).IsSubordinate (fun i => (𝔘.U i : Set X)) :=
  (exists_smoothPartitionOfUnity_subordinate 𝔘).choose_spec

/-- The `k`-th PoU function as a complex `SmoothCFunctions` (`ρ̃_k = ofReal ∘ ρ_k`). Port of
`DolbeaultComparisonInverse.rhoC`. -/
noncomputable def rhoC (𝔘 : FiniteCover X) (k : 𝔘.ι) : SmoothCFunctions X :=
  ofRealCM.comp (coverPoU 𝔘 k)

/-- The PoU functions sum to the constant `1`. Port of `DolbeaultComparisonInverse.sum_rhoC`. -/
theorem sum_rhoC (𝔘 : FiniteCover X) : ∑ k, rhoC 𝔘 k = 1 := by
  refine ContMDiffMap.ext fun x => ?_
  have h1 : (⇑(∑ k, rhoC 𝔘 k) : X → ℂ) = ∑ k, ⇑(rhoC 𝔘 k) :=
    map_sum ContMDiffMap.coeFnAddMonoidHom _ _
  rw [show (∑ k, rhoC 𝔘 k) x = (⇑(∑ k, rhoC 𝔘 k) : X → ℂ) x from rfl, h1, Finset.sum_apply,
    ContMDiffMap.coe_one, Pi.one_apply]
  show ∑ k, ((coverPoU 𝔘 k x : ℝ) : ℂ) = 1
  rw [← Complex.ofReal_sum, ← finsum_eq_sum_of_fintype,
    (coverPoU 𝔘).sum_eq_one (Set.mem_univ x), Complex.ofReal_one]

/-- Value form of `sum_rhoC`: `∑_k ρ_k x = 1` pointwise. -/
theorem sum_rhoC_apply (𝔘 : FiniteCover X) (x : X) : ∑ k, (rhoC 𝔘 k x) = 1 := by
  have h1 : (⇑(∑ k, rhoC 𝔘 k) : X → ℂ) = ∑ k, ⇑(rhoC 𝔘 k) :=
    map_sum ContMDiffMap.coeFnAddMonoidHom _ _
  have h2 : (∑ k, rhoC 𝔘 k) x = ∑ k, (rhoC 𝔘 k x) := by
    rw [show ((∑ k, rhoC 𝔘 k) x : ℂ) = (⇑(∑ k, rhoC 𝔘 k) : X → ℂ) x from rfl, h1, Finset.sum_apply]
  rw [← h2, sum_rhoC, ContMDiffMap.coe_one, Pi.one_apply]

/-- `rhoC 𝔘 k x = 0` for `x ∉ tsupport ρ_k` (the real PoU function vanishes there). -/
theorem rhoC_eq_zero_of_notMem (𝔘 : FiniteCover X) (k : 𝔘.ι) {x : X}
    (hx : x ∉ tsupport (coverPoU 𝔘 k)) : rhoC 𝔘 k x = 0 := by
  simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, image_eq_zero_of_notMem_tsupport hx]; rfl

/-- **Chart-analytic ⟹ real-smooth.** If `h` read in the chart at `y` is `ℂ`-analytic at the chart
image, then `h` is real-`C^∞` (`ContMDiffAt 𝓘(ℝ,ℂ)`) at `y`. Port of
`DolbeaultComparisonInverse.contMDiffAt_real_of_chart_analyticAt`. -/
theorem contMDiffAt_real_of_chart_analyticAt {h : X → ℂ} {y : X}
    (ha : AnalyticAt ℂ (h ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y)) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) h y := by
  have hcd : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (h ∘ (chartAt (H := ℂ) y).symm)
      ((chartAt (H := ℂ) y) y) :=
    ((ha.contDiffAt.restrict_scalars ℝ).contMDiffAt).of_le le_top
  have hchart : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (chartAt (H := ℂ) y) y :=
    (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := y)).contMDiffAt
      ((chartAt (H := ℂ) y).open_source.mem_nhds (mem_chart_source ℂ y))
  refine (hcd.comp y hchart).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt (H := ℂ) y).open_source.mem_nhds (mem_chart_source ℂ y)] with z hz
  simp only [Function.comp_apply, (chartAt (H := ℂ) y).left_inv hz]

/-- `ℂ`-multiplication is real-`C^∞` (it is `ℝ`-bilinear). Port of
`DolbeaultComparisonInverse.contMDiffMul_real_complex` — makes `SmoothCFunctions X` a ring. -/
instance contMDiffMul_real_complex : ContMDiffMul 𝓘(ℝ, ℂ) (⊤ : ℕ∞) ℂ :=
  { (inferInstance : IsManifold 𝓘(ℝ, ℂ) (⊤ : ℕ∞) ℂ) with
    contMDiff_mul := by
      rw [contMDiff_iff]
      refine ⟨continuous_mul, fun x y => ?_⟩
      simp only [mfld_simps]
      rw [contDiffOn_univ]
      exact contDiff_mul }

/-- The analytic representative `holoFn hg` of a holomorphic germ on `↥W` is real-`C^∞`
(`ContMDiffAt 𝓘(ℝ,ℂ)`) at every `y ∈ W` (chart-analytic, `holoFn_chart_analyticAt`, bridged to
`ContMDiffAt` by `contMDiffAt_real_of_chart_analyticAt`). The function-level analogue of
`DolbeaultComparisonInverse.holoFn_contMDiffAt`, here over the imported `CechDiskAcyclicProof.holoFn`. -/
theorem holoFn_contMDiffAt {W : Opens X} {g : MGerm W} (hg : g ∈ OmegaDGerm (0 : Divisor X) W)
    {y : X} (hy : y ∈ W) : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (holoFn hg) y :=
  contMDiffAt_real_of_chart_analyticAt (holoFn_chart_analyticAt hg hy)

/-! ### Ported `holoFn` algebra (limit-repair washout lemmas)

The cocycle-difference identity `h_j − h_i = holoFn(s_{ij})` needs `holoFn` to be subtractive,
restriction-compatible, and germ-class-dependent.  These are ports of `DolbeaultComparisonInverse`'s
`holoFn_tendsto` / `holoFn_sub` / `holoFn_restrict` / `holoFn_congr`, re-derived over the imported
`CechDiskAcyclicProof.holoFn` (which is the same `limUnder (𝓝[≠] x) (Gext (holoRep hg))`). -/

/-- `Gext` respects subtraction (extension by `0`). Port of `DolbeaultComparisonInverse.Gext_sub`. -/
theorem Gext_sub {U : Opens X} (f g : U → ℂ) : Gext (f - g) = Gext f - Gext g := by
  funext x
  simp only [Gext, Pi.sub_apply]
  split <;> simp

/-- For a holomorphic germ class, `Gext (holoRep hg)` has a genuine limit along `𝓝[≠] x` at every
`x ∈ W`. Port of `DolbeaultComparisonInverse.holoFn_tendsto`. -/
theorem holoFn_tendsto {W : Opens X} {g : MGerm W} (hg : g ∈ OmegaDGerm (0 : Divisor X) W) {x : X}
    (hx : x ∈ W) : ∃ c, Tendsto (Gext (holoRep hg)) (𝓝[≠] x) (𝓝 c) := by
  set φ := chartAt (H := ℂ) x with hφ
  have hmero : MeromorphicAt (Gext (holoRep hg) ∘ φ.symm) (φ x) :=
    Gext_meromorphicAt (holoRep_mem hg).1 hx
  have hord : 0 ≤ meromorphicOrderAt (Gext (holoRep hg) ∘ φ.symm) (φ x) := by
    rw [← ordU_eq_orderAt_Gext (holoRep hg) hx]; simpa using (mem_OmegaD.1 (holoRep_mem hg)).2 ⟨x, hx⟩
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hmero hord
  refine ⟨c, (hc.comp (φ.tendsto_nhdsNE (mem_chart_source ℂ x))).congr' ?_⟩
  filter_upwards [mem_nhdsWithin_of_mem_nhds (φ.open_source.mem_nhds (mem_chart_source ℂ x))] with z hz
  simp [Function.comp, φ.left_inv hz]

/-- **`holoFn` respects subtraction** at `x ∈ W`. Port of `DolbeaultComparisonInverse.holoFn_sub`. -/
theorem holoFn_sub {W : Opens X} {g₁ g₂ : MGerm W} (hg₁ : g₁ ∈ OmegaDGerm (0 : Divisor X) W)
    (hg₂ : g₂ ∈ OmegaDGerm (0 : Divisor X) W) (hg : g₁ - g₂ ∈ OmegaDGerm (0 : Divisor X) W)
    {x : X} (hx : x ∈ W) : holoFn hg x = holoFn hg₁ x - holoFn hg₂ x := by
  haveI := nhdsNE_neBot x
  obtain ⟨c₁, hc₁⟩ := holoFn_tendsto hg₁ hx
  obtain ⟨c₂, hc₂⟩ := holoFn_tendsto hg₂ hx
  have hgerm : toGerm W (holoRep hg₁ - holoRep hg₂) = toGerm W (holoRep hg) := by
    rw [map_sub, toGerm_holoRep hg₁, toGerm_holoRep hg₂, toGerm_holoRep hg]
  have heq : Gext (holoRep hg) =ᶠ[𝓝[≠] x] Gext (holoRep hg₁) - Gext (holoRep hg₂) := by
    have hmatch : rawRestrictG (inf_le_right : W ⊓ W ≤ W) (toGerm W (holoRep hg₁ - holoRep hg₂))
        = rawRestrictG (inf_le_left : W ⊓ W ≤ W) (toGerm W (holoRep hg)) := by rw [hgerm]
    have h := Gext_overlap_eventuallyEq (holoRep hg) (holoRep hg₁ - holoRep hg₂) hmatch hx hx
    rwa [Gext_sub] at h
  show limUnder (𝓝[≠] x) (Gext (holoRep hg)) = holoFn hg₁ x - holoFn hg₂ x
  rw [show holoFn hg₁ x = c₁ from hc₁.limUnder_eq, show holoFn hg₂ x = c₂ from hc₂.limUnder_eq]
  exact ((hc₁.sub hc₂).congr' heq.symm).limUnder_eq

/-- **`holoFn` depends only on the germ class.** Port of `DolbeaultComparisonInverse.holoFn_congr`. -/
theorem holoFn_congr {W : Opens X} {g g' : MGerm W} (hg : g ∈ OmegaDGerm (0 : Divisor X) W)
    (hg' : g' ∈ OmegaDGerm (0 : Divisor X) W) (hgg : g = g') {x : X} (hx : x ∈ W) :
    holoFn hg x = holoFn hg' x := by
  haveI := nhdsNE_neBot x
  have heq : Gext (holoRep hg) =ᶠ[𝓝[≠] x] Gext (holoRep hg') := by
    have hgerm : toGerm W (holoRep hg') = toGerm W (holoRep hg) := by
      rw [toGerm_holoRep, toGerm_holoRep, hgg]
    have hmatch : rawRestrictG (inf_le_right : W ⊓ W ≤ W) (toGerm W (holoRep hg'))
        = rawRestrictG (inf_le_left : W ⊓ W ≤ W) (toGerm W (holoRep hg)) := by rw [hgerm]
    exact Gext_overlap_eventuallyEq (holoRep hg) (holoRep hg') hmatch hx hx
  exact congrArg Filter.lim (Filter.map_congr heq)

/-- **`holoFn` is restriction-compatible.** Port of `DolbeaultComparisonInverse.holoFn_restrict`. -/
theorem holoFn_restrict {U W : Opens X} (h : W ≤ U) {g : MGerm U}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) U) {x : X} (hx : x ∈ W) :
    holoFn (rawRestrictG_omegaDGerm h hg) x = holoFn hg x := by
  haveI := nhdsNE_neBot x
  have heq : Gext (holoRep hg) =ᶠ[𝓝[≠] x] Gext (holoRep (rawRestrictG_omegaDGerm h hg)) := by
    have hmatch : rawRestrictG (inf_le_right : U ⊓ W ≤ W)
          (toGerm W (holoRep (rawRestrictG_omegaDGerm h hg)))
        = rawRestrictG (inf_le_left : U ⊓ W ≤ U) (toGerm U (holoRep hg)) := by
      rw [toGerm_holoRep, toGerm_holoRep, FiniteCover.rawRestrictG_comp_apply]
    exact Gext_overlap_eventuallyEq (holoRep hg) (holoRep (rawRestrictG_omegaDGerm h hg)) hmatch
      (h hx) hx
  show limUnder (𝓝[≠] x) (Gext (holoRep (rawRestrictG_omegaDGerm h hg)))
    = limUnder (𝓝[≠] x) (Gext (holoRep hg))
  exact congrArg Filter.lim (Filter.map_congr heq.symm)

/-- **The cocycle relation at the `holoFn` value level.** For an `𝒪`-cocycle `s` and a point `y` in
the triple overlap `U_q ⊓ U_i ⊓ U_j`, the analytic representatives satisfy
`holoFn(s_{qj}) y − holoFn(s_{qi}) y = holoFn(s_{ij}) y`.  From `δ¹s = 0` the germs obey
`s_{qj} = s_{qi} + s_{ij}` on the triple overlap; `holoFn` is subtractive (`holoFn_sub`) and
restriction-compatible (`holoFn_restrict`).  Port/adaptation of
`DolbeaultComparisonInverse.holoFn_cocycle_add`. -/
theorem holoFn_cocycle_sub (𝔙 : FiniteCover X) (s : ↥(𝔙.cocycles1 (0 : Divisor X)))
    (q i j : 𝔙.ι) {y : X} (hy : y ∈ (𝔙.U q ⊓ 𝔙.U i ⊓ 𝔙.U j : Opens X)) :
    holoFn (cocycleComp_mem 𝔙 s q j) y - holoFn (cocycleComp_mem 𝔙 s q i) y
      = holoFn (cocycleComp_mem 𝔙 s i j) y := by
  -- The triple-overlap restrictions.
  have hqj : (𝔙.U q ⊓ 𝔙.U i ⊓ 𝔙.U j : Opens X) ≤ 𝔙.U q ⊓ 𝔙.U j :=
    le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hqi : (𝔙.U q ⊓ 𝔙.U i ⊓ 𝔙.U j : Opens X) ≤ 𝔙.U q ⊓ 𝔙.U i := inf_le_left
  have hij : (𝔙.U q ⊓ 𝔙.U i ⊓ 𝔙.U j : Opens X) ≤ 𝔙.U i ⊓ 𝔙.U j :=
    le_inf (inf_le_left.trans inf_le_right) inf_le_right
  -- `δ¹s = 0` gives the germ relation `s_{qj} − s_{qi} + s_{ij} = 0` on the triple overlap.
  have hk0 : 𝔙.cechDelta1 (s : 𝔙.Cochain1) = 0 :=
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 s.2).1
  -- `(δ¹s)_{qij} = s_{ij}|△ − s_{qj}|△ + s_{qi}|△ = 0` (the `cechDelta1` index convention).
  have h0 : rawRestrictG hij ((s : 𝔙.Cochain1) (i, j))
      - rawRestrictG hqj ((s : 𝔙.Cochain1) (q, j))
      + rawRestrictG hqi ((s : 𝔙.Cochain1) (q, i)) = 0 := by
    have hev := congrFun hk0 (q, i, j)
    simpa only [FiniteCover.cechDelta1, LinearMap.pi_apply, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.comp_apply, LinearMap.proj_apply, Pi.zero_apply] using hev
  -- Rearranged: `s_{qj}|_△ − s_{qi}|_△ = s_{ij}|_△`.
  have hrel : rawRestrictG hqj ((s : 𝔙.Cochain1) (q, j))
        - rawRestrictG hqi ((s : 𝔙.Cochain1) (q, i))
      = rawRestrictG hij ((s : 𝔙.Cochain1) (i, j)) := by
    linear_combination (norm := module) -h0
  -- Read it back through `holoFn` (subtractive + restriction-compatible + germ-congruent).
  rw [← holoFn_restrict hqj (cocycleComp_mem 𝔙 s q j) hy,
    ← holoFn_restrict hqi (cocycleComp_mem 𝔙 s q i) hy,
    ← holoFn_sub (rawRestrictG_omegaDGerm hqj (cocycleComp_mem 𝔙 s q j))
      (rawRestrictG_omegaDGerm hqi (cocycleComp_mem 𝔙 s q i))
      (sub_mem (rawRestrictG_omegaDGerm hqj (cocycleComp_mem 𝔙 s q j))
        (rawRestrictG_omegaDGerm hqi (cocycleComp_mem 𝔙 s q i))) hy,
    holoFn_congr (sub_mem (rawRestrictG_omegaDGerm hqj (cocycleComp_mem 𝔙 s q j))
        (rawRestrictG_omegaDGerm hqi (cocycleComp_mem 𝔙 s q i)))
      (rawRestrictG_omegaDGerm hij (cocycleComp_mem 𝔙 s i j)) hrel hy,
    holoFn_restrict hij (cocycleComp_mem 𝔙 s i j) hy]

/-! ## §1 — The per-summand smoothness (fallback rung (b))

For the partition-of-unity globalization we form, on each cover set `U_i`, the primitive
`h_i := ∑_q ρ_q · holoFn (s_{qi})`.  Its `(q)`-summand is `primSummand 𝔙 s q i = rhoC q · holoFn(s_qi)`.
The cocycle component `s_{qi}` is a holomorphic germ on the OVERLAP `U_q ⊓ U_i`, so `holoFn(s_qi)` is
chart-analytic (hence `ContMDiffAt`) only on `U_q ⊓ U_i`.  Subordinateness puts `tsupport ρ_q ⊆ U_q`.

The crucial smoothness fact is therefore the *overlap* statement: `primSummand 𝔙 s q i` is
`ContMDiffAt` at every point of `U_i` (NOT at every point of `X` — at a point of `U_q ∖ U_i` where
`ρ_q ≠ 0` the holomorphic factor is junk).  This is the honest content of the 3-case
`tsupport`/overlap argument (`DolbeaultComparisonInverse.cechTerm`/`primFn`):

  * (a) `x₀ ∈ U_i` and `x₀ ∈ tsupport ρ_q`: then `x₀ ∈ U_q ⊓ U_i` (subordinateness), so both factors
    are smooth at `x₀` (`rhoC` always, `holoFn(s_qi)` by `holoFn_contMDiffAt` on the overlap);
  * (b) `x₀ ∈ U_i` and `x₀ ∉ tsupport ρ_q`: `ρ_q = 0` on a neighbourhood, so the product is locally
    `0`, hence smooth.
  These two opens cover `U_i`.  (The would-be third case `x₀ ∈ U_q ∖ U_i` is exactly the point where
  this object is NOT a global `SmoothCFunctions X` — which is why the construction confines `h_i` to
  `U_i`; see the status note.) -/

/-- The `(q)`-summand `ρ_q · holoFn(s_{qi})` of the cover-set primitive `h_i`, as a bare function. -/
noncomputable def primSummand (𝔙 : FiniteCover X) (s : ↥(𝔙.cocycles1 (0 : Divisor X)))
    (q i : 𝔙.ι) : X → ℂ :=
  fun x => rhoC 𝔙 q x * holoFn (cocycleComp_mem 𝔙 s q i) x

@[simp] theorem primSummand_apply (𝔙 : FiniteCover X) (s : ↥(𝔙.cocycles1 (0 : Divisor X)))
    (q i : 𝔙.ι) (x : X) :
    primSummand 𝔙 s q i x = rhoC 𝔙 q x * holoFn (cocycleComp_mem 𝔙 s q i) x := rfl

/-- **The per-summand overlap smoothness (fallback rung (b)).** `primSummand 𝔙 s q i = ρ_q ·
holoFn(s_{qi})` is `ContMDiffAt 𝓘(ℝ,ℂ)` at every `x₀ ∈ U_i`.  Two-case `tsupport`/overlap argument:
on `tsupport ρ_q` the point lies in `U_q ⊓ U_i` (so `holoFn(s_qi)` is `ContMDiffAt`), off it `ρ_q`
vanishes locally.  This is the honest function-level content of `cechTerm`/`primFn`. -/
theorem contMDiffAt_primSummand (𝔙 : FiniteCover X) (s : ↥(𝔙.cocycles1 (0 : Divisor X)))
    (q i : 𝔙.ι) {x₀ : X} (hx₀ : x₀ ∈ 𝔙.U i) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (primSummand 𝔙 s q i) x₀ := by
  by_cases hb : x₀ ∈ tsupport (coverPoU 𝔙 q)
  · -- (a) `x₀ ∈ U_q ⊓ U_i`: both factors smooth.
    have hxq : x₀ ∈ 𝔙.U q := coverPoU_subordinate 𝔙 q hb
    have hxov : x₀ ∈ (𝔙.U q ⊓ 𝔙.U i : Opens X) := ⟨hxq, hx₀⟩
    exact ((rhoC 𝔙 q).contMDiff x₀).mul (holoFn_contMDiffAt (cocycleComp_mem 𝔙 s q i) hxov)
  · -- (b) `x₀ ∉ tsupport ρ_q`: `ρ_q = 0` on a neighbourhood, product locally `0`.
    refine (contMDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(isClosed_tsupport (coverPoU 𝔙 q)).isOpen_compl.mem_nhds hb] with x hx
    simp only [primSummand_apply, rhoC_eq_zero_of_notMem 𝔙 q hx, zero_mul]

/-! ## §2 — The cover-set primitive `h_i` (fallback rung (c), manifold side)

`coverPrim 𝔙 s i = ∑_q ρ_q · holoFn(s_{qi})` is the partition-of-unity-globalized primitive on the
cover set `U_i`.  It is `ContMDiffAt` at every point of `U_i` (finite sum of the per-summand smooth
pieces of §1), and its pairwise differences telescope to the analytic representatives:
`h_j − h_i = holoFn(s_{ij})` on `U_i ⊓ U_j` (the cocycle relation `holoFn_cocycle_sub` + `∑ρ = 1`). -/

/-- The cover-set primitive `h_i = ∑_q ρ_q · holoFn(s_{qi}) : X → ℂ`, smooth on `U_i`. -/
noncomputable def coverPrim (𝔙 : FiniteCover X) (s : ↥(𝔙.cocycles1 (0 : Divisor X))) (i : 𝔙.ι) :
    X → ℂ :=
  fun x => ∑ q, primSummand 𝔙 s q i x

theorem coverPrim_apply (𝔙 : FiniteCover X) (s : ↥(𝔙.cocycles1 (0 : Divisor X))) (i : 𝔙.ι) (x : X) :
    coverPrim 𝔙 s i x = ∑ q, rhoC 𝔙 q x * holoFn (cocycleComp_mem 𝔙 s q i) x := rfl

/-- **`coverPrim` is `ContMDiffAt` on `U_i`** (finite sum of the per-summand smooth pieces). -/
theorem contMDiffAt_coverPrim (𝔙 : FiniteCover X) (s : ↥(𝔙.cocycles1 (0 : Divisor X))) (i : 𝔙.ι)
    {x₀ : X} (hx₀ : x₀ ∈ 𝔙.U i) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (coverPrim 𝔙 s i) x₀ :=
  ContMDiffAt.sum (fun q _ => contMDiffAt_primSummand 𝔙 s q i hx₀)

/-- **The telescoping difference identity.** On the overlap `U_i ⊓ U_j`,
`coverPrim s j − coverPrim s i = holoFn(s_{ij})` pointwise. The cocycle relation
(`holoFn_cocycle_sub`) collapses each `q`-bracket to `holoFn(s_{ij})` on `tsupport ρ_q`, and the
weights sum to `1` (`sum_rhoC_apply`). -/
theorem coverPrim_diff (𝔙 : FiniteCover X) (s : ↥(𝔙.cocycles1 (0 : Divisor X))) (i j : 𝔙.ι)
    {x : X} (hx : x ∈ (𝔙.U i ⊓ 𝔙.U j : Opens X)) :
    coverPrim 𝔙 s j x - coverPrim 𝔙 s i x = holoFn (cocycleComp_mem 𝔙 s i j) x := by
  rw [coverPrim_apply, coverPrim_apply, ← Finset.sum_sub_distrib]
  -- Per-`q`: the bracket is `ρ_q x · holoFn(s_{ij}) x` (cocycle relation on `tsupport`, else `ρ_q=0`).
  have hpt : ∀ q : 𝔙.ι,
      rhoC 𝔙 q x * holoFn (cocycleComp_mem 𝔙 s q j) x
        - rhoC 𝔙 q x * holoFn (cocycleComp_mem 𝔙 s q i) x
      = rhoC 𝔙 q x * holoFn (cocycleComp_mem 𝔙 s i j) x := by
    intro q
    by_cases hb : x ∈ tsupport (coverPoU 𝔙 q)
    · have hxq : x ∈ 𝔙.U q := coverPoU_subordinate 𝔙 q hb
      have hxtri : x ∈ (𝔙.U q ⊓ 𝔙.U i ⊓ 𝔙.U j : Opens X) := ⟨⟨hxq, hx.1⟩, hx.2⟩
      rw [← mul_sub, holoFn_cocycle_sub 𝔙 s q i j hxtri]
    · rw [rhoC_eq_zero_of_notMem 𝔙 q hb]; ring
  simp_rw [hpt, ← Finset.sum_mul, sum_rhoC_apply 𝔙 x, one_mul]

/-! ## §3 — The shared-chart disk cover and the chart pushforward

A **shared-chart disk cover** is a finite cover all of whose sets `U_i` live inside a single chart
`φ = chartAt ℂ c₀` and whose chart-images `φ '' U_i` lie in a fixed Euclidean ball `ball cc r ⊆ ℂ`.
This is the geometric situation STEP C of the obstruction map runs over: every overlap pulls back
through the SINGLE chart `φ` to opens of the ball, so the planar `∂̄`-engine applies and the chart
dictionary (`analyticAt_chart_change`) gives chart-analyticity in each point's own chart.

(Such a cover exists around any point — shrink the chart cover so every set sits in one chart-disk —
and is the input the `exists_cechModel` finiteness assembly produces a chart-disk Leray model from.) -/

/-- A finite cover all of whose sets live in one chart `φ = chartAt ℂ center`, with chart-images in a
fixed ball.  The geometric hypothesis STEP C of the obstruction map runs over. -/
structure SharedChartCover (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] extends FiniteCover X where
  /-- The common chart center; the shared chart is `chartAt ℂ center`. -/
  center : X
  /-- The chart-coordinate center of the common ball. -/
  ballCenter : ℂ
  /-- The radius of the common ball. -/
  radius : ℝ
  radius_pos : 0 < radius
  /-- Each cover set lies in the shared chart's source. -/
  subset_source : ∀ i, ((U i : Opens X) : Set X) ⊆ (chartAt (H := ℂ) center).source
  /-- Each cover set's chart-image lies in the common ball. -/
  image_subset_ball : ∀ i,
    (chartAt (H := ℂ) center) '' ((U i : Opens X) : Set X) ⊆ Metric.ball ballCenter radius

namespace SharedChartCover

/-- The shared chart `φ = chartAt ℂ center`. -/
noncomputable abbrev φ (𝔇 : SharedChartCover X) : OpenPartialHomeomorph X ℂ :=
  chartAt (H := ℂ) 𝔇.center

/-- The chart-image `Ω_i = φ '' U_i ⊆ ℂ` of a cover set. -/
def Ω (𝔇 : SharedChartCover X) (i : 𝔇.ι) : Set ℂ := 𝔇.φ '' ((𝔇.U i : Opens X) : Set X)

/-- For `x ∈ U_i`, the chart point `φ x` lies in `Ω_i`. -/
theorem mem_Ω (𝔇 : SharedChartCover X) {i : 𝔇.ι} {x : X} (hx : x ∈ 𝔇.U i) : 𝔇.φ x ∈ 𝔇.Ω i :=
  ⟨x, hx, rfl⟩

/-- For `x ∈ U_i`, the chart point `φ x` lies in the ball. -/
theorem mem_ball (𝔇 : SharedChartCover X) {i : 𝔇.ι} {x : X} (hx : x ∈ 𝔇.U i) :
    𝔇.φ x ∈ Metric.ball 𝔇.ballCenter 𝔇.radius :=
  𝔇.image_subset_ball i ⟨x, hx, rfl⟩

/-- For `x ∈ U_i`, `x` lies in the shared chart's source. -/
theorem mem_source (𝔇 : SharedChartCover X) {i : 𝔇.ι} {x : X} (hx : x ∈ 𝔇.U i) :
    x ∈ (chartAt (H := ℂ) 𝔇.center).source :=
  𝔇.subset_source i hx

end SharedChartCover

/-- **Chart pushforward of the primitive is `ContDiffAt`.**  For `x ∈ U_i` (so `x` in the shared
chart's source), the chart-read `coverPrim s i ∘ φ.symm` is `ContDiffAt ℝ ⊤` at `φ x`.  From the
manifold smoothness `contMDiffAt_coverPrim` (on `U_i`) precomposed with the smooth inverse chart
`φ.symm` (model `𝓘(ℝ,ℂ)` is the identity, so `ContMDiffAt ↔ ContDiffAt`). -/
theorem contDiffAt_coverPrim_chart (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) (i : 𝔇.toFiniteCover.ι) {x : X}
    (hx : x ∈ 𝔇.toFiniteCover.U i) :
    ContDiffAt ℝ (⊤ : ℕ∞) (coverPrim 𝔇.toFiniteCover s i ∘ (𝔇.φ).symm) (𝔇.φ x) := by
  set φ := chartAt (H := ℂ) 𝔇.center with hφ
  have hsrc : x ∈ φ.source := 𝔇.subset_source i hx
  have hxtgt : φ x ∈ φ.target := φ.map_source hsrc
  -- `φ.symm` is `ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ)` at `φ x`, with `φ.symm (φ x) = x`.
  have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) φ.symm (φ x) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := 𝔇.center) _ hxtgt).contMDiffAt
      (φ.open_target.mem_nhds hxtgt)
  have hxeq : φ.symm (φ x) = x := φ.left_inv hsrc
  have hprim : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (coverPrim 𝔇.toFiniteCover s i) x :=
    contMDiffAt_coverPrim 𝔇.toFiniteCover s i hx
  have hcomp : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (coverPrim 𝔇.toFiniteCover s i ∘ φ.symm) (φ x) :=
    (hxeq ▸ hprim).comp (φ x) hsymm
  exact contMDiffAt_iff_contDiffAt.1 hcomp

/-- The chart-image `Ω_i = φ '' U_i` is open in `ℂ` (`φ` is an `OpenPartialHomeomorph` and `U_i` is
open `⊆ φ.source`). -/
theorem isOpen_Ω (𝔇 : SharedChartCover X) (i : 𝔇.toFiniteCover.ι) : IsOpen (𝔇.Ω i) :=
  (chartAt (H := ℂ) 𝔇.center).isOpen_image_of_subset_source (𝔇.U i).isOpen (𝔇.subset_source i)

/-! ## §4 — Chart-analyticity of `H_i = η̂_i ∘ φ` and the difference (fallback rung (d), discharge)

Given holomorphic correctors `η̂_i` on the chart-image discs `ball ∩ Ω_i` (the output of the ball
solve `ballSplit_glued`), the ambient functions `H_i := η̂_i ∘ φ` are chart-analytic on `U_i` and their
differences split `holoFn(s_{ij})`.  These two discharges are sorry-free; what remains (isolated as the
predicate `HasBallSplitData`) is producing the ball-wide smooth primitives + glued `∂̄`-datum to feed
`ballSplit_glued`. -/

/-- **Chart-analyticity of `H_i = η̂_i ∘ φ`.**  If `η̂_i` is `DifferentiableOn ℂ` on the open
`ball ∩ Ω_i`, then for `y ∈ U_i` the ambient `H_i := η̂_i ∘ φ` reads `ℂ`-analytically in the chart at
`y` (`η̂_i` is analytic at `φ y ∈ ball ∩ Ω_i`, and `H_i ∘ φ.symm = η̂_i` there; transport to `y`'s own
chart by `analyticAt_chart_change`). -/
theorem analyticAt_compChart_of_differentiableOn (𝔇 : SharedChartCover X) (i : 𝔇.toFiniteCover.ι)
    {ηhat : ℂ → ℂ} (hη : DifferentiableOn ℂ ηhat (Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i))
    {y : X} (hy : y ∈ 𝔇.toFiniteCover.U i) :
    AnalyticAt ℂ ((ηhat ∘ 𝔇.φ) ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) := by
  set φ := chartAt (H := ℂ) 𝔇.center with hφ
  have hsrc : y ∈ φ.source := 𝔇.subset_source i hy
  have hyΩ : φ y ∈ 𝔇.Ω i := 𝔇.mem_Ω hy
  have hyball : φ y ∈ Metric.ball 𝔇.ballCenter 𝔇.radius := 𝔇.mem_ball hy
  have hopen : IsOpen (Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i) :=
    Metric.isOpen_ball.inter (isOpen_Ω 𝔇 i)
  -- `η̂_i` analytic at `φ y` (`DifferentiableOn ℂ` on the open set ⟹ `AnalyticAt`).
  have hηana : AnalyticAt ℂ ηhat (φ y) :=
    (hη.analyticOnNhd hopen) (φ y) ⟨hyball, hyΩ⟩
  -- The composite `H_i ∘ (chartAt y).symm` read in `𝔇`'s chart equals `η̂_i` near `φ y`.
  -- First read it in `𝔇`'s chart: `(η̂_i ∘ φ) ∘ φ.symm = η̂_i` near `φ y` (on `φ.target`).
  have hymain : AnalyticAt ℂ ((ηhat ∘ φ) ∘ φ.symm) (φ y) := by
    refine hηana.congr ?_
    have htgt : φ.target ∈ 𝓝 (φ y) := φ.open_target.mem_nhds (φ.map_source hsrc)
    filter_upwards [htgt] with w hw
    simp only [Function.comp_apply, φ.right_inv hw]
  -- Now transport from `𝔇`'s chart at `y` to `y`'s own chart (`analyticAt_chart_change`).
  -- `(η̂_i ∘ φ) ∘ φ.symm` analytic at `φ y` = `(chartAt 𝔇.center) y`; need it at `(chartAt y) y`.
  exact analyticAt_chart_change hsrc hymain

/-! ## §5 — The glued `∂̄`-datum, the ball solve, and the `HasChartAnalyticCorrectors` discharge

The §2 primitive, chart-read `ĥ_i := coverPrim s i ∘ φ.symm`, is `C^∞` on `Ω_i = φ '' U_i` (not on all
of the ball), and `ĥ_j − ĥ_i = holoFn(s_{ij}) ∘ φ.symm` on overlaps (`coverPrim_diff`).  The genuine
ball solve does NOT need ball-wide `ĥ_i`: it solves `∂̄u = ω̂` for ONE global glued datum `ω̂` on the
ball (`DbarDiskCohomology.dbar_solvable_ball`) and sets `η̂_i := ĥ_i − u` on `Ω_i ∩ ball`; then
`∂̄η̂_i = ∂̄ĥ_i − ω̂ = 0` (so `η̂_i` is holomorphic) and `η̂_j − η̂_i = ĥ_j − ĥ_i` is unchanged.

So the SINGLE remaining analytic obligation is the **global glued `∂̄`-datum** `ω̂ : ℂ → ℂ`: globally
`C^∞`, agreeing with `∂̄ĥ_i` on each `Ω_i ∩ ball`.  Mathematically `ω̂` is the chart-pushforward of the
Bott–Tu double sum `∑_{q,k}(ρ_q·holoFn(s_{qk}))·∂̄ρ_k` — globally `C^∞` because each term carries the
confining factor `∂̄ρ_k` (the 3-case `tsupport` argument of `DolbeaultComparisonInverse.cechTerm`).
This is the documented OBSTRUCTION-3 globalization; it is isolated below as the predicate
`HasGluedDbarDatum` — never a `sorry`.  Everything downstream (the ball solve, holomorphy of `η̂_i`,
chart-analyticity of `H_i := η̂_i ∘ φ`, and the difference identity) is discharged sorry-free here. -/

/-- **`∂̄ = 0 ⇒ holomorphic`, local form (Wirtinger).**  A function `ℝ`-differentiable at `x` with
vanishing Wirtinger `∂̄` is `ℂ`-differentiable at `x`.  Local variant of
`DbarDiskCohomology.differentiableAt_of_dbar_eq_zero` (which assumes global `ContDiff`) — needed
because the chart-read primitive `chartPrim` is only `ContDiffAt` on `Ω_i`, not globally `C^∞`. -/
theorem differentiableAt_of_dbar_eq_zero_local {g : ℂ → ℂ} {x : ℂ}
    (hg : DifferentiableAt ℝ g x) (hdb : DbarDisk.dbar g x = 0) : DifferentiableAt ℂ g x := by
  rw [differentiableAt_complex_iff_differentiableAt_real]
  refine ⟨hg, ?_⟩
  have h2 : (fderiv ℝ g x) 1 + Complex.I * (fderiv ℝ g x) Complex.I = 0 := by
    have := hdb
    rw [DbarDisk.dbar] at this
    field_simp at this
    linear_combination this
  have hD1 : (fderiv ℝ g x) 1 = -(Complex.I * (fderiv ℝ g x) Complex.I) := by linear_combination h2
  rw [hD1, smul_eq_mul, mul_neg, ← mul_assoc, Complex.I_mul_I]; ring

/-- **The chart-read primitive** `ĥ_i := coverPrim s i ∘ φ.symm : ℂ → ℂ` — the §2 cover-set primitive
pushed through the shared chart.  `C^∞` on `Ω_i` (`contDiffAt_coverPrim_chart`); its differences split
`holoFn(s_{ij}) ∘ φ.symm` on overlaps (`coverPrim_diff`). -/
noncomputable def chartPrim (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) (i : 𝔇.toFiniteCover.ι) : ℂ → ℂ :=
  coverPrim 𝔇.toFiniteCover s i ∘ (𝔇.φ).symm

/-- **The chart-read difference is the chart-pushed analytic representative.**  On the overlap image
`φ '' (U_i ⊓ U_j)`, the chart-read primitives differ by `holoFn(s_{ij}) ∘ φ.symm`:
`chartPrim s j (φ x) − chartPrim s i (φ x) = holoFn(s_{ij}) x` for `x ∈ U_i ⊓ U_j`.  Pure
chart-pushforward of `coverPrim_diff` (the `u`-free precursor of the §5 difference identity).  This
witnesses that the glued-datum predicate `HasGluedDbarDatum` is non-degenerate: the `∂̄ĥ_i` are forced
to agree on overlaps (their differences `∂̄(holoFn(s_{ij}) ∘ φ.symm)` vanish — the chart-read of a
holomorphic function), so a common datum `ω̂` is the genuine Forster glued `∂̄`-datum, not a vacuous
hypothesis. -/
theorem chartPrim_diff (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) (i j : 𝔇.toFiniteCover.ι) {x : X}
    (hx : x ∈ (𝔇.toFiniteCover.U i ⊓ 𝔇.toFiniteCover.U j : Opens X)) :
    chartPrim 𝔇 s j (𝔇.φ x) - chartPrim 𝔇 s i (𝔇.φ x)
      = holoFn (cocycleComp_mem 𝔇.toFiniteCover s i j) x := by
  have hsrc : x ∈ (chartAt (H := ℂ) 𝔇.center).source := 𝔇.subset_source i hx.1
  simp only [chartPrim, Function.comp_apply, (𝔇.φ).left_inv hsrc]
  exact coverPrim_diff 𝔇.toFiniteCover s i j hx

/-- **The remaining analytic obligation: the global glued `∂̄`-datum.**  For every cocycle `s` there is
a globally-`C^∞` function `ω̂ : ℂ → ℂ` agreeing with `∂̄(ĥ_i) = ∂̄(coverPrim s i ∘ φ.symm)` on each
`Ω_i ∩ ball`.  This is the chart-pushforward of the Bott–Tu double-sum datum
`∑_{q,k}(ρ_q·holoFn(s_{qk}))·∂̄ρ_k` (the documented OBSTRUCTION-3 PoU globalization, globally `C^∞` via
`cechTerm`'s 3-case `tsupport` argument).  Isolated as a predicate so the discharge below is
sorry-free; the precise remaining gap. -/
def HasGluedDbarDatum (𝔇 : SharedChartCover X) : Prop :=
  ∀ s : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)),
    ∃ dbarDatum : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) dbarDatum ∧
      ∀ i, ∀ z ∈ Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i,
        DbarDisk.dbar (chartPrim 𝔇 s i) z = dbarDatum z

/-- **`HasChartAnalyticCorrectors` from the glued `∂̄`-datum (sorry-free).**  Given the global glued
datum `ω̂`, solve `∂̄u = ω̂` on the ball (`dbar_solvable_ball`) and set `η̂_i := ĥ_i − u` on `Ω_i ∩ ball`:
`η̂_i` is holomorphic there (`∂̄η̂_i = ∂̄ĥ_i − ω̂ = 0`, `differentiableAt_of_dbar_eq_zero`), so
`H_i := η̂_i ∘ φ` is chart-analytic on `U_i` (`analyticAt_compChart_of_differentiableOn`), and the
differences split `holoFn(s_{ij})` on each overlap (`η̂_j − η̂_i = ĥ_j − ĥ_i`, then `coverPrim_diff`).
This is STEP C.4 + the §4 discharges, all sorry-free here. -/
theorem hasChartAnalyticCorrectors_of_hasGluedDbarDatum (𝔇 : SharedChartCover X)
    (H : HasGluedDbarDatum 𝔇) : HasChartAnalyticCorrectors 𝔇.toFiniteCover := by
  intro s
  obtain ⟨dbarDatum, hdatum, hagree⟩ := H s
  -- Solve `∂̄u = ω̂` on the ball.
  obtain ⟨u, hu_smooth, hu_dbar⟩ :=
    DbarDiskCohomology.dbar_solvable_ball hdatum 𝔇.ballCenter 𝔇.radius_pos
  -- The holomorphic chart correctors `η̂_i := ĥ_i − u` on `Ω_i ∩ ball`.
  set ηhat : 𝔇.toFiniteCover.ι → ℂ → ℂ := fun i => chartPrim 𝔇 s i - u with hηhatdef
  -- `η̂_i` is holomorphic on `ball ∩ Ω_i` (`∂̄η̂_i = ∂̄ĥ_i − ∂̄u = ω̂ − ω̂ = 0`).
  have hηhol : ∀ i, DifferentiableOn ℂ (ηhat i)
      (Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i) := by
    intro i z hz
    -- `ĥ_i` is `C^∞` at `z ∈ Ω_i`: `z = φ x` for some `x ∈ U_i`, then `contDiffAt_coverPrim_chart`.
    obtain ⟨x, hxU, hxz⟩ := hz.2
    have hĥ_cd : ContDiffAt ℝ (⊤ : ℕ∞) (chartPrim 𝔇 s i) z := by
      rw [← hxz]; exact contDiffAt_coverPrim_chart 𝔇 s i hxU
    -- `∂̄η̂_i z = ∂̄ĥ_i z − ∂̄u z = ω̂ z − ω̂ z = 0`.
    have hdb_eta : DbarDisk.dbar (ηhat i) z = 0 := by
      have hsub : DbarDisk.dbar (fun w => chartPrim 𝔇 s i w - u w) z
          = DbarDisk.dbar (chartPrim 𝔇 s i) z - DbarDisk.dbar u z :=
        dbarFun_sub (hĥ_cd.differentiableAt (by norm_num))
          (hu_smooth.differentiable (by norm_num) z)
      rw [hηhatdef]
      show DbarDisk.dbar (fun w => chartPrim 𝔇 s i w - u w) z = 0
      rw [hsub, hu_dbar z hz.1, hagree i z hz]; ring
    -- `∂̄η̂_i = 0` + `η̂_i` `ℝ`-differentiable ⟹ `ℂ`-differentiable (Wirtinger), on the open set.
    have hηcd : DifferentiableAt ℝ (ηhat i) z := by
      rw [hηhatdef]
      exact (hĥ_cd.differentiableAt (by norm_num)).sub (hu_smooth.differentiable (by norm_num) z)
    exact (differentiableAt_of_dbar_eq_zero_local hηcd hdb_eta).differentiableWithinAt
  -- The ambient correctors `H_i := η̂_i ∘ φ`.
  refine ⟨fun i => ηhat i ∘ 𝔇.φ, fun i y hy => ?_, fun i j x hx => ?_⟩
  · -- Chart-analytic on `U_i`.
    exact analyticAt_compChart_of_differentiableOn 𝔇 i (hηhol i) hy
  · -- Difference identity, pointwise on the open overlap (gives the `𝓝[≠]`-eventual form).
    have hUij : ∀ᶠ z in 𝓝[≠] x, z ∈ (𝔇.toFiniteCover.U i ⊓ 𝔇.toFiniteCover.U j : Opens X) :=
      eventually_nhdsWithin_of_eventually_nhds
        ((𝔇.toFiniteCover.U i ⊓ 𝔇.toFiniteCover.U j : Opens X).isOpen.mem_nhds hx)
    filter_upwards [hUij] with z hz
    -- `(η̂_j ∘ φ) z − (η̂_i ∘ φ) z = (ĥ_j − ĥ_i)(φ z) = (coverPrim j − coverPrim i) z = holoFn(s_{ij}) z`.
    show (ηhat j ∘ 𝔇.φ) z - (ηhat i ∘ 𝔇.φ) z = holoFn (cocycleComp_mem 𝔇.toFiniteCover s i j) z
    have hzsrc : z ∈ (chartAt (H := ℂ) 𝔇.center).source := 𝔇.subset_source i hz.1
    have hsymm_eq : (𝔇.φ).symm (𝔇.φ z) = z := (𝔇.φ).left_inv hzsrc
    simp only [hηhatdef, Function.comp_apply, Pi.sub_apply, chartPrim, hsymm_eq]
    -- The `u`-terms cancel; the rest is `coverPrim_diff`.
    have hcd := coverPrim_diff 𝔇.toFiniteCover s i j hz
    linear_combination hcd

/-- **`H¹(disk, 𝒪) = 0` for a shared-chart disk cover, from the glued `∂̄`-datum (sorry-free).**  The
end-to-end germ-level collapse modulo the single remaining globalization obligation
`HasGluedDbarDatum`: the §0–§5 discharge produces `HasChartAnalyticCorrectors`, and the imported
`cechH1_subsingleton_of_chartAnalyticCorrectors` collapses every class of `cechH1 0`. -/
theorem cechH1_subsingleton_of_hasGluedDbarDatum (𝔇 : SharedChartCover X)
    (H : HasGluedDbarDatum 𝔇) (q : 𝔇.toFiniteCover.cechH1 (0 : Divisor X)) : q = 0 :=
  cechH1_subsingleton_of_chartAnalyticCorrectors 𝔇.toFiniteCover
    (hasChartAnalyticCorrectors_of_hasGluedDbarDatum 𝔇 H) q

end Jacobians.Dolbeault

/-! ## Status and the EXACT remaining goal

WHAT IS DELIVERED HERE (all sorry-free; axiom-clean `[propext, Classical.choice, Quot.sound]`):

  * **§0 — Ported PoU machinery (fallback rung (a)):** `ofRealCM`, `coverPoU` / `coverPoU_subordinate`
    (the subordinate smooth partition of unity over a generic `FiniteCover`), `rhoC` / `sum_rhoC` /
    `sum_rhoC_apply` / `rhoC_eq_zero_of_notMem`, the real-smooth bridge
    `contMDiffAt_real_of_chart_analyticAt`, and the ring instance `contMDiffMul_real_complex` — all
    ported (proofs copied) from `DolbeaultComparisonInverse`, which is UN-IMPORTABLE here (it
    re-derives, under the same names, the `holoRep`/`holoFn`/… toolkit that the imported
    `CechDiskAcyclicProof` also derives — eight name clashes in `Jacobians.Dolbeault`).  The lighter
    `DolbeaultComparison` is imported (clash-free).  Plus the `holoFn` algebra ports `Gext_sub` /
    `holoFn_tendsto` / `holoFn_sub` / `holoFn_congr` / `holoFn_restrict` and the cocycle-value relation
    `holoFn_cocycle_sub` (`s_{qj} − s_{qi} = s_{ij}` on triple overlaps, from `δ¹s = 0`).

  * **§1 — Per-summand overlap smoothness (fallback rung (b)):** `contMDiffAt_primSummand` — the
    summand `ρ_q · holoFn(s_{qi})` is `ContMDiffAt 𝓘(ℝ,ℂ)` at every point of `U_i`, by the two-case
    `tsupport`/overlap argument (on `tsupport ρ_q ⊆ U_q` the point lies in `U_q ⊓ U_i`, off it `ρ_q`
    vanishes).  This is the honest function-level content of `DolbeaultComparisonInverse.cechTerm` /
    `primFn` (the load-bearing piece the task flagged).  NOTE — the genuine reason `h_i` is confined to
    `U_i`: at a point of `U_q ∖ U_i` with `ρ_q ≠ 0` the holomorphic factor is junk, so the summand is
    NOT globally `C^∞` on `X`.  The construction (and Forster) therefore work on `U_i`, never on all of
    `X`/the ball.

  * **§2 — The cover-set primitive (fallback rung (c), manifold side):** `coverPrim 𝔙 s i =
    ∑_q ρ_q · holoFn(s_{qi})`, `ContMDiffAt` on `U_i` (`contMDiffAt_coverPrim`), with the TELESCOPING
    DIFFERENCE IDENTITY `coverPrim_diff`: `coverPrim s j − coverPrim s i = holoFn(s_{ij})` on `U_i ⊓ U_j`
    (the cocycle relation `holoFn_cocycle_sub` collapses each `q`-bracket, `∑ρ = 1` finishes).

  * **§3 — The shared-chart disk cover + chart pushforward:** `SharedChartCover` (a `FiniteCover` all of
    whose sets sit in one chart `φ = chartAt ℂ center` with chart-images in a fixed ball — the geometric
    situation STEP C runs over), `Ω`/`isOpen_Ω`, and `contDiffAt_coverPrim_chart` (the chart-read
    `coverPrim s i ∘ φ.symm` is `ContDiffAt ℝ ⊤` on `Ω_i`).

  * **§4 — Chart-analyticity of `H_i = η̂_i ∘ φ`:** `analyticAt_compChart_of_differentiableOn` — a
    holomorphic chart corrector `η̂_i` on `ball ∩ Ω_i` gives `H_i := η̂_i ∘ φ` chart-analytic on `U_i`
    (`η̂_i` analytic at `φ y`, `H_i ∘ φ.symm = η̂_i` there, then `analyticAt_chart_change` to `y`'s own
    chart).

  * **§5 — The glued `∂̄`-datum reduction (fallback rung (d), discharge):** the SORRY-FREE chain
    `HasGluedDbarDatum ⟹ HasChartAnalyticCorrectors ⟹ (H¹(disk, 𝒪) = 0)`:
    - `differentiableAt_of_dbar_eq_zero_local` (local Wirtinger, since `chartPrim` is only `ContDiffAt`);
    - `chartPrim` (the chart-read primitive) + `chartPrim_diff` (its overlap difference is the
      chart-pushed `holoFn(s_{ij})`, witnessing `HasGluedDbarDatum` is non-degenerate);
    - `hasChartAnalyticCorrectors_of_hasGluedDbarDatum`: solve `∂̄u = ω̂` on the ball
      (`DbarDiskCohomology.dbar_solvable_ball`), set `η̂_i := chartPrim s i − u` (holomorphic on
      `ball ∩ Ω_i` by the local Wirtinger lemma), `H_i := η̂_i ∘ φ` (chart-analytic by §4), differences
      split `holoFn(s_{ij})` by `coverPrim_diff`;
    - `cechH1_subsingleton_of_hasGluedDbarDatum`: the end-to-end germ-level collapse via the imported
      `cechH1_subsingleton_of_chartAnalyticCorrectors`.

IMPORT FINDING (corrects/confirms the task premise).  Importing `CechDiskAcyclicAssembly` +
`CechDiskAcyclicProof` (transitive) together with `DolbeaultComparison` + `DbarDiskCohomology` +
`ChartDiskCover` compiles cleanly — NO `NormedAddCommGroup (ℂ →L[ℝ] ℂ)` diamond and NO name clash (the
clash is ONLY against `DolbeaultComparisonInverse`, which is correctly avoided by porting).

THE EXACT REMAINING GOAL — `HasGluedDbarDatum 𝔇`: produce, for each cocycle `s`, a single
globally-`C^∞` function `ω̂ : ℂ → ℂ` agreeing with `∂̄(coverPrim s i ∘ φ.symm)` on each `Ω_i ∩ ball`.
This is the chart-pushforward of the Bott–Tu **double-sum** glued `∂̄`-datum
`∑_{q,k}(ρ_q · holoFn(s_{qk})) · ∂̄ρ_k` — globally `C^∞` because each term carries the CONFINING factor
`∂̄ρ_k` (supported in `U_k`), so the documented 3-case `tsupport` argument of
`DolbeaultComparisonInverse.cechTerm` makes the whole double sum globally smooth and `i`-independent.
(`chartPrim_diff` shows the per-`i` data are consistent: the `∂̄ĥ_i` are forced to agree on overlaps.)
This is the single OBSTRUCTION-3 PoU globalization that "reduced-but-didn't-close" twice; it is the only
remaining gap, written as the predicate `HasGluedDbarDatum`, NEVER a `sorry`.  Producing `ω̂` requires
PORTING the double-sum `cechTerm` analytic content into the chart-function setting (the documented
~400-LoC step), and — combined with the §0–§5 chain above — discharges `HasGluedDbarDatum`, hence
`HasChartAnalyticCorrectors`, hence germ-level `H¹(disk, 𝒪) = 0`, for a shared-chart disk cover.
-/
