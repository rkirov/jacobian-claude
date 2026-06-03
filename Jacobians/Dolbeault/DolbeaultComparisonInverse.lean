/-
  Dolbeault's comparison theorem — **inverse direction** (`Čech → Dolbeault`), the CONSTRUCTION.

  This file builds the inverse map `cech_to_dolbeault : H¹(X, 𝒪) → H^{0,1}(X)` from the
  partition-of-unity backbone, the `∂̄ρ_k` gluing data, the ℂ-scaling toolkit, and the glued-form
  operator `cechToDolbeaultForm` (Bott–Tu double-sum). It deliberately imports only the *light*
  dependencies (`DolbeaultComparison`, `CechH0`, `ChartDiskCover`, partitions of unity) and NOT the
  heavy forward file `DolbeaultComparisonProof` — the construction uses no forward symbol, so keeping
  this file off that import makes it fast to elaborate. The final assembly into the `ℝ`-linear
  equivalence (which needs the forward map `dolbeault_to_cech`) lives in `DolbeaultComparisonEquiv`.
-/
import Jacobians.Dolbeault.DolbeaultComparison
import Jacobians.Dolbeault.CechH0
import Jacobians.Dolbeault.ChartDiskCover
import Jacobians.MeromorphicNFRepair
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.BumpFunction

open scoped Manifold ContDiff Bundle Topology
open TopologicalSpace (Opens)
open Filter

-- Same permissive transparency as `RealForms` (the section hom-bundle instances, and any
-- `Finset.sum` / ℂ-scaling over `SmoothCOneForms`, need it).
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable (𝔘 : FiniteCover X)


/-! ### Sorry-free backbone of the Čech → Dolbeault map: the partition of unity

The Čech → Dolbeault globalization needs a smooth partition of unity `{ρ_i}` subordinate to the
cover. We provide it **sorry-free** from Mathlib (`SmoothPartitionOfUnity.exists_isSubordinate`,
available because a compact `T2` `ℂ`-manifold is a `σ`-compact finite-dimensional real manifold via
`RealManifold`). This `ρ` is the actual analytic input `h_i := ∑_k ρ_k · f_ik` is built from. -/

/-- **(Čech → Dolbeault backbone, sorry-free.)** The partition-of-unity *telescoping identity* — the
algebraic heart of the Čech → Dolbeault coboundary construction. For any additive Čech `1`-cocycle
`f` (`f_jk − f_ik + f_ij = 0`, the `cechDelta1 = 0` relation) and any weights `ρ` summing to `1`, the
globalized functions `h_i := ∑_k ρ_k • f_ki` satisfy `h_j − h_i = f_ij` — i.e. the cocycle becomes a
coboundary of the smooth (partition-of-unity-glued) `0`-cochain. Pure module algebra (it is what
"`∂̄h_i` glue to a global form" rests on); proven here abstractly over any `ℂ`-module. -/
theorem cechCoboundary_telescoping {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M] [Module ℂ M]
    (f : ι → ι → M) (hcoc : ∀ a b c, f b c - f a c + f a b = 0)
    (ρ : ι → ℂ) (hρ : ∑ k, ρ k = 1) (i j : ι) :
    (∑ k, ρ k • f k j) - (∑ k, ρ k • f k i) = f i j := by
  rw [← Finset.sum_sub_distrib]
  have hpt : ∀ k, ρ k • f k j - ρ k • f k i = ρ k • f i j := fun k => by
    rw [← smul_sub]; congr 1; linear_combination (norm := module) -hcoc k i j
  simp_rw [hpt, ← Finset.sum_smul, hρ, one_smul]

/-- **(Čech → Dolbeault backbone, sorry-free.)** A smooth partition of unity subordinate to the
finite cover `𝔘`, over the real-manifold structure `𝓘(ℝ, ℂ)`. The input for the globalization
`h_i := ∑_k ρ_k · f_ik`. -/
theorem exists_smoothPartitionOfUnity_subordinate :
    ∃ ρ : SmoothPartitionOfUnity 𝔘.ι 𝓘(ℝ, ℂ) X (Set.univ : Set X),
      ρ.IsSubordinate (fun i => (𝔘.U i : Set X)) := by
  have hcov : (Set.univ : Set X) ⊆ ⋃ i, (𝔘.U i : Set X) := by
    rw [Set.univ_subset_iff, ← TopologicalSpace.Opens.coe_iSup, 𝔘.covers]; rfl
  exact SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ
    (fun i => (𝔘.U i : Set X)) (fun i => (𝔘.U i).isOpen) hcov

/-- **(Inverse, phase 2.)** A holomorphic function representative of an `OmegaDGerm 0`-class: since
`OmegaDGerm 0 U = map toGerm (OmegaD 0 U)` and `OmegaD 0 = ` holomorphic functions, the class has a
holomorphic representative (chosen). The unique-up-to-nothing holomorphic lift the PoU globalization
multiplies by `ρ_k`. -/
noncomputable def holoRep {U : TopologicalSpace.Opens X} {g : MGerm U}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) U) : U → ℂ :=
  (Submodule.mem_map.mp hg).choose

theorem holoRep_mem {U : TopologicalSpace.Opens X} {g : MGerm U}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) U) : holoRep hg ∈ OmegaD (0 : Divisor X) U :=
  (Submodule.mem_map.mp hg).choose_spec.1

theorem toGerm_holoRep {U : TopologicalSpace.Opens X} {g : MGerm U}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) U) : toGerm U (holoRep hg) = g :=
  (Submodule.mem_map.mp hg).choose_spec.2

/-! ### Inverse, phase 3 — the partition of unity and the `∂̄ρ_k` forms (gluing route, Forster §15) -/

/-- `ℝ → ℂ` as a smooth map, for coercing the real-valued PoU functions to `SmoothCFunctions`. -/
noncomputable def ofRealCM : ContMDiffMap (𝓘(ℝ)) (𝓘(ℝ, ℂ)) ℝ ℂ (⊤ : ℕ∞) :=
  ⟨Complex.ofReal, Complex.ofRealCLM.contMDiff⟩

/-- A fixed smooth partition of unity subordinate to the cover (`exists_smoothPartitionOfUnity_
subordinate`) — the globalization input for the inverse map. -/
noncomputable def cechPoU (𝔇 : ChartDiskCover X) :
    SmoothPartitionOfUnity 𝔇.toFiniteCover.ι 𝓘(ℝ, ℂ) X (Set.univ : Set X) :=
  (exists_smoothPartitionOfUnity_subordinate 𝔇.toFiniteCover).choose

theorem cechPoU_subordinate (𝔇 : ChartDiskCover X) :
    (cechPoU 𝔇).IsSubordinate (fun i => (𝔇.U i : Set X)) :=
  (exists_smoothPartitionOfUnity_subordinate 𝔇.toFiniteCover).choose_spec

/-- The `k`-th PoU function as a complex `SmoothCFunctions` (`ρ̃_k = ofReal ∘ ρ_k`). -/
noncomputable def rhoC (𝔇 : ChartDiskCover X) (k : 𝔇.toFiniteCover.ι) : SmoothCFunctions X :=
  ofRealCM.comp (cechPoU 𝔇 k)

/-- `∂̄ρ_k` as a global `(0,1)`-form. -/
noncomputable def dbarRho (𝔇 : ChartDiskCover X) (k : 𝔇.toFiniteCover.ι) : SmoothCOneForms X :=
  dbarL (rhoC 𝔇 k)

/-- The PoU functions sum to the constant `1` (finite cover ⇒ plain `Finset.sum`). -/
theorem sum_rhoC (𝔇 : ChartDiskCover X) : ∑ k, rhoC 𝔇 k = 1 := by
  refine ContMDiffMap.ext fun x => ?_
  have h1 : (⇑(∑ k, rhoC 𝔇 k) : X → ℂ) = ∑ k, ⇑(rhoC 𝔇 k) :=
    map_sum ContMDiffMap.coeFnAddMonoidHom _ _
  rw [show (∑ k, rhoC 𝔇 k) x = (⇑(∑ k, rhoC 𝔇 k) : X → ℂ) x from rfl, h1, Finset.sum_apply,
    ContMDiffMap.coe_one, Pi.one_apply]
  show ∑ k, ((cechPoU 𝔇 k x : ℝ) : ℂ) = 1
  rw [← Complex.ofReal_sum, ← finsum_eq_sum_of_fintype,
    (cechPoU 𝔇).sum_eq_one (Set.mem_univ x), Complex.ofReal_one]

/-- **The gluing relation** `∑_k ∂̄ρ_k = 0` (`∂̄` of `∑ρ_k = 1` is `∂̄1 = 0`). This is what makes the
local `∂̄η_i` agree on overlaps. -/
theorem dbarL_one_eq_zero : dbarL (1 : SmoothCFunctions X) = 0 := by
  rw [dbarL_eq_proj01L_differential]
  have hd : differential (1 : SmoothCFunctions X) = 0 := by
    refine ContMDiffSection.ext fun x => ?_
    show mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun _ : X => (1 : ℂ)) x = 0
    exact mfderiv_const
  rw [hd]; exact proj01L.map_zero

/-- **The gluing relation** `∑_k ∂̄ρ_k = 0` — `∂̄` of `∑_k ρ_k = 1` is `∂̄1 = 0`. This is what makes
the local primitives `∂̄η_i` agree on overlaps (so they glue to a global `(0,1)`-form). The summand
forms are `dbarRho 𝔇 k = dbarL (rhoC 𝔇 k)`; `dbarL` is `ℝ`-linear, so the sum commutes through it
(`map_sum`) onto `∑_k ρ_k = 1` (`sum_rhoC`).

Historical note: summing `SmoothCOneForms` (`Finset.sum`) was once thought to be blocked by the
`Module ℝ` section-instance diamond (`reference_module_real_diamond`). It is not: with the file-level
`set_option backward.isDefEq.respectTransparency false` already in force (for the hom-bundle section
instances), `AddCommMonoid (SmoothCOneForms X)` synthesises and the form-sum elaborates normally. -/
theorem sum_dbarRho_eq_zero (𝔇 : ChartDiskCover X) :
    ∑ k, dbarRho 𝔇 k = 0 := by
  have h : ∑ k, dbarRho 𝔇 k = dbarL (∑ k, rhoC 𝔇 k) := (map_sum dbarL _ _).symm
  rw [h, sum_rhoC, dbarL_one_eq_zero]

/-! ### ℂ-valued function scaling of `(0,1)`-forms (the double-sum term builder)

Each Bott–Tu double-sum term is `(ρ_j·F_jk) • ∂̄ρ_k` — a `(0,1)`-form `∂̄ρ_k` scaled by a ℂ-valued
smooth function. The base manifold model `𝓘(ℝ,ℂ)` is an `ℝ`-model, so Mathlib's `smul_section` only
covers `ℝ`-scaling; ℂ-scaling is recovered by writing `z • β = (mul ℝ ℂ z).comp β` (post-compose
mult-by-`z`) and using `clm_comp`. The result stays `(0,1)` because `proj01` commutes with the
ℂ-scale (`proj01_smul`). -/

/-- **(`ContMDiffAt` form, the workhorse.)** Scaling a smooth `(0,1)`-valued section by a ℂ-valued
function, fiberwise, is smooth at `x₀` when both are. The ℂ-smul is post-composition on the trivial
codomain (`z • β = (mul ℝ ℂ z).comp β`), so it slides through the tangent `symmL`, reducing to
`clm_comp` of the smooth `x ↦ mul ℝ ℂ (F x)` and the smooth in-coordinates of `s`. -/
theorem contMDiffAt_cSmul_section {F : X → ℂ}
    {s : ∀ x : X, TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x} {x₀ : X}
    (hF : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) F x₀)
    (hs : ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) (⊤ : ℕ∞)
      (fun x => (⟨x, s x⟩ : Bundle.TotalSpace (ℂ →L[ℝ] ℂ)
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x))) x₀) :
    ContMDiffAt 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) (⊤ : ℕ∞)
      (fun x => (⟨x, (F x) • (s x)⟩ : Bundle.TotalSpace (ℂ →L[ℝ] ℂ)
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x))) x₀ := by
  rw [contMDiffAt_hom_bundle] at hs ⊢
  refine ⟨contMDiffAt_id, ?_⟩
  simp only [ContinuousLinearMap.inCoordinates,
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    Bundle.Trivial.fiberBundle_trivializationAt', ContinuousLinearMap.id_comp] at hs ⊢
  have hM : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ) (⊤ : ℕ∞)
      (fun x => ContinuousLinearMap.mul ℝ ℂ (F x)) x₀ :=
    ContMDiffAt.clm_apply contMDiffAt_const hF
  refine (hM.clm_comp hs.2).congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => ?_)
  refine ContinuousLinearMap.ext fun v => ?_
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Global form of `contMDiffAt_cSmul_section` for a `SmoothCFunctions` scalar and a smooth form. -/
theorem contMDiff_cSmul_section (c : SmoothCFunctions X) (g : SmoothCOneForms X) :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) (⊤ : ℕ∞)
      (fun x => (⟨x, (c x) • (g x)⟩ : Bundle.TotalSpace (ℂ →L[ℝ] ℂ)
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x))) :=
  fun x₀ => contMDiffAt_cSmul_section (c.contMDiff x₀) (g.contMDiff_toFun x₀)

/-- **Chart-analytic ⟹ real-smooth.** If a `ℂ`-valued function `h` read in the chart at `y` is
complex-analytic at the chart image, then `h` is real-`C^∞` (`ContMDiffAt 𝓘(ℝ,ℂ)`) at `y`. (The
`(0,1)`-form term needs this for the holomorphic representatives `F_jk = Gext(holoRep)`.) -/
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

/-- **The analytic representative.** For a holomorphic (`OmegaD 0`) function `g` on `↥V`, its
**limit-repair** `x ↦ limUnder (𝓝[≠] x) (Gext g)` is chart-analytic at every `y ∈ V` (it discards the
removable-singularity junk of `Gext g`, agreeing with the normal-form representative
`toMeromorphicNFOn` of the chart-read). Adapts `MeromorphicLiouville.exists_holoRepr_eq_NFOn` to
`Gext g`. With `contMDiffAt_real_of_chart_analyticAt` this gives a real-smooth `F_jk`. -/
theorem gextLimRep_chart_analyticAt {V : Opens X} {g : V → ℂ} (hg : g ∈ OmegaD 0 V)
    {y : X} (hy : y ∈ V) :
    AnalyticAt ℂ ((fun x => limUnder (𝓝[≠] x) (Gext g)) ∘ (chartAt (H := ℂ) y).symm)
      ((chartAt (H := ℂ) y) y) := by
  set φ := chartAt (H := ℂ) y with hφ
  set F := Gext g ∘ φ.symm with hFdef
  have hmero₀ : MeromorphicAt F (φ y) := Gext_meromorphicAt hg.1 hy
  obtain ⟨V₀, hV₀open, hzV₀, hFV₀, hana₀⟩ :=
    Jacobians.MeromorphicAt.exists_isOpen_meromorphicOn hmero₀
  set W := V₀ ∩ φ.target with hWdef
  have hWopen : IsOpen W := hV₀open.inter φ.open_target
  have hzW : φ y ∈ W := ⟨hzV₀, φ.map_source (mem_chart_source ℂ y)⟩
  have hFW : MeromorphicOn F W := fun w hw => hFV₀ w hw.1
  have hana : ∀ w ∈ W, w ≠ φ y → AnalyticAt ℂ F w := fun w hw hwz => hana₀ w hw.1 hwz
  have hWtarget : W ⊆ φ.target := fun _ hw => hw.2
  have hord : ∀ w ∈ W, 0 ≤ meromorphicOrderAt F w := by
    intro w hw
    by_cases hwz : w = φ y
    · subst hwz
      have hord0 := (mem_OmegaD.1 hg).2 ⟨y, hy⟩
      rw [ordU_eq_orderAt_Gext g hy] at hord0
      simpa using hord0
    · exact (hana w hw hwz).meromorphicOrderAt_nonneg
  refine (analyticAt_toMeromorphicNFOn hFW hord hzW).congr ?_
  filter_upwards [hWopen.mem_nhds hzW] with w hw
  show toMeromorphicNFOn F W w = limUnder (𝓝[≠] (φ.symm w)) (Gext g)
  obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg (hFW w hw) (hord w hw)
  have hNFOn : toMeromorphicNFOn F W w = c := by
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hFW hw]
    exact toMeromorphicNFAt_self_eq_limUnder (hFW w hw) (hord w hw) hc
  rw [hNFOn]
  have hys : φ.symm w ∈ φ.source := φ.map_target (hWtarget hw)
  have htsymm : Tendsto φ.symm (𝓝[≠] w) (𝓝[≠] (φ.symm w)) := by
    have := φ.symm.tendsto_nhdsNE (x := w) (by simpa using hWtarget hw)
    simpa using this
  haveI hNeBot : (𝓝[≠] (φ.symm w)).NeBot := htsymm.neBot
  symm
  apply Filter.Tendsto.limUnder_eq
  have hfwd : Tendsto φ (𝓝[≠] (φ.symm w)) (𝓝[≠] (φ (φ.symm w))) := φ.tendsto_nhdsNE hys
  have hwr : φ (φ.symm w) = w := φ.right_inv (hWtarget hw)
  have hcomp : Tendsto (F ∘ φ) (𝓝[≠] (φ.symm w)) (𝓝 c) := by
    rw [← hwr] at hc; exact hc.comp hfwd
  refine hcomp.congr' ?_
  filter_upwards [mem_nhdsWithin_of_mem_nhds (φ.open_source.mem_nhds hys)] with z hz
  simp [hFdef, Function.comp, φ.left_inv hz]

/-- The `(0,1)`-projection commutes with ℂ-scaling of the codomain: `proj01 (z • α) = z • proj01 α`
(`z` factors out of the Wirtinger average). -/
theorem proj01_smul (z : ℂ) (α : ℂ →L[ℝ] ℂ) : proj01 (z • α) = z • proj01 α := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [proj01_apply, proj01_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, mulI, ContinuousLinearMap.mul_apply',
    ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.real_smul]
  push_cast
  ring

/-- **ℂ-valued smooth-function scaling of a `(0,1)`-valued smooth form** (the double-sum term builder):
`(c • g) x = c x • g x`, a smooth `(0,1)`-valued form. -/
noncomputable def cSmulForm (c : SmoothCFunctions X) (g : SmoothCOneForms X) : SmoothCOneForms X where
  toFun := fun x => (c x) • (g x)
  contMDiff_toFun := contMDiff_cSmul_section c g

@[simp] theorem cSmulForm_apply (c : SmoothCFunctions X) (g : SmoothCOneForms X) (x : X) :
    cSmulForm c g x = (c x) • (g x) := rfl

/-- ℂ-scaling preserves the `(0,1)`-forms: `c • g ∈ A^{0,1}` whenever `g ∈ A^{0,1}`. (Witness
`c • h` where `g = proj01L h`; `proj01` commutes with the ℂ-scale, `proj01_smul`.) -/
theorem cSmulForm_mem_zeroOne (c : SmoothCFunctions X) {g : SmoothCOneForms X}
    (hg : g ∈ OneFormsZeroOne X) : cSmulForm c g ∈ OneFormsZeroOne X := by
  obtain ⟨h, rfl⟩ := hg
  refine ⟨cSmulForm c h, ?_⟩
  refine ContMDiffSection.ext fun x => ?_
  simp only [proj01L_apply, proj01Section_apply, cSmulForm_apply]
  exact proj01_smul (c x) (h x)

/-! ### Support of the gluing forms `∂̄ρ_k`

Each double-sum term `ρ_j·F_jk·∂̄ρ_k` is globally smooth because `∂̄ρ_k` is supported in `U_k`
(and `ρ_j` in `U_j`), confining the product to the overlap `U_j ∩ U_k` where `F_jk` lives. -/

/-- `∂̄` shrinks support: `∂̄u x = 0` wherever `u` is locally constant (`x ∉ tsupport u`). (Stated
pointwise — section coes are dependently typed, so `tsupport` of a section is not available.) -/
theorem dbarL_eq_zero_of_notMem_tsupport (u : SmoothCFunctions X) {x : X}
    (hx : x ∉ tsupport (⇑u : X → ℂ)) : (dbarL u) x = 0 := by
  have h0 : (⇑u : X → ℂ) =ᶠ[nhds x] 0 := by
    filter_upwards [(isClosed_tsupport (⇑u : X → ℂ)).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  rw [dbarL_apply]
  show proj01 ((differential u).toFun x) = 0
  have hmf : (differential u).toFun x = 0 := by
    show mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x = 0
    rw [h0.mfderiv_eq]; exact mfderiv_const
  rw [hmf, map_zero]

/-- `∂̄ρ_k x = 0` for `x ∉ tsupport ρ_k` — so `∂̄ρ_k` is supported in `U_k` (`ρ_k` subordinate). -/
theorem dbarRho_eq_zero_of_notMem (𝔇 : ChartDiskCover X) (k : 𝔇.toFiniteCover.ι) {x : X}
    (hx : x ∉ tsupport (cechPoU 𝔇 k)) : (dbarRho 𝔇 k) x = 0 := by
  refine dbarL_eq_zero_of_notMem_tsupport (rhoC 𝔇 k) (fun hc => hx ?_)
  refine closure_mono (fun y hy => ?_) hc
  simp only [Function.mem_support, ne_eq] at hy ⊢
  exact fun h0 => hy (by simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM, h0]; rfl)

/-! ### The holomorphic representative function and the double-sum terms -/

/-- The **holomorphic representative function** `F = Gext(limit-repair(holoRep g)) : X → ℂ` of an
`OmegaDGerm 0` class `g` on `↥V`: the (choice-free) limit-repair of a holomorphic representative,
real-smooth at every point of `V` (`holoFn_contMDiffAt`). -/
noncomputable def holoFn {V : Opens X} {g : MGerm V} (hg : g ∈ OmegaDGerm (0 : Divisor X) V) :
    X → ℂ :=
  fun x => limUnder (𝓝[≠] x) (Gext (holoRep hg))

/-- `holoFn hg` is real-`C^∞` at every point of `V` (the analytic representative is chart-analytic,
`gextLimRep_chart_analyticAt`, bridged to `ContMDiffAt` by `contMDiffAt_real_of_chart_analyticAt`). -/
theorem holoFn_contMDiffAt {V : Opens X} {g : MGerm V} (hg : g ∈ OmegaDGerm (0 : Divisor X) V)
    {y : X} (hy : y ∈ V) : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (holoFn hg) y :=
  contMDiffAt_real_of_chart_analyticAt (gextLimRep_chart_analyticAt (holoRep_mem hg) hy)

/-- The `(j,k)` component of a Čech `1`-cocycle is a holomorphic (`OmegaDGerm 0`) germ-class on the
overlap `U_j ⊓ U_k` (the `sections1` part of `cocycles1`). -/
theorem cocycle_mem (𝔇 : ChartDiskCover X) (f : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)))
    (j k : 𝔇.toFiniteCover.ι) :
    (f : 𝔇.toFiniteCover.Cochain1) (j, k) ∈ OmegaDGerm (0 : Divisor X) (𝔇.U j ⊓ 𝔇.U k) :=
  (Submodule.mem_inf.1 f.2).2 (j, k)

/-- The `(j,k)` **double-sum term** `T_jk = (ρ_j · F_jk) • ∂̄ρ_k`, a global smooth `(0,1)`-valued form
(`F_jk = holoFn` = the analytic representative). Globally smooth by a 3-case `ContMDiffAt` argument:
on the overlap `U_j ⊓ U_k` everything is smooth (`F_jk` via `holoFn_contMDiffAt`); off `tsupport ρ_j`
the factor `ρ_j` vanishes; off `tsupport ρ_k` the factor `∂̄ρ_k` vanishes — and these three opens cover
`X` (a point in neither support-complement lies in `tsupport ρ_j ∩ tsupport ρ_k ⊆ U_j ⊓ U_k`). -/
noncomputable def cechTerm (𝔇 : ChartDiskCover X)
    (f : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) (j k : 𝔇.toFiniteCover.ι) :
    SmoothCOneForms X where
  toFun := fun x => (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) • (dbarRho 𝔇 k x)
  contMDiff_toFun := by
    intro x₀
    by_cases hbj : x₀ ∈ tsupport (cechPoU 𝔇 j)
    · by_cases hbk : x₀ ∈ tsupport (cechPoU 𝔇 k)
      · -- (a) x₀ ∈ U_j ⊓ U_k: the genuine smooth case.
        have hxV : x₀ ∈ ((𝔇.U j ⊓ 𝔇.U k : Opens X) : Set X) :=
          ⟨cechPoU_subordinate 𝔇 j hbj, cechPoU_subordinate 𝔇 k hbk⟩
        have hmulrho : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ) (⊤ : ℕ∞)
            (fun x => ContinuousLinearMap.mul ℝ ℂ (rhoC 𝔇 j x)) x₀ :=
          ContMDiffAt.clm_apply contMDiffAt_const ((rhoC 𝔇 j).contMDiff x₀)
        have hG : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
            (fun x => rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) x₀ :=
          (hmulrho.clm_apply (holoFn_contMDiffAt (cocycle_mem 𝔇 f j k) hxV)).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun x => by simp [ContinuousLinearMap.mul_apply'])
        exact contMDiffAt_cSmul_section hG ((dbarRho 𝔇 k).contMDiff_toFun x₀)
      · -- (c) x₀ ∉ tsupport ρ_k: `∂̄ρ_k = 0` on a neighborhood, so the term is `0`.
        refine ContMDiffAt.congr_of_eventuallyEq (Bundle.contMDiffAt_zeroSection ℝ
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x)) ?_
        filter_upwards [(isClosed_tsupport (cechPoU 𝔇 k)).isOpen_compl.mem_nhds hbk] with x hx
        have hV : (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) • (dbarRho 𝔇 k x) = 0 := by
          rw [dbarRho_eq_zero_of_notMem 𝔇 k hx]; module
        exact congrArg (Bundle.TotalSpace.mk x) hV
    · -- (b) x₀ ∉ tsupport ρ_j: `ρ_j = 0` on a neighborhood, so the term is `0`.
      refine ContMDiffAt.congr_of_eventuallyEq (Bundle.contMDiffAt_zeroSection ℝ
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x)) ?_
      filter_upwards [(isClosed_tsupport (cechPoU 𝔇 j)).isOpen_compl.mem_nhds hbj] with x hx
      have hr : rhoC 𝔇 j x = 0 := by
        simp only [rhoC, ContMDiffMap.comp_apply, ofRealCM,
          image_eq_zero_of_notMem_tsupport hx]; rfl
      have hV : (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) • (dbarRho 𝔇 k x) = 0 := by
        rw [hr, zero_mul]; module
      exact congrArg (Bundle.TotalSpace.mk x) hV

/-- `proj01 α` at a vector, written out: `proj01 α v = ½(α v + i·α(i·v))` (the Wirtinger average). -/
theorem proj01_apply_val (α : ℂ →L[ℝ] ℂ) (v : ℂ) :
    proj01 α v = (2 : ℂ)⁻¹ * (α v + Complex.I * α (Complex.I * v)) := by
  rw [proj01_apply]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, mulI, ContinuousLinearMap.mul_apply',
    Complex.real_smul]
  push_cast; ring

/-- The `(0,1)`-projection is idempotent (`proj01²= proj01`). -/
theorem proj01_idempotent (α : ℂ →L[ℝ] ℂ) : proj01 (proj01 α) = proj01 α := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [proj01_apply_val (proj01 α) v, proj01_apply_val α v, proj01_apply_val α (Complex.I * v)]
  have hI : Complex.I * (Complex.I * v) = -v := by rw [← mul_assoc, Complex.I_mul_I]; ring
  rw [hI, map_neg]
  linear_combination (-(1 / 4 : ℂ) * α v) * Complex.I_sq

/-- Each double-sum term `T_jk` is a `(0,1)`-form: its fiber value `c • (∂̄ρ_k x)` lies in the range
of `proj01` because `∂̄ρ_k x` does (`dbarL_mem_zeroOne`/idempotence) and `proj01` commutes with the
ℂ-scale (`proj01_smul`). -/
theorem cechTerm_mem_zeroOne (𝔇 : ChartDiskCover X)
    (f : ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X))) (j k : 𝔇.toFiniteCover.ι) :
    cechTerm 𝔇 f j k ∈ OneFormsZeroOne X := by
  refine ⟨cechTerm 𝔇 f j k, ?_⟩
  refine ContMDiffSection.ext fun x => ?_
  show proj01 (cechTerm 𝔇 f j k x) = cechTerm 𝔇 f j k x
  show proj01 ((rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) • (dbarRho 𝔇 k x))
    = (rhoC 𝔇 j x * holoFn (cocycle_mem 𝔇 f j k) x) • (dbarRho 𝔇 k x)
  rw [proj01_smul]
  have hfix : proj01 ((dbarRho 𝔇 k) x) = (dbarRho 𝔇 k) x := by
    show proj01 (dbarL (rhoC 𝔇 k) x) = dbarL (rhoC 𝔇 k) x
    rw [dbarL_eq_proj01L_differential]
    show proj01 (proj01 ((differential (rhoC 𝔇 k)) x)) = proj01 ((differential (rhoC 𝔇 k)) x)
    exact proj01_idempotent _
  rw [hfix]

/-- **(Analytic sub-kernel — the Čech → Dolbeault glued-form operator.)** The `ℝ`-linear map sending
a holomorphic Čech `1`-cocycle `f = {f_ij}` to the global `(0,1)`-form `ω` with `ω = ∂̄η_i` on `U_i`,
`η_i := ∑_k ρ_k·f_ik` (partition-of-unity globalization). The genuine analytic content of the inverse:
lift the germ-class cocycle to holomorphic reps, the PoU smooth globalization
(`SmoothPartitionOfUnity.IsSubordinate.contMDiff_finsum_smul`), and glue the local `∂̄η_i` (which agree
on overlaps, `cechCoboundary_telescoping`) into a global section (gluedFun-for-forms). Plan:
`docs/dolbeault_comparison_inverse_plan.md`. -/
noncomputable def cechToDolbeaultForm (𝔇 : ChartDiskCover X) :
    ↥(𝔇.toFiniteCover.cocycles1 (0 : Divisor X)) →ₗ[ℝ] ↥(OneFormsZeroOne X) :=
  sorry

/-- **(Analytic sub-kernel — well-definedness of Čech → Dolbeault.)** A Čech **coboundary** cocycle
maps to a `∂̄`-image (its glued form `ω` is `∂̄` of the global primitive that the coboundary's
holomorphic `0`-cochain supplies), hence to `0` in `H^{0,1} = A^{0,1}/im ∂̄`. This is the kernel
inclusion that makes the lift to `cechH1 = Z¹/B¹` well-defined. -/
theorem cechToDolbeaultForm_coboundary_le (𝔇 : ChartDiskCover X) :
    ((𝔇.toFiniteCover.coboundaries1 (0 : Divisor X)).submoduleOf
        (𝔇.toFiniteCover.cocycles1 (0 : Divisor X))).restrictScalars ℝ
      ≤ LinearMap.ker ((Submodule.mkQ (dbarImageInZeroOne X)) ∘ₗ cechToDolbeaultForm 𝔇) :=
  sorry

/-- **Čech → Dolbeault.** The `ℝ`-linear inverse `H¹(X, 𝒪) → H^{0,1}(X)`. Assembled **sorry-free** from
the analytic glued-form operator `cechToDolbeaultForm` and its well-definedness
`cechToDolbeaultForm_coboundary_le` via `Submodule.liftQ` through the Čech quotient `Z¹/B¹` (scalar
`ℂ → ℝ`). All genuine content lives in the two named sub-kernels above. -/
noncomputable def cech_to_dolbeault (𝔇 : ChartDiskCover X) :
    𝔇.toFiniteCover.cechH1 0 →ₗ[ℝ] DolbeaultH01 X :=
  Submodule.liftQ (((𝔇.toFiniteCover.coboundaries1 (0 : Divisor X)).submoduleOf
      (𝔇.toFiniteCover.cocycles1 (0 : Divisor X))).restrictScalars ℝ)
    ((Submodule.mkQ (dbarImageInZeroOne X)) ∘ₗ cechToDolbeaultForm 𝔇)
    (cechToDolbeaultForm_coboundary_le 𝔇)

end Jacobians.Dolbeault
