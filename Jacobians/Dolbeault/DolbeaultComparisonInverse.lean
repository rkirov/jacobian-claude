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
