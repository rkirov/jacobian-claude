/-
  **Removable singularity for meromorphic 1-forms** (Forster §17.4, the reverse of `holToMeroₗ`).

  Gate (C)'s one isolated analytic gap: a meromorphic 1-form `α` with `formOrderW α ≥ 0` everywhere
  (i.e. `α ∈ omegaD 0`) is — modulo the removable-singularity germ-junk — a genuine *holomorphic*
  1-form.  This is the reverse map `Ω_0 → HolomorphicOneForms` inverse to the injection
  `holToMeroₗ : HolomorphicOneForms ↪ Ω_0` (`MeromorphicOneFormSystem.lean`), giving the §17.4
  equality `omegaDim 0 = genus X` UNCONDITIONALLY and `FiniteDimensional ℂ (omegaDModule 0)`.

  ## The math

  `α ∈ omegaD 0` means the chart coefficient `formCoeff α.toFun x` is `MeromorphicAt` with
  `meromorphicOrderAt ≥ 0` at `chart x x`, for every `x`.  Order `≥ 0` means the coefficient germ
  agrees, off `x`, with an **analytic** function (`exists_analyticAt_eventuallyEq_…`, the standard
  removable singularity).  We repair `α.toFun` to its analytic value:

  * `repairedCoeff α x₀` is the normal-form `toMeromorphicNFAt` of `localRep`'s pullback — analytic
    on the chart target, and equal to `localRep α.toFun` off the (removed) singular points.
  * `repairedSection α` is the genuine bundle section `y ↦ repaired-coefficient • frame`, smooth
    because its chart pullback is analytic (the section-assembly lemma `holOfLocalRepAnalytic`,
    extracted from the Montel completeness reconstruction `contMDiffOn_totalSpaceMk_L_inner`).

  This `repairedSection α : HolomorphicOneForms X` has `holToMero (repairedSection α)` germ-equal to
  `α` (they agree off the singular points), so `holToOmega0Module` is **surjective**.  With its
  proven injectivity (`holToOmega0Module_injective`) this is a `LinearEquiv`
  `HolomorphicOneForms X ≃ₗ omegaDModule 0`, whence:

  * `FiniteDimensional ℂ (omegaDModule 0)` (transported from `HolomorphicOneForms`, finite-dim);
  * `omegaDim 0 = genus X` (the §17.4 equality, both directions now proven).

  Chaining with `CanonicalForm17Data.hKgenus` (`CanonicalFormIso.lean`) makes the Serre-duality
  input `lDim K = genus X` UNCONDITIONAL.

  Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.4; Mathlib's
  `MeromorphicAt.analyticAt` / `toMeromorphicNFAt` removable singularity.
-/
import Jacobians.Dolbeault.CanonicalFormIso

open scoped Manifold ContDiff Topology Bundle
open Module Filter
open Jacobians.Montel

namespace Jacobians.Dolbeault

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 1: the section-assembly lemma

The converse of `Montel.localRep_analyticOn_chartTarget`: a bundle section `L` whose chart pullback
`z ↦ L ((chart x₀).symm z) (e.symmL ℂ … 1)` is `AnalyticOn (chart x₀).target` for every chart center
`x₀` is a smooth section, hence a `HolomorphicOneForms X`.

The proof mirrors `Montel.contMDiffOn_totalSpaceMk_L_inner` (the smooth-from-analytic half of the
Montel completeness reconstruction), but feeds analyticity directly (no sequence limit) and works on
the full chart source, so smoothness at any `y` is read in `y`'s own chart. -/

/-- **Scalar smoothness from chart-pullback analyticity** on an open subset `S` of the chart source.
If the chart pullback is analytic on `chart x₀ '' S`, then the scalar `y ↦ L y (e.symmL ℂ y 1)` is
`ContMDiffOn ω` on `S`.  The inverse of `localRep_analyticOn_chartTarget`; the argument is
`Montel.contMDiffOn_limit_inner` with `S` in place of `innerChartOpen`. -/
theorem contMDiffOn_scalar_of_pullback_analyticOn
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y) (x₀ : X)
    {S : Set X} (hSopen : IsOpen S) (hSsub : S ⊆ (chartAt ℂ x₀).source)
    (hAn : letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticOn ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        ((chartAt ℂ x₀) '' S)) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun y : X => L y (e.symmL ℂ y 1)) S := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  have hs : S ⊆ (extChartAt 𝓘(ℂ, ℂ) x₀).source := by
    have : (extChartAt 𝓘(ℂ, ℂ) x₀).source = (chartAt ℂ x₀).source := by simp [extChartAt]
    rw [this]; exact hSsub
  have h2s : Set.MapsTo (fun y : X => L y (e.symmL ℂ y 1))
      S (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)).source := by
    have h_src : (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)).source = Set.univ := by simp [extChartAt]
    rw [h_src]; exact fun _ _ => Set.mem_univ _
  rw [contMDiffOn_iff_of_subset_source' hs h2s]
  have h_set_eq : extChartAt 𝓘(ℂ, ℂ) x₀ '' S = (chartAt ℂ x₀) '' S := by simp [extChartAt]
  have h_fun_eq : (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ) ∘
      (fun y : X => L y (e.symmL ℂ y 1)) ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm) =
      fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1) := by
    funext z; simp [extChartAt, Function.comp_def]
  rw [h_set_eq, h_fun_eq]
  have hSimg_open : IsOpen ((chartAt ℂ x₀) '' S) :=
    (chartAt ℂ x₀).isOpen_image_iff_of_subset_source hSsub |>.mpr hSopen
  exact (contDiffOn_omega_iff_analyticOn hSimg_open.uniqueDiffOn).mpr hAn

/-- **Section smoothness from chart-pullback analyticity** on an open subset `S` of the chart source.
The bundle-section `y ↦ (y, L y)` is `ContMDiffOn ω` on `S`.  This is
`Montel.contMDiffOn_totalSpaceMk_L_inner` re-derived on an arbitrary open `S ⊆ (chart x₀).source`. -/
theorem contMDiffOn_totalSpaceMk_of_pullback_analyticOn
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y) (x₀ : X)
    {S : Set X} (hSopen : IsOpen S) (hSsub : S ⊆ (chartAt ℂ x₀).source)
    (hAn : letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticOn ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        ((chartAt ℂ x₀) '' S)) :
    ContMDiffOn 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)
        y (L y))
      S := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀ with he_def
  have h_scalar : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun y : X => L y (e.symmL ℂ y 1)) S :=
    contMDiffOn_scalar_of_pullback_analyticOn L x₀ hSopen hSsub hAn
  set eHom := trivializationAt (ℂ →L[ℂ] ℂ)
    (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) x₀ with heHom_def
  have h_src_sub_hom : S ⊆ eHom.baseSet := by
    intro y hy
    rw [heHom_def, hom_trivializationAt_baseSet]
    refine ⟨?_tangent, Set.mem_univ _⟩
    rw [TangentBundle.trivializationAt_baseSet]
    exact hSsub hy
  intro y₀ hy₀
  rw [Bundle.Trivialization.contMDiffWithinAt_section _ (h_src_sub_hom hy₀)]
  have h_simpl : ∀ y ∈ S,
      (eHom (Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ) y (L y))).2 =
        (L y (e.symmL ℂ y 1)) • (ContinuousLinearMap.id ℂ ℂ) := by
    intro y hy
    rw [heHom_def, hom_trivializationAt_apply]
    apply ContinuousLinearMap.ext
    intro v
    have h_triv_id : Bundle.Trivialization.continuousLinearMapAt ℂ
        (trivializationAt ℂ (Bundle.Trivial X ℂ) x₀) y = ContinuousLinearMap.id ℂ ℂ :=
      Bundle.Trivial.continuousLinearMapAt_trivialization ℂ X ℂ y
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp',
               Function.comp_apply, h_triv_id, ContinuousLinearMap.id_apply,
               ContinuousLinearMap.smul_apply]
    have hv : (v : ℂ) = v • (1 : ℂ) := by rw [smul_eq_mul, mul_one]
    conv_lhs => rw [hv, (e.symmL ℂ y).map_smul]
    rw [(L y).map_smul]
    simp only [smul_eq_mul]; ring
  have h_smul_smooth : ContMDiffWithinAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun y : X => (L y (e.symmL ℂ y 1)) • (ContinuousLinearMap.id ℂ ℂ))
      S y₀ :=
    (h_scalar y₀ hy₀).smul contMDiffWithinAt_const
  exact h_smul_smooth.congr (fun y hy => h_simpl y hy) (h_simpl y₀ hy₀)

/-- **The section-assembly lemma, local form.**  A bundle section `L` whose chart pullback in *each
point's own chart* is `AnalyticAt` the chart centre is `ContMDiff`, hence a `HolomorphicOneForms X`.
Smoothness at `y` is read in `y`'s own chart: `AnalyticAt` gives analyticity on an open neighbourhood
of `chart y y`, whose chart-preimage is an open neighbourhood of `y`. -/
noncomputable def holOfLocalRepAnalyticAt
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hAn : ∀ x₀ : X,
      letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticAt ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        ((chartAt ℂ x₀) x₀)) :
    HolomorphicOneForms X where
  toFun := L
  contMDiff_toFun := by
    intro y
    set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y
    -- `AnalyticAt` ⇒ analytic on an open ball `U := ball (chart y y) r` around `chart y y`.
    obtain ⟨r, hr, hUan⟩ := (hAn y).exists_ball_analyticOnNhd
    set U : Set ℂ := Metric.ball ((chartAt ℂ y) y) r with hU_def
    have hUopen : IsOpen U := Metric.isOpen_ball
    have hUmem : (chartAt ℂ y) y ∈ U := Metric.mem_ball_self hr
    -- restrict to the chart source ∩ chart⁻¹ U, an open nbhd of `y`.
    set S : Set X := (chartAt ℂ y).source ∩ (chartAt ℂ y) ⁻¹' U with hS_def
    have hSopen : IsOpen S :=
      (chartAt ℂ y).continuousOn.isOpen_inter_preimage (chartAt ℂ y).open_source hUopen
    have hSsub : S ⊆ (chartAt ℂ y).source := Set.inter_subset_left
    have hyS : y ∈ S := ⟨mem_chart_source ℂ y, by
      simp only [hS_def, Set.mem_preimage]; exact hUmem⟩
    -- pullback analytic on `chart y '' S ⊆ U`.
    have himg : (chartAt ℂ y) '' S ⊆ U := by
      rintro z ⟨w, hw, rfl⟩; exact hw.2
    have hAnS : AnalyticOn ℂ
        (fun z : ℂ => L ((chartAt ℂ y).symm z) (e.symmL ℂ ((chartAt ℂ y).symm z) 1))
        ((chartAt ℂ y) '' S) := (hUan.mono himg).analyticOn
    have h_on := contMDiffOn_totalSpaceMk_of_pullback_analyticOn L y hSopen hSsub hAnS
    exact (h_on y hyS).contMDiffAt (hSopen.mem_nhds hyS)

@[simp] theorem holOfLocalRepAnalyticAt_toFun
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hAn : ∀ x₀ : X,
      letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticAt ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        ((chartAt ℂ x₀) x₀)) :
    (holOfLocalRepAnalyticAt L hAn).toFun = L := rfl

/-! ## Part 2: the repaired holomorphic section of an order-`≥ 0` meromorphic 1-form

For `α ∈ omegaD 0`, the chart coefficient `formCoeff α.toFun x` is `MeromorphicAt` with order `≥ 0`
at every chart centre.  We repair the section to its analytic value.

The single key structural fact is that the removable-singularity *junk* of `α.toFun` is isolated to
chart centres: for `w` in a *punctured* neighbourhood of any `x₀`, the covector `α.toFun w` is pinned
by `α`'s meromorphy at `x₀` (`toFun_eq_localRep_smul`), so reading it in `w`'s own chart it equals the
analytic normal-form value (`repVal`).  Hence the per-point repair `repairedSection` is a genuine
holomorphic section whose germ matches `α` everywhere off the centres. -/

/-- The frame covector at `y` from the canonical tangent trivialisation: `φ_y : T_y X →L[ℂ] ℂ`. -/
noncomputable def frameCovector (y : X) : TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ :=
  letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y
  (e.continuousLinearEquivAt ℂ y (by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source ℂ y) :
    TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] ℂ)

/-- `φ_y (e_y.symmL ℂ y 1) = 1`: the frame covector evaluated on the canonical frame vector. -/
theorem frameCovector_symmL_self (y : X) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y
    frameCovector y (e.symmL ℂ y 1) = 1 := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) y
  have hy : y ∈ e.baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact mem_chart_source ℂ y
  set φ := e.continuousLinearEquivAt ℂ y hy with hφ
  show φ (e.symmL ℂ y 1) = 1
  have h_symmL : (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) = e.symmL ℂ y :=
    Bundle.Trivialization.symm_continuousLinearEquivAt_eq' e hy
  rw [show e.symmL ℂ y 1 = (φ.symm : ℂ →L[ℂ] TangentSpace 𝓘(ℂ, ℂ) y) 1 from by rw [h_symmL]]
  exact φ.apply_symm_apply 1

/-- The **repaired chart value** of `α` at `y`: the normal-form value of the chart coefficient at the
chart centre — the removable-singularity limit `lim_{z → chart y y} formCoeff α.toFun y (z)`. -/
noncomputable def repVal (α : MeromorphicOneForm X) (y : X) : ℂ :=
  toMeromorphicNFAt (formCoeff α.toFun y) ((chartAt ℂ y) y) ((chartAt ℂ y) y)

/-- The repaired chart coefficient `toMeromorphicNFAt (formCoeff α.toFun y) (chart y y)` is
`AnalyticAt (chart y y)` when `α ∈ omegaD 0` (order `≥ 0` ⟹ removable singularity).  Reuses the
repo's `exists_analyticAt_eventuallyEq_of_meromorphicOrderAt_nonneg`. -/
theorem analyticAt_repairedCoeff {α : MeromorphicOneForm X} (hα : α ∈ omegaD (X := X) 0) (y : X) :
    AnalyticAt ℂ (toMeromorphicNFAt (formCoeff α.toFun y) ((chartAt ℂ y) y)) ((chartAt ℂ y) y) := by
  have hmero : MeromorphicAt (formCoeff α.toFun y) ((chartAt ℂ y) y) := α.meromorphic y
  have hord : 0 ≤ meromorphicOrderAt (formCoeff α.toFun y) ((chartAt ℂ y) y) := by
    have := hα y
    simpa [MeromorphicOneForm.formOrderW] using this
  have hNF : MeromorphicNFAt (toMeromorphicNFAt (formCoeff α.toFun y) ((chartAt ℂ y) y))
      ((chartAt ℂ y) y) := meromorphicNFAt_toMeromorphicNFAt
  have hord_nf : 0 ≤ meromorphicOrderAt (toMeromorphicNFAt (formCoeff α.toFun y) ((chartAt ℂ y) y))
      ((chartAt ℂ y) y) := by
    rwa [meromorphicOrderAt_congr hmero.eq_nhdsNE_toMeromorphicNFAt] at hord
  exact hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp hord_nf

/-- The chart coefficient agrees, off the centre, with its repaired (normal-form) coefficient. -/
theorem formCoeff_eventuallyEq_repairedCoeff (α : MeromorphicOneForm X) (y : X) :
    formCoeff α.toFun y =ᶠ[𝓝[≠] ((chartAt ℂ y) y)]
      toMeromorphicNFAt (formCoeff α.toFun y) ((chartAt ℂ y) y) :=
  (α.meromorphic y).eq_nhdsNE_toMeromorphicNFAt

end Jacobians.Dolbeault
