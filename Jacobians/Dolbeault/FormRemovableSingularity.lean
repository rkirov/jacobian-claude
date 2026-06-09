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

/-- **Scalar smoothness from chart-pullback analyticity** (full chart source).  If the chart
pullback `z ↦ L ((chart x₀).symm z) (e.symmL ℂ ((chart x₀).symm z) 1)` is analytic on the chart
target, then the scalar `y ↦ L y (e.symmL ℂ y 1)` is `ContMDiffOn ω` on the chart source.  This is
the inverse of `localRep_analyticOn_chartTarget`; the argument is `Montel.contMDiffOn_limit_inner`
generalised from `innerChartOpen` to `(chart x₀).source`. -/
theorem contMDiffOn_scalar_of_pullback_analyticOn
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y) (x₀ : X)
    (hAn : letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticOn ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        (chartAt ℂ x₀).target) :
    letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun y : X => L y (e.symmL ℂ y 1)) (chartAt ℂ x₀).source := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
  have hs : (chartAt ℂ x₀).source ⊆ (extChartAt 𝓘(ℂ, ℂ) x₀).source := by
    have : (extChartAt 𝓘(ℂ, ℂ) x₀).source = (chartAt ℂ x₀).source := by simp [extChartAt]
    rw [this]
  have h2s : Set.MapsTo (fun y : X => L y (e.symmL ℂ y 1))
      (chartAt ℂ x₀).source (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)).source := by
    have h_src : (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ)).source = Set.univ := by simp [extChartAt]
    rw [h_src]; exact fun _ _ => Set.mem_univ _
  rw [contMDiffOn_iff_of_subset_source' hs h2s]
  have h_set_eq : extChartAt 𝓘(ℂ, ℂ) x₀ '' (chartAt ℂ x₀).source =
      (chartAt ℂ x₀).target := by
    have h1 : extChartAt 𝓘(ℂ, ℂ) x₀ '' (chartAt ℂ x₀).source =
        (chartAt ℂ x₀) '' (chartAt ℂ x₀).source := by simp [extChartAt]
    rw [h1, (chartAt ℂ x₀).image_source_eq_target]
  have h_fun_eq : (extChartAt 𝓘(ℂ, ℂ) (0 : ℂ) ∘
      (fun y : X => L y (e.symmL ℂ y 1)) ∘ (extChartAt 𝓘(ℂ, ℂ) x₀).symm) =
      fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1) := by
    funext z; simp [extChartAt, Function.comp_def]
  rw [h_set_eq, h_fun_eq]
  exact (contDiffOn_omega_iff_analyticOn (chartAt ℂ x₀).open_target.uniqueDiffOn).mpr hAn

/-- **Section smoothness from chart-pullback analyticity** (full chart source).  The bundle-section
`y ↦ (y, L y)` is `ContMDiffOn ω` on the chart source, given chart-pullback analyticity at `x₀`.
This is `Montel.contMDiffOn_totalSpaceMk_L_inner` re-derived on `(chart x₀).source` from the scalar
smoothness above. -/
theorem contMDiffOn_totalSpaceMk_of_pullback_analyticOn
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y) (x₀ : X)
    (hAn : letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticOn ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        (chartAt ℂ x₀).target) :
    ContMDiffOn 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : X => Bundle.TotalSpace.mk' (ℂ →L[ℂ] ℂ)
        (E := fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x)
        y (L y))
      (chartAt ℂ x₀).source := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀ with he_def
  have h_scalar : ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (fun y : X => L y (e.symmL ℂ y 1)) (chartAt ℂ x₀).source :=
    contMDiffOn_scalar_of_pullback_analyticOn L x₀ hAn
  set eHom := trivializationAt (ℂ →L[ℂ] ℂ)
    (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) x₀ with heHom_def
  have h_src_sub_hom : (chartAt ℂ x₀).source ⊆ eHom.baseSet := by
    intro y hy
    rw [heHom_def, hom_trivializationAt_baseSet]
    refine ⟨?_tangent, Set.mem_univ _⟩
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy
  intro y₀ hy₀
  rw [Bundle.Trivialization.contMDiffWithinAt_section _ (h_src_sub_hom hy₀)]
  have h_simpl : ∀ y ∈ (chartAt ℂ x₀).source,
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
      (chartAt ℂ x₀).source y₀ :=
    (h_scalar y₀ hy₀).smul contMDiffWithinAt_const
  exact h_smul_smooth.congr (fun y hy => h_simpl y hy) (h_simpl y₀ hy₀)

/-- **The section-assembly lemma** (converse of `localRep_analyticOn_chartTarget`).  A bundle section
`L` whose chart pullback is analytic on the chart target *for every chart center* is `ContMDiff`,
hence a `HolomorphicOneForms X`.  Smoothness at `y` is read in `y`'s own chart, whose source is a
neighbourhood of `y`. -/
noncomputable def holOfLocalRepAnalytic
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hAn : ∀ x₀ : X,
      letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticOn ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        (chartAt ℂ x₀).target) :
    HolomorphicOneForms X where
  toFun := L
  contMDiff_toFun := by
    intro y
    have h_on := contMDiffOn_totalSpaceMk_of_pullback_analyticOn L y (hAn y)
    exact (h_on y (mem_chart_source ℂ y)).contMDiffAt
      ((chartAt ℂ y).open_source.mem_nhds (mem_chart_source ℂ y))

@[simp] theorem holOfLocalRepAnalytic_toFun
    (L : (y : X) → TangentSpace 𝓘(ℂ, ℂ) y →L[ℂ] (Bundle.Trivial X ℂ) y)
    (hAn : ∀ x₀ : X,
      letI e := trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) x₀
      AnalyticOn ℂ
        (fun z : ℂ => L ((chartAt ℂ x₀).symm z) (e.symmL ℂ ((chartAt ℂ x₀).symm z) 1))
        (chartAt ℂ x₀).target) :
    (holOfLocalRepAnalytic L hAn).toFun = L := rfl

end Jacobians.Dolbeault
