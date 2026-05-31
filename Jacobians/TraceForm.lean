/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.PeriodLattice

/-!
# Trace (pushforward) of a holomorphic 1-form along a branched cover

The global assembly of `f₊ : Ω¹(X) → Ω¹(Y)` for a non-constant holomorphic map
`f : X → Y` of compact Riemann surfaces.

This file builds the trace as a **fibre sum** off the branch locus, proves it is
holomorphic there, assembles it into a global form via the branch-point
extension, and proves the projection formula at the period level.

## Design

For `ω : HolomorphicOneForms X` and `y ∉ branchLocus f`, the fibre `f⁻¹{y}` is
finite (`fiber_finite_off_branchLocus`) and every `x` in it is off `criticalSet f`,
so `mfderiv f x : T_x X →L[ℂ] T_y Y` is invertible and `(ω x) ∘ (mfderiv f x)⁻¹`
is a cotangent covector at `y`. Summing over the fibre gives the trace covector.

Holomorphicity off the branch locus is local: over a `properNbhd`-shrunk open
`V ∋ y₀` the cover splits into finitely many sheets, each carrying a holomorphic
section `s : V → X`, and on `V` the fibre sum equals `∑_k pullbackForm s_k ω`, a
finite sum of holomorphic 1-forms.

## References

Forster §§4, 10; Griffiths–Harris Ch. 2 §2.7 (the trace map for forms).
-/

set_option linter.unusedSectionVars false

namespace Jacobians

open scoped Manifold ContDiff Bundle Topology
open Filter Set

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y] [Nonempty Y]
    [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-- The covector at `y = f x` obtained by pulling back `α x` through the inverse of
`mfderiv f x`. The summand of the fibre-sum trace.

Typed in the model fibre `ℂ →L[ℂ] ℂ` (definitionally equal to `T_{f x} Y →L[ℂ] ℂ`
and to `T_y Y →L[ℂ] ℂ`, since `TangentSpace 𝓘(ℂ) _ = ℂ` reduces to `ℂ`). Working in
the model fibre means the fibre sum requires **no transport** between cotangent
spaces of different fibre points.

(NB: the form variable is `α`, not `ω` — in this codebase `ω` is the analytic
smoothness exponent `IsManifold 𝓘(ℂ) ω X`.) -/
noncomputable def traceSummand (f : X → Y) (α : HolomorphicOneForms X) (x : X) :
    ℂ →L[ℂ] ℂ :=
  (α.toFun x).comp ((mfderiv 𝓘(ℂ) 𝓘(ℂ) f x).inverse)

/-- Value of the single-section pullback covector `(α (g y)) ∘ mfderiv g y` at a
point `y`, in the cotangent fibre at `y`. The per-sheet term of the local
representation of the fibre-sum trace over a base neighborhood. -/
noncomputable def sheetPullback (α : HolomorphicOneForms X) (g : Y → X) (y : Y) :
    TangentSpace 𝓘(ℂ) y →L[ℂ] ℂ :=
  (α.toFun (g y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g y)

/-! ### Local pullback smoothness (`ContMDiffAt`-only)

The smoothness core of `pullbackForm`, weakened from a *global* `ContMDiff`
hypothesis on the map to a *pointwise* `ContMDiffAt`. This is what lets us pull a
form back along a local holomorphic section (`exists_holo_localInverse_…`), which
is only `ContMDiffOn` its domain. Apart from the hypothesis it is a verbatim copy
of the `pullbackForm.contMDiff_toFun` argument. -/

/-- The hom-bundle section `y ↦ (α (s y)) ∘ mfderiv s y` is `ContMDiffAt` at `y₀`
(as a section into the cotangent bundle of `Y`) whenever `s` is `ContMDiffAt` at
`y₀`. Pointwise version of `pullbackForm`'s `contMDiff_toFun` proof: the global
`ContMDiff` hypothesis there is only ever used at the single point `x₀`, so it
weakens to `ContMDiffAt`. This is what allows pulling a form back along a *local*
holomorphic section, which is only `ContMDiffOn` its domain. -/
theorem contMDiffAt_pullback_section (α : HolomorphicOneForms X) {s : Y → X} {y₀ : Y}
    (hs : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω s y₀) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk'
        (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
        ((α.toFun (s y)).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) s y))) y₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hA : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun y => ContinuousLinearMap.inCoordinates ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ)
          (s y₀) (s y) (s y₀) (s y) (α.toFun (s y))) y₀ := by
    have hα := α.contMDiff_toFun (s y₀)
    rw [contMDiffAt_hom_bundle] at hα
    obtain ⟨_, h⟩ := hα
    exact h.comp y₀ hs
  have hB : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun y => ContinuousLinearMap.inCoordinates ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := X))
          y₀ y (s y₀) (s y) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) s y)) y₀ :=
    hs.mfderiv_const (le_refl _)
  have hcomp : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun y => (ContinuousLinearMap.inCoordinates ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := X)) ℂ (Bundle.Trivial X ℂ)
          (s y₀) (s y) (s y₀) (s y) (α.toFun (s y))).comp
        (ContinuousLinearMap.inCoordinates ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) ℂ
          (TangentSpace 𝓘(ℂ, ℂ) (M := X))
          y₀ y (s y₀) (s y) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) s y))) y₀ :=
    hA.clm_comp hB
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [
    ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := Y)) y₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt ℂ _ y₀)),
    (hs.continuousAt.preimage_mem_nhds
      ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) (s y₀)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt ℂ _ (s y₀))))
    ] with y hy_TS_Y hy_TS_X
  ext
  simp only [ContinuousLinearMap.inCoordinates,
    ContinuousLinearMap.comp_apply,
    Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_apply]
  rw [Bundle.Trivialization.symmL_continuousLinearMapAt _ hy_TS_X]

/-- `sheetPullback α g` is `ContMDiffAt` at `y₀` whenever `g` is `ContMDiffAt`
there. Restatement of `contMDiffAt_pullback_section` in terms of `sheetPullback`
(as a section into the cotangent bundle of `Y`). -/
theorem contMDiffAt_sheetPullback (α : HolomorphicOneForms X) {g : Y → X} {y₀ : Y}
    (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω g y₀) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk'
        (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
        (sheetPullback α g y)) y₀ :=
  contMDiffAt_pullback_section α hg

/-! ### The section's derivative is the inverse of `mfderiv f` -/

/-- For a two-sided local inverse pair `(f, s)` around `(x₀, y₀)` (i.e. `f ∘ s = id`
near `y₀` and `s ∘ f = id` near `x₀`, with `s y₀ = x₀` and `f x₀ = y₀`), the
derivative of the section is the `ContinuousLinearMap.inverse` of `mfderiv f x₀`.
Chain rule (`mfderiv_comp`) on both local identities + `mfderiv_id` +
`ContinuousLinearMap.inverse_eq`. -/
theorem mfderiv_section_eq_inverse {f : X → Y} {s : Y → X} {x₀ : X} {y₀ : Y}
    (hsx : s y₀ = x₀) (hfx : f x₀ = y₀)
    (hf_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x₀)
    (hs_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) s y₀)
    (hfs : (f ∘ s) =ᶠ[𝓝 y₀] id) (hsf : (s ∘ f) =ᶠ[𝓝 x₀] id) :
    mfderiv 𝓘(ℂ) 𝓘(ℂ) s y₀ = (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x₀).inverse := by
  -- f ∘ s = id near y₀  ⟹  mfderiv f x₀ ∘SL mfderiv s y₀ = id on T_{y₀} Y.
  have hcomp_fs : (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x₀).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) s y₀) =
      ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) y₀) := by
    have h1 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (f ∘ s) y₀ = mfderiv 𝓘(ℂ) 𝓘(ℂ) (id : Y → Y) y₀ :=
      hfs.mfderiv_eq
    rw [mfderiv_id] at h1
    rw [← h1, mfderiv_comp y₀ (hsx ▸ hf_diff) hs_diff, hsx]
  -- s ∘ f = id near x₀  ⟹  mfderiv s y₀ ∘ mfderiv f x₀ = id on T_{x₀} X.
  have hcomp_sf : (mfderiv 𝓘(ℂ) 𝓘(ℂ) s y₀).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x₀) =
      ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) x₀) := by
    have h1 : mfderiv 𝓘(ℂ) 𝓘(ℂ) (s ∘ f) x₀ = mfderiv 𝓘(ℂ) 𝓘(ℂ) (id : X → X) x₀ :=
      hsf.mfderiv_eq
    rw [mfderiv_id] at h1
    rw [← h1, mfderiv_comp x₀ (hfx ▸ hs_diff) hf_diff, hfx]
  exact (ContinuousLinearMap.inverse_eq hcomp_fs hcomp_sf).symm

/-! ### Two-sided local section at a non-critical point

Strengthens `exists_holo_localInverse_of_notMem_criticalSet` to a genuine
two-sided local inverse: combining the section `g` (a right inverse, `f ∘ g = id`
on `V`) with the local injectivity of `f` off the critical set
(`isLocalHomeoOffCritical`) gives `g ∘ f = id` on a neighborhood of `x₀` as well.
This is exactly the data `mfderiv_section_eq_inverse` and
`contMDiffAt_pullback_section` consume. -/

/-- A `C^ω` two-sided local inverse `g` at a non-critical point `x₀`: an open
`V ∋ f x₀` with `g (f x₀) = x₀`, `f ∘ g = id` on `V`, `g ∘ f = id` near `x₀`, and
`g` smooth on `V`. -/
theorem exists_twoSided_localInverse (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) {x₀ : X} (hxcrit : x₀ ∉ criticalSet f) :
    ∃ (g : Y → X) (V : Set Y), IsOpen V ∧ f x₀ ∈ V ∧ g (f x₀) = x₀ ∧
      (∀ y ∈ V, f (g y) = y) ∧ ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g V ∧
      ((g ∘ f) =ᶠ[𝓝 x₀] id) := by
  obtain ⟨g, V, hVopen, hfxV, hgfx, hsec, hgsmooth⟩ :=
    exists_holo_localInverse_of_notMem_criticalSet f hf hnonconst hxcrit
  obtain ⟨U, hUopen, hxU, hinj, -⟩ := isLocalHomeoOffCritical f hf hnonconst hxcrit
  refine ⟨g, V, hVopen, hfxV, hgfx, hsec, hgsmooth, ?_⟩
  -- `g` is continuous at `f x₀` (open domain `V`), with `g (f x₀) = x₀ ∈ U`.
  have hg_contAt : ContinuousAt g (f x₀) :=
    (hgsmooth.continuousOn.continuousAt (hVopen.mem_nhds hfxV))
  have hgU : ∀ᶠ y in 𝓝 (f x₀), g y ∈ U :=
    hg_contAt.eventually_mem (by rw [hgfx]; exact hUopen.mem_nhds hxU)
  -- Pull the two `Y`-side neighborhoods of `f x₀` back along `f` (continuous at `x₀`).
  have hf_contAt : ContinuousAt f x₀ := hf.continuous.continuousAt
  have hxV : ∀ᶠ x in 𝓝 x₀, f x ∈ V := hf_contAt.eventually_mem (hVopen.mem_nhds hfxV)
  have hxgU : ∀ᶠ x in 𝓝 x₀, g (f x) ∈ U := hf_contAt.eventually (p := fun y => g y ∈ U) hgU
  have hxinU : ∀ᶠ x in 𝓝 x₀, x ∈ U := hUopen.eventually_mem hxU
  filter_upwards [hxV, hxgU, hxinU] with x hxVmem hxgUmem hxinUmem
  show g (f x) = x
  -- `f (g (f x)) = f x` (right inverse on `V`); inject on `U` (`g (f x), x ∈ U`).
  exact hinj hxgUmem hxinUmem (hsec (f x) hxVmem)

/-! ### Value identity: the fibre summand is a section pullback -/

/-- **Key value identity.** At `y₀ = f x₀`, the trace summand `traceSummand f α x₀`
equals `sheetPullback α g y₀` for any two-sided local section `g` through `x₀`.
Combines `g (f x₀) = x₀` with `mfderiv g (f x₀) = (mfderiv f x₀).inverse`
(`mfderiv_section_eq_inverse`), so the off-branch fibre sum is, sheet by sheet, a
holomorphic pullback. -/
theorem traceSummand_eq_sheetPullback {f : X → Y} {g : Y → X} {x₀ : X}
    (α : HolomorphicOneForms X) (hgfx : g (f x₀) = x₀)
    (hf_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x₀)
    (hg_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g (f x₀))
    (hfs : (f ∘ g) =ᶠ[𝓝 (f x₀)] id) (hsf : (g ∘ f) =ᶠ[𝓝 x₀] id) :
    traceSummand f α x₀ = sheetPullback α g (f x₀) := by
  have hinv : mfderiv 𝓘(ℂ) 𝓘(ℂ) g (f x₀) = (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x₀).inverse :=
    mfderiv_section_eq_inverse hgfx rfl hf_diff hg_diff hfs hsf
  show (α.toFun x₀).comp ((mfderiv 𝓘(ℂ) 𝓘(ℂ) f x₀).inverse) =
    (α.toFun (g (f x₀))).comp (mfderiv 𝓘(ℂ) 𝓘(ℂ) g (f x₀))
  rw [hinv, hgfx]

/-- `traceSummand` is additive in the form. -/
theorem traceSummand_add (f : X → Y) (α β : HolomorphicOneForms X) (x : X) :
    traceSummand f (α + β) x = traceSummand f α x + traceSummand f β x := by
  show ((α + β).toFun x).comp _ = (α.toFun x).comp _ + (β.toFun x).comp _
  rw [show (α + β).toFun x = α.toFun x + β.toFun x from rfl, ContinuousLinearMap.add_comp]

/-- `traceSummand` is ℂ-homogeneous in the form. -/
theorem traceSummand_smul (f : X → Y) (c : ℂ) (α : HolomorphicOneForms X) (x : X) :
    traceSummand f (c • α) x = c • traceSummand f α x := by
  show ((c • α).toFun x).comp _ = c • (α.toFun x).comp _
  rw [show (c • α).toFun x = c • α.toFun x from rfl, ContinuousLinearMap.smul_comp]

/-! ## The off-branch fibre-sum, holomorphic

We package the trace value at `y` as a `finsum` over the fibre `f⁻¹{y}` (total:
`= 0` when the fibre is infinite, which never happens off the branch locus). Off
branch, the cover splits into finitely many holomorphic sheets over a common base
neighborhood `V`, and on `V` the fibre sum is `∑ᵢ sheetPullback α (gᵢ)`, a finite
sum of holomorphic one-forms — hence holomorphic. -/

/-- Retyping of the trace summand to the cotangent fibre at `y`, given `f x = y`.
Since `TangentSpace 𝓘(ℂ) (f x) = TangentSpace 𝓘(ℂ) y` definitionally collapses to
`ℂ`, this is a transport along `f x = y`. -/
noncomputable def traceSummandAt (f : X → Y) (α : HolomorphicOneForms X) (_y : Y) (x : X) :
    ℂ →L[ℂ] ℂ :=
  traceSummand f α x

/-- **Trace value (fibre sum).** The covector at `y` obtained by summing
`traceSummand f α x` over the fibre `f⁻¹{y}`. Total via `finsum` (`= 0` when the
fibre is infinite); off the branch locus the fibre is finite and this is the
genuine finite sum. Typed in the model fibre `ℂ →L[ℂ] ℂ`, which is definitionally
the cotangent fibre `T_y Y →L[ℂ] ℂ`. -/
noncomputable def traceFun (f : X → Y) (α : HolomorphicOneForms X) (y : Y) :
    ℂ →L[ℂ] ℂ :=
  ∑ᶠ (x : X) (_ : x ∈ f ⁻¹' {y}), traceSummandAt f α y x

/-- **Local sheet system** of a branched cover `f` over a base neighborhood `V` of
`y₀` (off the branch locus). Bundles the finitely many holomorphic sections whose
images sweep out the entire fibre at each point of `V`. This is precisely the
trivialization data of the covering `isCoveringMapOn_compl_branchLocus`, repackaged
as sections (Forster §4.22). -/
structure LocalSheetSystem (f : X → Y) (y₀ : Y) where
  /-- Number of sheets (classically `= deg f`). -/
  n : ℕ
  /-- The base neighborhood over which the cover trivializes. -/
  V : Set Y
  isOpen_V : IsOpen V
  mem_V : y₀ ∈ V
  /-- The `n` holomorphic sheet sections. -/
  sheet : Fin n → Y → X
  /-- Each sheet is `C^ω` on `V`. -/
  sheet_smooth : ∀ i, ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (sheet i) V
  /-- Each sheet is a section of `f` on `V`: `f ∘ sheet i = id` on `V`. -/
  sheet_section : ∀ i, ∀ y ∈ V, f (sheet i y) = y
  /-- Each sheet is a *local two-sided* inverse: `sheet i ∘ f = id` near `sheet i y`.
  (True of genuine covering sections, which are local homeomorphisms.) -/
  sheet_leftInv : ∀ i, ∀ y ∈ V, (sheet i ∘ f) =ᶠ[𝓝 (sheet i y)] id
  /-- The sheets are everywhere distinct over `V` (different sheets, different points). -/
  sheet_inj : ∀ y ∈ V, Function.Injective (fun i => sheet i y)
  /-- The sheets sweep out the **entire** fibre over each `y ∈ V`. -/
  fibre_eq : ∀ y ∈ V, f ⁻¹' {y} = Set.range (fun i => sheet i y)

namespace LocalSheetSystem

variable {f : X → Y} {y₀ : Y} (S : LocalSheetSystem f y₀)

/-- Each sheet is `MDifferentiableAt` at every point of `V`. -/
theorem sheet_mdifferentiableAt (i : Fin S.n) {y : Y} (hy : y ∈ S.V) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (S.sheet i) y :=
  ((S.sheet_smooth i).contMDiffAt (S.isOpen_V.mem_nhds hy)).mdifferentiableAt (by decide)

/-- **Per-sheet value identity.** On `V`, the retyped fibre summand at the sheet
point `sheet i y` equals `sheetPullback α (sheet i) y`. -/
theorem traceSummandAt_sheet_eq {f : X → Y} {y₀ : Y} (S : LocalSheetSystem f y₀)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (α : HolomorphicOneForms X) (i : Fin S.n) {y : Y} (hy : y ∈ S.V) :
    traceSummandAt f α y (S.sheet i y) = sheetPullback α (S.sheet i) y := by
  have hfsy : f (S.sheet i y) = y := S.sheet_section i y hy
  have hf_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (S.sheet i y) :=
    hf.mdifferentiableAt (by decide)
  have hg_diff : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (S.sheet i) (f (S.sheet i y)) := by
    rw [hfsy]; exact S.sheet_mdifferentiableAt i hy
  have hfs : (f ∘ S.sheet i) =ᶠ[𝓝 (f (S.sheet i y))] id := by
    rw [hfsy]
    filter_upwards [S.isOpen_V.mem_nhds hy] with y' hy'
    show f (S.sheet i y') = y'; exact S.sheet_section i y' hy'
  have hsf : (S.sheet i ∘ f) =ᶠ[𝓝 (S.sheet i y)] id := S.sheet_leftInv i y hy
  have hgfx : S.sheet i (f (S.sheet i y)) = S.sheet i y := by rw [hfsy]
  have hval := traceSummand_eq_sheetPullback (f := f) (g := S.sheet i)
    (x₀ := S.sheet i y) α hgfx hf_diff hg_diff hfs hsf
  -- `traceSummandAt f α y (sheet i y)` is just `traceSummand f α (sheet i y)` (no
  -- transport now that summands live in the model fibre `ℂ →L ℂ`).
  rw [traceSummandAt, hval, hfsy]

/-- **Local representation of the trace (off-branch core).** Over the base
neighborhood `V`, the fibre-sum trace is the finite sum of the per-sheet pullbacks:
`traceFun f α y = ∑ᵢ sheetPullback α (sheet i) y`. The fibre `f⁻¹{y}` is the range
of the injective sheet map (`fibre_eq` + `sheet_inj`), so the `finsum` over the
fibre collapses to the finite sum over the `n` sheets (`finsum_mem_range`), each
term identified by `traceSummandAt_sheet_eq`. -/
theorem traceFun_eq_sum_sheetPullback {f : X → Y} {y₀ : Y} (S : LocalSheetSystem f y₀)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (α : HolomorphicOneForms X) {y : Y} (hy : y ∈ S.V) :
    traceFun f α y = ∑ i, sheetPullback α (S.sheet i) y := by
  rw [traceFun, S.fibre_eq y hy,
    finsum_mem_range (S.sheet_inj y hy), finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun i _ => S.traceSummandAt_sheet_eq hf α i hy

/-- **Off-branch holomorphicity.** Given a local sheet system at `y₀`,
the trace section `y ↦ traceFun f α y` is `ContMDiffAt` (analytic) at `y₀` — i.e.
the fibre-sum trace is a holomorphic one-form near `y₀`. Reduces, via the local
representation `traceFun = ∑ᵢ sheetPullback (sheet i)` on `V`, to the per-sheet
smoothness `contMDiffAt_sheetPullback` summed over the (finitely many) sheets
(`ContMDiffAt.sum_section`). -/
theorem contMDiffAt_traceFun {f : X → Y} {y₀ : Y} (S : LocalSheetSystem f y₀)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (α : HolomorphicOneForms X) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk'
        (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
        (traceFun f α y)) y₀ := by
  -- On `V` (a neighborhood of `y₀`), `traceFun = ∑ᵢ sheetPullback (sheet i)`.
  have hrep : (fun y : Y => Bundle.TotalSpace.mk'
      (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
      (traceFun f α y)) =ᶠ[𝓝 y₀]
      (fun y : Y => Bundle.TotalSpace.mk'
        (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
        (∑ i, sheetPullback α (S.sheet i) y)) := by
    filter_upwards [S.isOpen_V.mem_nhds S.mem_V] with y hy
    rw [S.traceFun_eq_sum_sheetPullback hf α hy]
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hrep
  -- Finite sum of per-sheet pullback sections, each `ContMDiffAt` at `y₀ ∈ V`.
  refine ContMDiffAt.sum_section (fun i _ => ?_)
  exact contMDiffAt_sheetPullback α
    ((S.sheet_smooth i).contMDiffAt (S.isOpen_V.mem_nhds S.mem_V))

end LocalSheetSystem

/-! ### Linearity of the fibre-sum trace (off the branch locus)

The fibre sum is ℂ-linear in the form. Over a finite fibre this is termwise
linearity of `traceSummand` plus additivity/homogeneity of `finsum` over a finite
set. (At a branch point the naive `finsum` is `0`; the genuine trace there is the
removable-singularity extension, handled in the assembly below.) -/

/-- Additivity of the fibre-sum trace off the branch locus. -/
theorem traceFun_add_of_notMem_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α β : HolomorphicOneForms X)
    {y : Y} (hy : y ∉ branchLocus f) :
    traceFun f (α + β) y = traceFun f α y + traceFun f β y := by
  have hfin : (f ⁻¹' {y}).Finite := fiber_finite_off_branchLocus f hf hnonconst hy
  unfold traceFun
  simp only [traceSummandAt, traceSummand_add f α β]
  rw [finsum_mem_add_distrib hfin]

/-- ℂ-homogeneity of the fibre-sum trace off the branch locus. -/
theorem traceFun_smul_of_notMem_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (c : ℂ) (α : HolomorphicOneForms X)
    {y : Y} (hy : y ∉ branchLocus f) :
    traceFun f (c • α) y = c • traceFun f α y := by
  have hfin : (f ⁻¹' {y}).Finite := fiber_finite_off_branchLocus f hf hnonconst hy
  unfold traceFun
  simp only [traceSummandAt, traceSummand_smul f c α]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.smul_sum]

/-! ### Existence of the local sheet system (covering unpacking) -/

/-- **[PROVEN]** Off the branch locus a local sheet system exists (Forster §4.22).

Construction (no covering trivialization needed — assembled directly from the proven
local pieces): the fibre `f⁻¹{y₀}` is finite (`fiber_finite_off_branchLocus`),
enumerated as `pt : Fin n → X` via `Fintype.equivFin`. The `pt i` are pairwise
distinct points off `criticalSet`, separated by pairwise-disjoint opens `Sep i`
(`X` is T2, `Set.Finite.t2_separation`). At each `pt i`, `exists_twoSided_localInverse`
gives a `C^ω` two-sided section `g i` on an open `Vsec i ∋ y₀`
(supplying `sheet_smooth`, `sheet_section`, and the `sheet_leftInv` content), and
`isLocalHomeoOffCritical` gives an open injective neighborhood, shrunk into `Sep i`
to make the sheets disjoint. Properness (`properNbhd` of `isProperMap_of_contMDiff`)
shrinks the fibre's open cover `⋃ Uinj` to a base `Ubase ∋ y₀` with `f⁻¹ Ubase ⊆ ⋃ Uinj`.
Over `V := Ubase ∩ ⋂ i (Vsec i ∩ g i⁻¹ (Uinj i))` every preimage of `y ∈ V` lands in
some `Uinj j`, where `g j y` is its unique preimage — giving `fibre_eq`; the disjoint
`Sep i` give `sheet_inj`. With this, `contMDiffAt_traceFun_of_notMem_branchLocus`
(off-branch holomorphicity of the trace) is **unconditional**. -/
theorem exists_localSheetSystem (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) {y₀ : Y} (hy₀ : y₀ ∉ branchLocus f) :
    Nonempty (LocalSheetSystem f y₀) := by
  classical
  -- The fibre over `y₀` is finite; enumerate it as `Fin n`.
  have hfin : (f ⁻¹' {y₀}).Finite := fiber_finite_off_branchLocus f hf hnonconst hy₀
  let _ffib : Fintype (f ⁻¹' {y₀}) := hfin.fintype
  set n : ℕ := Fintype.card (f ⁻¹' {y₀}) with hn_def
  set e : (f ⁻¹' {y₀}) ≃ Fin n := Fintype.equivFin _ with he_def
  -- The `i`-th fibre point, as a term of `X`.
  set pt : Fin n → X := fun i => (e.symm i : X) with hpt_def
  have hpt_fib : ∀ i, f (pt i) = y₀ := fun i => (e.symm i).2
  have hpt_crit : ∀ i, pt i ∉ criticalSet f := fun i hmem =>
    hy₀ ⟨pt i, hmem, hpt_fib i⟩
  have hpt_inj : Function.Injective pt := fun i j hij => by
    have : e.symm i = e.symm j := Subtype.ext hij
    exact e.symm.injective this
  -- Separate the finitely many distinct fibre points by pairwise-disjoint open
  -- neighborhoods (`X` is T2). `Sep i ∋ pt i`, open, and disjoint for distinct
  -- `pt i`. This makes the sheets provably distinct over the base (sheet `i`
  -- lands in `Sep i`, sheet `j` in the disjoint `Sep j`).
  obtain ⟨Sep₀, hSep₀_mem, hSep₀_disj⟩ :
      ∃ U : X → Set X, (∀ x, x ∈ U x ∧ IsOpen (U x)) ∧ (Set.range pt).PairwiseDisjoint U :=
    (Set.finite_range pt).t2_separation
  set Sep : Fin n → Set X := fun i => Sep₀ (pt i) with hSep_def
  have hSep_mem : ∀ i, pt i ∈ Sep i := fun i => (hSep₀_mem (pt i)).1
  have hSep_open : ∀ i, IsOpen (Sep i) := fun i => (hSep₀_mem (pt i)).2
  have hSep_disj : ∀ i j, i ≠ j → Disjoint (Sep i) (Sep j) := fun i j hij =>
    hSep₀_disj (Set.mem_range_self i) (Set.mem_range_self j)
      (fun h => hij (hpt_inj h))
  -- For each fibre point, a `C^ω` two-sided local section `g i` on an open
  -- `Vsec i ∋ y₀` (with `g i y₀ = pt i`, `f ∘ g i = id` on `Vsec i`,
  -- `g i ∘ f = id` near `pt i`) together with an open injective neighborhood
  -- `Uinj i ∋ pt i` of `pt i` in `X` (`isLocalHomeoOffCritical`), shrunk into
  -- the separating window `Sep i` so the sheets are pairwise disjoint.
  have hpkg : ∀ i : Fin n, ∃ (g : Y → X) (Vsec : Set Y) (Uinj : Set X),
      IsOpen Vsec ∧ y₀ ∈ Vsec ∧ g y₀ = pt i ∧
        (∀ y ∈ Vsec, f (g y) = y) ∧ ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω g Vsec ∧
        ((g ∘ f) =ᶠ[𝓝 (pt i)] id) ∧
        IsOpen Uinj ∧ pt i ∈ Uinj ∧ Set.InjOn f Uinj ∧ Uinj ⊆ Sep i := by
    intro i
    obtain ⟨g, Vsec, hVo, hfxV, hgfx, hsec, hgsm, hgf⟩ :=
      exists_twoSided_localInverse f hf hnonconst (hpt_crit i)
    obtain ⟨Uinj, hUo, hxU, hinj, -⟩ := isLocalHomeoOffCritical f hf hnonconst (hpt_crit i)
    -- `exists_twoSided_localInverse` lives over `f (pt i) = y₀`; rewrite to `y₀`.
    rw [hpt_fib i] at hfxV hgfx
    -- Intersect the injective neighborhood with the separating window `Sep i`.
    refine ⟨g, Vsec, Uinj ∩ Sep i, hVo, hfxV, hgfx, hsec, hgsm, hgf,
      hUo.inter (hSep_open i), ⟨hxU, hSep_mem i⟩, hinj.mono Set.inter_subset_left,
      Set.inter_subset_right⟩
  choose g Vsec Uinj hVo hy₀V hgfx hsec hgsm hgf hUo hxU hinj hUsep using hpkg
  -- The fibre `f⁻¹{y₀} = pt '' univ` is contained in the open `⋃ⱼ Uinj j`.
  set Ubig : Set X := ⋃ j, Uinj j with hUbig_def
  have hUbig_open : IsOpen Ubig := isOpen_iUnion hUo
  have hfib_sub : f ⁻¹' {y₀} ⊆ Ubig := by
    intro x hx
    have hxfib : x ∈ f ⁻¹' {y₀} := hx
    -- `x` is the `e`-image of itself; it equals `pt (e ⟨x, _⟩)`.
    set j : Fin n := e ⟨x, hxfib⟩ with hj_def
    have hpt_eq : pt j = x := by simp only [hpt_def, hj_def, Equiv.symm_apply_apply]
    exact Set.mem_iUnion.mpr ⟨j, hpt_eq ▸ hxU j⟩
  -- Properness: shrink to an open base `Ubase ∋ y₀` with `f⁻¹ Ubase ⊆ Ubig`.
  obtain ⟨Ubase, hUbase_open, hy₀Ubase, hUbase_sub⟩ :=
    properNbhd (isProperMap_of_contMDiff f hf) y₀ hUbig_open hfib_sub
  -- Each `Wsheet i := Vsec i ∩ (g i)⁻¹ (Uinj i)` is open (continuity of the
  -- section on its open domain) and contains `y₀` (`g i y₀ = pt i ∈ Uinj i`).
  set Wsheet : Fin n → Set Y := fun i => Vsec i ∩ g i ⁻¹' Uinj i with hWsheet_def
  have hWsheet_open : ∀ i, IsOpen (Wsheet i) := fun i =>
    (hgsm i).continuousOn.isOpen_inter_preimage (hVo i) (hUo i)
  have hy₀Wsheet : ∀ i, y₀ ∈ Wsheet i := fun i =>
    ⟨hy₀V i, by rw [Set.mem_preimage, hgfx i]; exact hxU i⟩
  -- The base neighborhood: properness ∩ all sheet windows.
  set V : Set Y := Ubase ∩ ⋂ i, Wsheet i with hV_def
  have hV_open : IsOpen V :=
    hUbase_open.inter (isOpen_iInter_of_finite (fun i => hWsheet_open i))
  have hy₀V_mem : y₀ ∈ V := ⟨hy₀Ubase, Set.mem_iInter.mpr hy₀Wsheet⟩
  have hV_sub_Ubase : ∀ {y}, y ∈ V → y ∈ Ubase := fun {_} hy => hy.1
  have hV_sub_Wsheet : ∀ i {y}, y ∈ V → y ∈ Wsheet i :=
    fun i {_} hy => (Set.mem_iInter.mp hy.2) i
  have hV_sub_Vsec : ∀ i {y}, y ∈ V → y ∈ Vsec i := fun i {_} hy => (hV_sub_Wsheet i hy).1
  have hVsub_Vsec : ∀ i, V ⊆ Vsec i := fun i _ hy => (hV_sub_Wsheet i hy).1
  -- `f (g i y) = y` for `y ∈ V` (section on `V ⊆ Vsec i`).
  have hsec_V : ∀ i, ∀ y ∈ V, f (g i y) = y := fun i y hy =>
    hsec i y (hV_sub_Vsec i hy)
  -- `g i y ∈ Uinj i` for `y ∈ V` (from the `g i ⁻¹ Uinj i` window).
  have hgmem_V : ∀ i, ∀ y ∈ V, g i y ∈ Uinj i := fun i y hy =>
    (hV_sub_Wsheet i hy).2
  refine ⟨{
    n := n
    V := V
    isOpen_V := hV_open
    mem_V := hy₀V_mem
    sheet := g
    sheet_smooth := fun i => (hgsm i).mono (hVsub_Vsec i)
    sheet_section := hsec_V
    sheet_leftInv := ?_
    sheet_inj := ?_
    fibre_eq := ?_ }⟩
  · -- `sheet_leftInv`: `g i ∘ f = id` near `g i y` for `y ∈ V`.
    -- The two-sided inverse gives this near `pt i = g i y₀`. For general `y ∈ V`,
    -- `g i y ∈ Uinj i` where `f` is injective, and `g i ∘ f = id` near it follows
    -- from the section identity + injectivity, via the same argument as
    -- `exists_twoSided_localInverse`.
    intro i y hy
    -- `g i` is continuous at `y` (open domain `Vsec i ⊇ V ∋ y`).
    have hgi_contAt : ContinuousAt (g i) y :=
      (hgsm i).continuousOn.continuousAt ((hVo i).mem_nhds (hV_sub_Vsec i hy))
    -- Near `g i y`, points land in `Uinj i`.
    have hpre_U : ∀ᶠ x in 𝓝 (g i y), x ∈ Uinj i :=
      (hUo i).eventually_mem (hgmem_V i y hy)
    -- `f` is continuous at `g i y`.
    have hf_contAt : ContinuousAt f (g i y) := hf.continuous.continuousAt
    -- Near `g i y`: `f x ∈ V` (since `f (g i y) = y ∈ V`, `V` open).
    have hfx_V : ∀ᶠ x in 𝓝 (g i y), f x ∈ V :=
      hf_contAt.eventually_mem (by rw [hsec_V i y hy]; exact hV_open.mem_nhds hy)
    -- Near `g i y`: `g i (f x) ∈ Uinj i`.
    have hgfx_U : ∀ᶠ x in 𝓝 (g i y), g i (f x) ∈ Uinj i := by
      filter_upwards [hfx_V] with x hx
      exact hgmem_V i (f x) hx
    filter_upwards [hpre_U, hfx_V, hgfx_U] with x hxU' hxV' hgfxU'
    show g i (f x) = x
    -- `f (g i (f x)) = f x` (section at `f x ∈ V`); inject on `Uinj i`.
    exact hinj i hgfxU' hxU' (hsec_V i (f x) hxV')
  · -- `sheet_inj`: the sheets are distinct over `V`. For `y ∈ V`,
    -- `g i y ∈ Uinj i ⊆ Sep i` and `g j y ∈ Uinj j ⊆ Sep j`, and the `Sep`'s
    -- are pairwise disjoint for distinct indices — so equal sheet values force
    -- equal indices.
    intro y hy i j hij
    by_contra hne
    have hxSi : g i y ∈ Sep i := hUsep i (hgmem_V i y hy)
    have hxSj : g j y ∈ Sep j := hUsep j (hgmem_V j y hy)
    have hgij : g i y = g j y := hij
    -- `g i y = g j y` lies in `Sep i ∩ Sep j`, which is empty for `i ≠ j`.
    exact (hSep_disj i j hne).le_bot ⟨hxSi, hgij ▸ hxSj⟩
  · -- `fibre_eq`: the sheets exhaust the fibre over each `y ∈ V`.
    intro y hy
    apply Set.eq_of_subset_of_subset
    · -- `⊆`: any `x ∈ f⁻¹{y}` lies in some `Uinj j` (properness), and there
      -- `g j y` is the unique preimage of `y`, so `x = g j y`.
      intro x hx
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      -- `x ∈ f⁻¹ Ubase ⊆ Ubig = ⋃ Uinj`.
      have hxUbase : x ∈ f ⁻¹' Ubase := by
        rw [Set.mem_preimage, hx]; exact hV_sub_Ubase hy
      have hxUbig : x ∈ Ubig := hUbase_sub hxUbase
      obtain ⟨j, hxUj⟩ := Set.mem_iUnion.mp hxUbig
      -- `g j y ∈ Uinj j` and `f (g j y) = y = f x`; inject on `Uinj j`.
      have hgjy_U : g j y ∈ Uinj j := hgmem_V j y hy
      have hfgjy : f (g j y) = y := hsec_V j y hy
      have : x = g j y := hinj j hxUj hgjy_U (by rw [hx, hfgjy])
      exact Set.mem_range.mpr ⟨j, this.symm⟩
    · -- `⊇`: each `g i y` is in the fibre (`f (g i y) = y`).
      rintro x ⟨i, rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact hsec_V i y hy

/-- **Off-branch holomorphicity of the trace, top-level form.** For `y₀` off the
branch locus, the fibre-sum trace `y ↦ traceFun f α y` is `ContMDiffAt` (a
holomorphic one-form) at `y₀`. Combines `exists_localSheetSystem` (the isolated
covering step) with the fully-proven `LocalSheetSystem.contMDiffAt_traceFun`. -/
theorem contMDiffAt_traceFun_of_notMem_branchLocus (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (α : HolomorphicOneForms X) {y₀ : Y} (hy₀ : y₀ ∉ branchLocus f) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (fun y : Y => Bundle.TotalSpace.mk'
        (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
        (traceFun f α y)) y₀ := by
  obtain ⟨S⟩ := exists_localSheetSystem f hf hnonconst hy₀
  exact S.contMDiffAt_traceFun hf α

/-! ### The trace as a bundle section, and its canonical branch extension

We package the covector-valued trace as a map into the cotangent-bundle total space
(`traceTotalSpaceMk`) so we can speak of its `ContMDiff`ness directly, and we define the
*canonical extension* `traceFunExt` that overwrites the (wrong) `finsum = 0` value
at each branch point with the **removable-singularity limit** `limUnder (𝓝[≠] y₀)`.

Off the branch locus `traceFunExt = traceFun`; on a *punctured* neighborhood of a
branch point they also agree (the branch locus is finite, so a punctured nhd avoids
it). These two agreements are all the reduction lemma below needs. -/

/-- The trace, packaged as a map into the **total space** of the cotangent bundle of
`Y` (the shape consumed by `ContMDiffAt`/`ContMDiffSection`). `coeff` is the covector
to place in the fibre at `y` — either the raw fibre sum `traceFun f α y` or its branch
extension `traceFunExt f α y`. -/
noncomputable abbrev traceTotalSpaceMk (coeff : Y → (ℂ →L[ℂ] ℂ)) (y : Y) :
    Bundle.TotalSpace (ℂ →L[ℂ] ℂ)
      (fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) :=
  Bundle.TotalSpace.mk'
    (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) (ℂ →L[ℂ] ℂ) y
    (coeff y)

/-- **Canonical branch extension of the trace coefficient.** Equal to the fibre sum
`traceFun f α` off the branch locus, and to the removable-singularity limit
`limUnder (𝓝[≠] y) (traceFun f α)` at each branch point (where the naive `finsum` is
`0`). The membership test is decidable via `Classical.dec`. -/
noncomputable def traceFunExt (f : X → Y) (α : HolomorphicOneForms X) (y : Y) :
    ℂ →L[ℂ] ℂ := by
  classical
  exact if y ∈ branchLocus f then limUnder (𝓝[≠] y) (traceFun f α) else traceFun f α y

/-- Off the branch locus, the extension is the raw fibre sum. -/
theorem traceFunExt_of_notMem_branchLocus (f : X → Y) (α : HolomorphicOneForms X)
    {y : Y} (hy : y ∉ branchLocus f) :
    traceFunExt f α y = traceFun f α y := by
  classical
  rw [traceFunExt, if_neg hy]

/-- A punctured neighborhood of any point `y₀` **eventually avoids the branch locus**:
the branch locus is finite (hence `branchLocus f \ {y₀}` is closed), so its complement
is a neighborhood of `y₀`, and a point there which is also `≠ y₀` is off-branch. This is
the engine behind both the agreement lemma below and the linearity argument: on `𝓝[≠] y₀`
the trace is genuinely the off-branch fibre sum. -/
theorem eventually_notMem_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (y₀ : Y) :
    ∀ᶠ y in 𝓝[≠] y₀, y ∉ branchLocus f := by
  have hBfin : (branchLocus f).Finite := finite_branchLocus_of_nonconstant f hf hnonconst
  have hclosed : IsClosed (branchLocus f \ {y₀}) := hBfin.diff.isClosed
  have hnhd : (branchLocus f \ {y₀})ᶜ ∈ 𝓝 y₀ :=
    hclosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hnhd] with y hy_ne hy_notdiff
  rw [Set.mem_compl_iff, Set.mem_diff, not_and, not_not] at hy_notdiff
  exact fun hyB => hy_ne (hy_notdiff hyB)

/-- On the **punctured** neighborhood of any point `y₀`, the extension agrees with the
raw fibre sum: on `𝓝[≠] y₀` points are eventually off the branch locus
(`eventually_notMem_branchLocus`), where `traceFunExt = traceFun`. This is the bridge
turning a limit/continuity statement about `traceFun` into one about `traceFunExt`. -/
theorem traceFunExt_eventuallyEq_traceFun (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X) (y₀ : Y) :
    traceFunExt f α =ᶠ[𝓝[≠] y₀] traceFun f α := by
  filter_upwards [eventually_notMem_branchLocus f hf hnonconst y₀] with y hy_off
  exact traceFunExt_of_notMem_branchLocus f α hy_off

/-! ### Off-branch smoothness of the extended section

Off the branch locus the extension equals the raw fibre sum on a whole (open)
neighborhood, so off-branch `ContMDiffAt` of the *extended* section follows from the
unconditional off-branch `ContMDiffAt` of the raw fibre-sum section. -/

/-- The extended trace section is `ContMDiffAt` at every point **off** the branch
locus, unconditionally (no analytic hypothesis): the extension agrees with the raw
fibre sum on the open set `(branchLocus f)ᶜ`, where the fibre sum is holomorphic
(`contMDiffAt_traceFun_of_notMem_branchLocus`). -/
theorem contMDiffAt_traceSection_ext_of_notMem_branchLocus (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (α : HolomorphicOneForms X) {y₀ : Y} (hy₀ : y₀ ∉ branchLocus f) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (traceTotalSpaceMk (traceFunExt f α)) y₀ := by
  have hBclosed : IsClosed (branchLocus f) :=
    (finite_branchLocus_of_nonconstant f hf hnonconst).isClosed
  -- On the open complement of the branch locus, `traceFunExt = traceFun`.
  have heq : traceTotalSpaceMk (traceFunExt f α) =ᶠ[𝓝 y₀] traceTotalSpaceMk (traceFun f α) := by
    filter_upwards [hBclosed.isOpen_compl.mem_nhds hy₀] with y hy
    simp only [traceTotalSpaceMk, traceFunExt_of_notMem_branchLocus f α hy]
  exact (contMDiffAt_traceFun_of_notMem_branchLocus f hf hnonconst α hy₀).congr_of_eventuallyEq heq

/-- A connected complex 1-manifold has **no isolated points**: the punctured
neighborhood filter `𝓝[≠] y₀` is `NeBot`. (`Y` is `Infinite`
— `y_infinite_of_chartedSpace_complex` — hence `Nontrivial`; with `T1Space` +
`ConnectedSpace` this gives `PerfectSpace`, hence `NeBot (𝓝[≠] y₀)`.) This is what
makes limits along punctured neighborhoods unique, the engine of the linearity
argument below. -/
instance neBot_nhdsWithin_compl_self (y₀ : Y) : (𝓝[≠] y₀).NeBot := by
  haveI : Infinite Y := Jacobians.Discharge.ContMDiff.Degree.y_infinite_of_chartedSpace_complex
  infer_instance

/-! ### The reduction lemma (regluing + linearity), conditional on per-branch extension

The deliverable: a **fully-proven** reduction of `exists_traceForm` to one per-branch-point
analytic input. The input, `hext`, packages — for each form `α` and each branch point
`y₀` — the two facts that the (classically true) holomorphic extension supplies:

* `hsmooth`: the extended bundle section is `ContMDiffAt` at `y₀` (the *holomorphic*
  extension; from boundedness + Mathlib's removable singularity, then bundle regluing);
* `hcont`: the extension coefficient `traceFunExt f α : Y → (ℂ →L[ℂ] ℂ)` is `ContinuousAt`
  at `y₀` (the weaker *continuous* extension — the shadow of `hsmooth`).

Both are consequences of the single analytic crux (local boundedness of the trace near
a branch point, §1 of the assembly docstring); we keep them as the hypothesis so the
regluing **and** the full ℂ-linearity of `T` are proven here, unconditionally. -/

/-- **Reduction lemma for the trace.** Given the per-branch-point extension data `hext`
(holomorphic-extension smoothness + continuity at each branch point, for every form),
the trace `f₊ : Ω¹(X) →ₗ[ℂ] Ω¹(Y)` exists as a genuine holomorphic-one-form linear map
agreeing with the off-branch fibre sum `traceFun`.

Everything here is proven outright:
* **Section assembly**: `traceFunExt f α` is a global `ContMDiffSection` — off-branch from
  `contMDiffAt_traceSection_ext_of_notMem_branchLocus`, at branch points from `hext`.
* **Linearity**: at a branch point the extension value is the *unique* limit of `traceFun`
  along the punctured neighborhood (`neBot_nhdsWithin_compl_self` + `tendsto_nhds_unique`),
  and limits respect `+`/`•`; off-branch the fibre sum is already additive/homogeneous
  (`traceFun_add_of_notMem_branchLocus`, `traceFun_smul_of_notMem_branchLocus`). -/
theorem exists_traceForm_of_branchExtension (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (hext : ∀ (α : HolomorphicOneForms X) (y₀ : Y), y₀ ∈ branchLocus f →
      ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
          (traceTotalSpaceMk (traceFunExt f α)) y₀ ∧
        ContinuousAt (traceFunExt f α) y₀) :
    ∃ T : HolomorphicOneForms X →ₗ[ℂ] HolomorphicOneForms Y,
      ∀ (α : HolomorphicOneForms X) (y : Y), y ∉ branchLocus f →
        (T α).toFun y = traceFun f α y := by
  classical
  -- Global `ContMDiff` of the extended section, for each form.
  have hsmooth : ∀ α : HolomorphicOneForms X, ContMDiff 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (traceTotalSpaceMk (traceFunExt f α)) := by
    intro α y₀
    by_cases hy₀ : y₀ ∈ branchLocus f
    · exact (hext α y₀ hy₀).1
    · exact contMDiffAt_traceSection_ext_of_notMem_branchLocus f hf hnonconst α hy₀
  -- The underlying section assignment `α ↦ ⟨traceFunExt f α, …⟩`.
  set T₀ : HolomorphicOneForms X → HolomorphicOneForms Y :=
    fun α => ⟨traceFunExt f α, hsmooth α⟩ with hT₀_def
  -- `traceFunExt f α y` is the unique punctured-nhd limit of `traceFun f α` at a branch
  -- point: it is `ContinuousAt` (hence tends to its value along `𝓝[≠]`) and equals the
  -- raw fibre sum on the punctured neighborhood.
  have htendsto : ∀ (α : HolomorphicOneForms X) {y₀ : Y}, y₀ ∈ branchLocus f →
      Filter.Tendsto (traceFun f α) (𝓝[≠] y₀) (𝓝 (traceFunExt f α y₀)) := by
    intro α y₀ hy₀
    have hca : Filter.Tendsto (traceFunExt f α) (𝓝[≠] y₀) (𝓝 (traceFunExt f α y₀)) :=
      ((hext α y₀ hy₀).2.continuousWithinAt (s := {y₀}ᶜ))
    exact hca.congr' (traceFunExt_eventuallyEq_traceFun f hf hnonconst α y₀)
  -- Pointwise additivity of the extended coefficient (everywhere, incl. branch points).
  have hadd : ∀ (α β : HolomorphicOneForms X) (y : Y),
      traceFunExt f (α + β) y = traceFunExt f α y + traceFunExt f β y := by
    intro α β y
    by_cases hy : y ∈ branchLocus f
    · -- Unique-limit argument: both sides are limits of `traceFun … ` along `𝓝[≠] y`.
      refine tendsto_nhds_unique (htendsto (α + β) hy) ?_
      have hsum := (htendsto α hy).add (htendsto β hy)
      refine hsum.congr' ?_
      filter_upwards [eventually_notMem_branchLocus f hf hnonconst y] with z hz_off
      exact (traceFun_add_of_notMem_branchLocus f hf hnonconst α β hz_off).symm
    · rw [traceFunExt_of_notMem_branchLocus f (α + β) hy,
        traceFunExt_of_notMem_branchLocus f α hy, traceFunExt_of_notMem_branchLocus f β hy,
        traceFun_add_of_notMem_branchLocus f hf hnonconst α β hy]
  -- Pointwise ℂ-homogeneity of the extended coefficient (everywhere, incl. branch points).
  have hsmul : ∀ (c : ℂ) (α : HolomorphicOneForms X) (y : Y),
      traceFunExt f (c • α) y = c • traceFunExt f α y := by
    intro c α y
    by_cases hy : y ∈ branchLocus f
    · refine tendsto_nhds_unique (htendsto (c • α) hy) ?_
      have hsm := (htendsto α hy).const_smul c
      refine hsm.congr' ?_
      filter_upwards [eventually_notMem_branchLocus f hf hnonconst y] with z hz_off
      exact (traceFun_smul_of_notMem_branchLocus f hf hnonconst c α hz_off).symm
    · rw [traceFunExt_of_notMem_branchLocus f (c • α) hy,
        traceFunExt_of_notMem_branchLocus f α hy,
        traceFun_smul_of_notMem_branchLocus f hf hnonconst c α hy]
  -- Assemble the linear map. `+`/`•` of sections are pointwise (`coe_add`, `coe_smul`),
  -- so the section identities follow termwise from `hadd`/`hsmul`.
  refine ⟨{
    toFun := T₀
    map_add' := fun α β => ?_
    map_smul' := fun c α => ?_ }, ?_⟩
  · refine ContMDiffSection.ext (fun y => ?_)
    show traceFunExt f (α + β) y = (T₀ α + T₀ β).toFun y
    rw [hadd α β y]; rfl
  · refine ContMDiffSection.ext (fun y => ?_)
    show traceFunExt f (c • α) y = (c • T₀ α).toFun y
    rw [hsmul c α y]; rfl
  · -- Off-branch the section is the raw fibre sum, by construction of `traceFunExt`.
    intro α y hy
    show traceFunExt f α y = traceFun f α y
    exact traceFunExt_of_notMem_branchLocus f α hy

/-! ## Assembling into `HolomorphicOneForms Y` via branch extension

The off-branch fibre sum `traceFun f α` is now an **unconditional** holomorphic
one-form on `Y ∖ branchLocus f`: `contMDiffAt_traceFun_of_notMem_branchLocus`
depends only on `exists_localSheetSystem` (closed above) and the proven
`LocalSheetSystem.contMDiffAt_traceFun`. To upgrade it to a *global* element of
`HolomorphicOneForms Y` we must extend across the finite `branchLocus f`
(`finite_branchLocus_of_nonconstant`). The extended value at a branch point is the
removable-singularity **limit**, *not* the naive `finsum` (which is `0` there, since
the fibre over a branch point is still finite but the per-sheet derivatives blow up).
The global section's `toFun` is therefore the *extension*, characterized only by
agreeing with `traceFun` off the branch locus — we must not assert global smoothness
of `traceFun` itself, which is false at branch points.

### State of the assembly: framework PROVEN, one analytic fact ISOLATED

The regluing **and** the full ℂ-linearity are now proven outright in
`exists_traceForm_of_branchExtension` (above), which reduces `exists_traceForm` to a
single per-branch-point input `hext`. So the whole bundle/linearity scaffolding is
done and reusable; what remains is exactly that input, isolated below as
`traceExtendsAt_branchPoint` — the genuine analytic frontier.

`HolomorphicOneForms Y = ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω _`, so the extended
section `traceFunExt f α` must carry a *global* `ContMDiff` proof — including at branch
points. The per-branch-point input has two halves, **both consequences of the single
analytic crux** (local boundedness of the trace near a branch point):

1. **[GENUINE ANALYTIC CRUX — not in Mathlib, not in `Discharge/`]** *Local
   boundedness of the trace near each branch point.* In a chart at a branch point
   `y₀`, the coefficient `z ↦ traceFun f α (chart⁻¹ z)` is holomorphic on the punctured
   disk and **bounded** as `z → 0`. The classical reason: near `y₀` the cover has local
   normal form `w ↦ wᵉ` on each ramified sheet (`Discharge/Manifold/LocalNormalForm.lean`
   `MMeromorphicAt.exists_local_normal_form` gives the `wᵉ` model for the *map*), and
   the symmetric sum over the `e` colliding sheets of the per-sheet pullback
   `(α (sheetᵢ z)) ∘ (mfderiv sheetᵢ z)` cancels the `wᵉ⁻¹`-type blow-up via roots-of-
   unity orthogonality `∑ₖ ζ^{k(n+1)} = e·[e ∣ n+1]` (a Puiseux / Newton-symmetric-
   function computation). No project lemma currently supplies this; it is the analytic
   heart of the trace's well-definedness.

2. **Removable singularity + bundle regluing.** Given (1), Mathlib closes the chart
   step — `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` (or
   `differentiableOn_update_limUnder_of_bddAbove`, file
   `Mathlib/Analysis/Complex/RemovableSingularity.lean`) — yielding *both* the
   continuity (`ContinuousAt (traceFunExt f α)`) and, after lifting the chart-level
   analyticity back through `contMDiffAt_hom_bundle`, the section `ContMDiffAt`. These
   are precisely the two conjuncts of `hext`.

Sound (classically true; Forster §10, Griffiths–Harris Ch. 2 §2.7). References:
Forster §4.22–4.25 (local normal form `wᵉ`), §10 (the trace). -/

/-! ### Bridge from chart-coefficient boundedness to the branch-point extension

The trace's branch-point extension `traceExtendsAt_branchPoint` is the *only* genuinely
analytic step of the whole trace construction. We discharge it here **modulo a single
clean local-boundedness input** (`traceLocalCoeff_bddAbove`, the analytic crux): the
*local coefficient* of the trace, read in the fixed chart at `y₀`, is bounded on a
punctured disk. From boundedness everything else is Mathlib's removable singularity
theorem plus the bundle-coordinate plumbing developed below.

The right scalar to control is **not** the discontinuous "global coefficient"
`(traceFun f α y) 1` (the value of the covector on the chart-`∂/∂z` *at the varying point
`y`*; discontinuous when the tangent bundle is non-trivial, exactly the obstruction
isolated in `CotangentCoeff.lean`), but the **local coefficient**

> `traceLocalCoeff f α y₀ y := inCoordinates … y₀ y y₀ y (traceFun f α y) (1 : ℂ)`,

the coordinate of the trace section in the *fixed `y₀`-trivialization*. This is the
object whose continuity/smoothness `Mathlib.contMDiffAt_hom_bundle` (`contMDiffAt_section`)
governs, and which `continuousAt_inCoordinates` (in `CotangentCoeff.lean`) already shows is
continuous wherever the section is smooth. -/

/-- **Local coefficient of the trace.** The coordinate of the (extended) trace section
`traceFunExt f α` read in the *fixed* hom-bundle trivialization at `y₀`, evaluated on the
model basis vector `1 : ℂ`. Concretely `inCoordinates … y₀ y y₀ y (coeff y) (1 : ℂ) : ℂ`.
This is the continuous/holomorphic object (unlike the raw `(coeff y) 1`); the trace
section is `ContMDiffAt`/`ContinuousAt` at `y₀` **iff** this scalar is, by
`contMDiffAt_hom_bundle`. We define it for an arbitrary coefficient so it can be applied to
both `traceFun` and `traceFunExt`. -/
noncomputable def traceLocalCoeff (coeff : Y → (ℂ →L[ℂ] ℂ)) (y₀ y : Y) : ℂ :=
  ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
    y₀ y y₀ y (coeff y) (1 : ℂ)

/-- A `ℂ →L[ℂ] ℂ` operator is its value-at-`1` times the identity: `φ = (φ 1) • id`. The
elementary fact underlying the reconstruction of an operator-valued chart coordinate from
its scalar coordinate. -/
theorem clm_eq_apply_one_smul_id (φ : ℂ →L[ℂ] ℂ) :
    φ = (φ (1 : ℂ)) • ContinuousLinearMap.id ℂ ℂ := by
  apply ContinuousLinearMap.ext_ring
  simp

/-- **Section lift from the local coefficient (the converse of `continuousAt_inCoordinates`).**
If the scalar local coefficient `y ↦ traceLocalCoeff coeff y₀ y` is `ContMDiffAt` at `y₀`,
then the section `traceTotalSpaceMk coeff` is `ContMDiffAt` at `y₀`. This is the bundle-
coordinate engine: by `contMDiffAt_hom_bundle` the section is smooth iff its `inCoordinates`
operator is smooth into the fixed normed space `ℂ →L[ℂ] ℂ`; that operator equals
`(traceLocalCoeff coeff y₀ y) • id` (`clm_eq_apply_one_smul_id`), a scalar multiple of a
constant operator, hence smooth from the scalar's smoothness. -/
theorem contMDiffAt_traceTotalSpaceMk_of_localCoeff (coeff : Y → (ℂ →L[ℂ] ℂ)) {y₀ : Y}
    (hcoeff : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω (fun y => traceLocalCoeff coeff y₀ y) y₀) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω (traceTotalSpaceMk coeff) y₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  -- The `inCoordinates` operator equals `(scalar) • id`.
  have hsmul : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ω
      (fun y => (traceLocalCoeff coeff y₀ y) • ContinuousLinearMap.id ℂ ℂ) y₀ :=
    hcoeff.smul contMDiffAt_const
  refine hsmul.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => ?_))
  show ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℂ) (M := Y)) ℂ (Bundle.Trivial Y ℂ)
      y₀ y y₀ y (coeff y) = traceLocalCoeff coeff y₀ y • ContinuousLinearMap.id ℂ ℂ
  exact clm_eq_apply_one_smul_id _

/-- **Off-branch smoothness of the local coefficient.** Wherever `y₁` is off the branch
locus *and* lies in the fixed chart source at `y₀`, the scalar local coefficient
`y ↦ traceLocalCoeff (traceFun f α) y₀ y` is `ContMDiffAt` at `y₁`. Derived from the
off-branch section smoothness `contMDiffAt_traceFun_of_notMem_branchLocus` read in the
*fixed `y₀`-trivialization* (`contMDiffAt_section_iff` with the hom-bundle trivialization at
`y₀`, whose coordinate is exactly `inCoordinates … y₀ · y₀ ·` by `hom_trivializationAt_apply`),
then evaluated on the model basis vector `1`. -/
theorem contMDiffAt_traceLocalCoeff_of_notMem_branchLocus (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (α : HolomorphicOneForms X) (y₀ : Y) {y₁ : Y} (hy₁ : y₁ ∉ branchLocus f)
    (hy₁src : y₁ ∈ (chartAt ℂ y₀).source) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω (fun y => traceLocalCoeff (traceFun f α) y₀ y) y₁ := by
  -- The trace section is `ContMDiffAt` at `y₁` (off branch).
  have hsec : ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
      (traceTotalSpaceMk (traceFun f α)) y₁ :=
    contMDiffAt_traceFun_of_notMem_branchLocus f hf hnonconst α hy₁
  -- Read it in the FIXED hom-bundle trivialization at `y₀`. Its base set is the tangent
  -- trivialization base set at `y₀` (∩ the trivial-bundle base set `univ`), i.e. the chart
  -- source at `y₀`, which contains `y₁`.
  have hy₁base : y₁ ∈ (trivializationAt (ℂ →L[ℂ] ℂ)
      (fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) y₀).baseSet := by
    rw [hom_trivializationAt_baseSet]
    refine ⟨?_, Set.mem_univ _⟩
    rw [TangentBundle.trivializationAt_baseSet]
    exact hy₁src
  have hcoord := ((trivializationAt (ℂ →L[ℂ] ℂ)
      (fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y) y₀).contMDiffAt_section_iff
      (E := fun y : Y => TangentSpace 𝓘(ℂ) y →L[ℂ] (Bundle.Trivial Y ℂ) y)
      (s := fun y => traceFun f α y) hy₁base).mp hsec
  -- `(ehom ⟨y, traceFun f α y⟩).2 = inCoordinates … y₀ y y₀ y (traceFun f α y)` (defeq), an
  -- operator-valued `ContMDiffAt`; apply at `1` to get the scalar local coefficient.
  exact hcoord.clm_apply contMDiffAt_const

/-! ### Scalar manifold ↔ chart bridges (for maps `Y → ℂ`)

A scalar map `g : Y → ℂ` is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ,ℂ) ω` at `y₀` exactly when its chart
pullback `g ∘ (chartAt ℂ y₀).symm` is `AnalyticAt` at `(chartAt ℂ y₀) y₀` (target chart on
the model space `ℂ` is the identity). We package the two directions needed for the
removable-singularity bridge. -/

/-- **Manifold smoothness ⟹ chart-pullback differentiability (scalar codomain).** If
`g : Y → ℂ` is `ContMDiffAt … ω` at `y₁`, its chart pullback `g ∘ (chartAt ℂ y₀).symm` is
`DifferentiableAt ℂ` at `(chartAt ℂ y₀) y₁`, provided `y₁` lies in the chart source. The
chart inverse `(chartAt ℂ y₀).symm : ℂ → Y` is `ContMDiffAt` at `(chartAt ℂ y₀) y₁`
(`contMDiffOn_chart_symm`, since `(chartAt ℂ y₀) y₁ ∈ target`) and maps it to `y₁`, so the
composite `g ∘ (chartAt ℂ y₀).symm : ℂ → ℂ` is `ContMDiffAt`, i.e. `DifferentiableAt`. -/
theorem differentiableAt_chartPullback_of_contMDiffAt {g : Y → ℂ} {y₀ y₁ : Y}
    (hg : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω g y₁) (hy₁ : y₁ ∈ (chartAt ℂ y₀).source) :
    DifferentiableAt ℂ (g ∘ (chartAt ℂ y₀).symm) ((chartAt ℂ y₀) y₁) := by
  have hmem : (chartAt ℂ y₀) y₁ ∈ (chartAt ℂ y₀).target :=
    (chartAt ℂ y₀).map_source hy₁
  -- chart inverse is `ContMDiffAt` at the chart image, landing at `y₁`.
  have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ y₀).symm ((chartAt ℂ y₀) y₁) :=
    (contMDiffOn_chart_symm (I := 𝓘(ℂ)) (x := y₀) ((chartAt ℂ y₀) y₁) hmem).contMDiffAt
      ((chartAt ℂ y₀).open_target.mem_nhds hmem)
  have hsymm_eq : (chartAt ℂ y₀).symm ((chartAt ℂ y₀) y₁) = y₁ :=
    (chartAt ℂ y₀).left_inv hy₁
  have hg' : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω g ((chartAt ℂ y₀).symm ((chartAt ℂ y₀) y₁)) := by
    rw [hsymm_eq]; exact hg
  -- composite `g ∘ chart.symm : ℂ → ℂ`, smooth at the chart image, hence differentiable.
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω (g ∘ (chartAt ℂ y₀).symm) ((chartAt ℂ y₀) y₁) :=
    hg'.comp ((chartAt ℂ y₀) y₁) hsymm
  exact (contMDiffAt_iff_contDiffAt.mp hcomp).differentiableAt (by simp)

/-- **Chart-pullback analyticity ⟹ manifold smoothness (scalar codomain).** Converse of
`differentiableAt_chartPullback_of_contMDiffAt` at the basepoint: if `g : Y → ℂ` is
`ContinuousAt` at `y₀` and its chart pullback `g ∘ (chartAt ℂ y₀).symm` is `AnalyticAt ℂ` at
`(chartAt ℂ y₀) y₀`, then `g` is `ContMDiffAt … ω` at `y₀`. This is the `mpr` of
`contMDiffAt_iff` for a scalar target (the target chart is the identity, the source extended
chart is `chartAt ℂ y₀`), feeding the removably-extended analytic local coefficient back into
section smoothness. -/
theorem contMDiffAt_of_analyticAt_chartPullback {g : Y → ℂ} {y₀ : Y}
    (hcont : ContinuousAt g y₀)
    (han : AnalyticAt ℂ (g ∘ (chartAt ℂ y₀).symm) ((chartAt ℂ y₀) y₀)) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω g y₀ := by
  rw [contMDiffAt_iff]
  refine ⟨hcont, ?_⟩
  have hrange : range (𝓘(ℂ) : ModelWithCorners ℂ ℂ ℂ) = univ :=
    ModelWithCorners.Boundaryless.range_eq_univ
  rw [hrange, contDiffWithinAt_univ]
  -- Identify the extended-chart pullback with `g ∘ (chartAt ℂ y₀).symm` (target chart = id).
  have hfun : (extChartAt 𝓘(ℂ) (g y₀) ∘ g ∘ (extChartAt 𝓘(ℂ) y₀).symm)
      = (g ∘ (chartAt ℂ y₀).symm) := by
    funext z; simp [extChartAt_coe, extChartAt_coe_symm]
  have hbase : extChartAt 𝓘(ℂ) y₀ y₀ = (chartAt ℂ y₀) y₀ := by simp [extChartAt_coe]
  rw [hfun, hbase]
  exact han.contDiffAt

/-- **[ISOLATED ANALYTIC SORRY — the trace's local boundedness at a branch point]**

The single genuinely-analytic input: in the fixed chart `c := chartAt ℂ y₀`, the trace's
*local coefficient* `z ↦ traceLocalCoeff (traceFun f α) y₀ (c.symm z)` is **bounded** on a
punctured neighborhood of `c y₀` (in the chart codomain `ℂ`). Equivalently: the holomorphic
one-form `traceFun f α` on `Y ∖ branchLocus f` is *locally bounded* near the branch point
`y₀`, read in the `y₀`-chart.

This is the **only** fact the whole trace construction is missing. Its classical proof uses
the local normal form `w ↦ wᵉ` of the branched cover on each colliding sheet
(`Discharge/Manifold/LocalNormalForm.lean`) and the roots-of-unity cancellation of the
per-sheet `wᵉ⁻¹` blow-ups, `∑ₖ ζ^{k(n+1)} = e·[e ∣ n+1]` (a Puiseux / Newton-symmetric-
function computation absent from Mathlib and `Discharge/`). Holomorphy of this scalar on the
punctured disk is **not** assumed here — it is derived in `traceExtendsAt_branchPoint` from
the off-branch holomorphicity of the trace section. -/
theorem traceLocalCoeff_bddAbove (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X)
    {y₀ : Y} (hy₀ : y₀ ∈ branchLocus f) :
    BddAbove (norm ∘ (fun z : ℂ => traceLocalCoeff (traceFun f α) y₀ ((chartAt ℂ y₀).symm z)) ''
      (((chartAt ℂ y₀).target ∩ (chartAt ℂ y₀).symm ⁻¹' ((branchLocus f)ᶜ)) \ {(chartAt ℂ y₀) y₀})) :=
  sorry

/-- **[ISOLATED SECONDARY SORRY — the `traceFunExt`-branch-value is in the correct frame; a
`traceFunExt`-DESIGN gap, NOT a consequence of boundedness]**

Two facts asserting that the branch-point value `traceFunExt f α y₀` (defined as the raw
operator limit `limUnder (𝓝[≠] y₀) (traceFun f α)`) is the *geometrically correct* extension:

1. **Raw convergence** — `traceFun f α y → traceFunExt f α y₀` along `𝓝[≠] y₀` (so the raw
   `limUnder` actually converges, giving conjunct 2's continuity).
2. **Local-coefficient matching** — the local coefficient of the extended trace at `y₀`,
   `traceLocalCoeff (traceFunExt f α) y₀ y₀`, equals the removable-singularity limit of the
   chart-pulled-back local coefficient of the *raw* trace (giving conjunct 1's analytic match
   at the puncture).

**Why this is isolated separately from the boundedness crux.** The local-boundedness input
`traceLocalCoeff_bddAbove` controls the *local coefficient* — the trace read in the **fixed
`y₀`-trivialization** — the genuinely continuous/holomorphic object, which suffices for the
*section*'s smoothness off `y₀` and for its removable extension. But the section's value AT
`y₀` is fixed by `traceFunExt f α y₀`, which the current design takes to be the **raw**
operator `limUnder`. The raw operator `traceFun f α y` is read in the *varying chart at `y`*:
it equals `inCoordinates(traceFun f α y) ∘ clmAt(tangentTriv y₀) y`, whose second factor (the
chart-transition derivative) is *discontinuous* in `y` for a non-trivial tangent bundle
(genus ≥ 2; the obstruction isolated in `CotangentCoeff.lean`,
`const_one_section_continuous_of_coordChange_fixes_one`). Hence the raw limit need not exist,
and even granting it, its frame does not match the local-coefficient extension's — neither
fact follows from boundedness.

This is a **design issue in `traceFunExt`** (consumed by `exists_traceForm_of_branchExtension`
via `htendsto`/`hext`): the branch value should be defined via the **local coefficient** (or
as the *bundle-limit* of the section), not the raw-operator `limUnder`. With that fix both
facts become provable from boundedness alone (the section converges in the bundle; its limit
value, read locally, is the analytic extension). As stated against the current raw-operator
`traceFunExt`, this is the precise residual gap. See the report and
`docs/trace_branchpoint_plan.md`. -/
theorem traceFunExt_branchValue_correct (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X)
    {y₀ : Y} (hy₀ : y₀ ∈ branchLocus f) :
    Filter.Tendsto (traceFun f α) (𝓝[≠] y₀) (𝓝 (traceFunExt f α y₀)) ∧
      traceLocalCoeff (traceFunExt f α) y₀ y₀ =
        limUnder (𝓝[≠] ((chartAt ℂ y₀) y₀))
          (fun z => traceLocalCoeff (traceFun f α) y₀ ((chartAt ℂ y₀).symm z)) :=
  sorry

/-- **[PROVEN MODULO the boundedness crux `traceLocalCoeff_bddAbove` and the raw-convergence
input `traceFun_tendsto_branchExtension`]**

For every form `α` and every branch point `y₀ ∈ branchLocus f`, the canonical branch
extension `traceFunExt f α` is, at `y₀`:
* `ContMDiffAt` as a section of the cotangent bundle (the *holomorphic* extension), and
* `ContinuousAt` as a coefficient `Y → (ℂ →L[ℂ] ℂ)` (the *continuous* extension).

**Bridge structure.**
* *Continuity (conjunct 2)* is the raw-convergence input `traceFun_tendsto_branchExtension`
  transported through `traceFunExt =ᶠ[𝓝[≠] y₀] traceFun`.
* *Section smoothness (conjunct 1)* is Mathlib's removable singularity theorem
  (`Complex.differentiableOn_update_limUnder_of_bddAbove`,
  `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`) applied to the
  *local coefficient* read in the `y₀`-chart: it is holomorphic off `y₀` (off-branch section
  smoothness, `contMDiffAt_traceLocalCoeff_of_notMem_branchLocus`, + the scalar chart bridges)
  and bounded there (the crux `traceLocalCoeff_bddAbove`), hence extends analytically; its
  value at `y₀` matches `traceLocalCoeff (traceFunExt f α) y₀ y₀` by the raw-convergence input.
  The analytic local coefficient is lifted back to the section via
  `contMDiffAt_traceTotalSpaceMk_of_localCoeff`.

Everything *downstream* — the global `ContMDiffSection` regluing and the full ℂ-linearity of
the trace — is proven unconditionally in `exists_traceForm_of_branchExtension`. -/
theorem traceExtendsAt_branchPoint (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X)
    {y₀ : Y} (hy₀ : y₀ ∈ branchLocus f) :
    ContMDiffAt 𝓘(ℂ) (𝓘(ℂ).prod 𝓘(ℂ, ℂ →L[ℂ] ℂ)) ω
        (traceTotalSpaceMk (traceFunExt f α)) y₀ ∧
      ContinuousAt (traceFunExt f α) y₀ := by
  classical
  set c := chartAt ℂ y₀ with hc_def
  -- Abbreviations for the local coefficient of the raw / extended trace, and its chart pullback.
  set Hraw : Y → ℂ := fun y => traceLocalCoeff (traceFun f α) y₀ y with hHraw
  set Hext : Y → ℂ := fun y => traceLocalCoeff (traceFunExt f α) y₀ y with hHext
  set G : ℂ → ℂ := fun z => Hraw (c.symm z) with hG
  set z₀ : ℂ := c y₀ with hz₀
  -- ============================ Conjunct 2: continuity (from the raw-convergence input) ====
  obtain ⟨hraw, hmatch⟩ := traceFunExt_branchValue_correct f hf hnonconst α hy₀
  have hcont : ContinuousAt (traceFunExt f α) y₀ := by
    have hEq : traceFunExt f α =ᶠ[𝓝[≠] y₀] traceFun f α :=
      traceFunExt_eventuallyEq_traceFun f hf hnonconst α y₀
    -- `traceFunExt` tends to its own value along the punctured nbhd; it is also constant-value
    -- continuous "at" `y₀` trivially, so it is `ContinuousAt`.
    have hwithin : Filter.Tendsto (traceFunExt f α) (𝓝[≠] y₀) (𝓝 (traceFunExt f α y₀)) :=
      hraw.congr' hEq.symm
    rw [← continuousWithinAt_compl_self]
    exact hwithin
  refine ⟨?_, hcont⟩
  -- ============================ Conjunct 1: section smoothness ==============================
  -- Reduce the section to its scalar local coefficient `Hext`, then to chart-pullback analyticity.
  apply contMDiffAt_traceTotalSpaceMk_of_localCoeff
  -- Goal: `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ,ℂ) ω (fun y => traceLocalCoeff (traceFunExt f α) y₀ y) y₀`.
  set L : ℂ := limUnder (𝓝[≠] z₀) G with hL
  have hBfin : (branchLocus f).Finite := finite_branchLocus_of_nonconstant f hf hnonconst
  have hz₀_target : z₀ ∈ c.target := c.map_source (mem_chart_source ℂ y₀)
  -- The other branch points in the chart, pushed into the chart codomain: a finite set `Badℂ`
  -- of `c.target` not containing `z₀`. Removing it from `c.target` gives a nbhd `s` of `z₀` whose
  -- punctured part lands off the branch locus.
  set Bad : Set Y := (branchLocus f \ {y₀}) ∩ c.source with hBad
  have hBad_fin : Bad.Finite := (hBfin.diff.subset Set.inter_subset_left)
  set Badℂ : Set ℂ := c '' Bad with hBadℂ
  have hBadℂ_fin : Badℂ.Finite := hBad_fin.image _
  set s : Set ℂ := c.target \ Badℂ with hs_def
  have hz₀_notBadℂ : z₀ ∉ Badℂ := by
    rintro ⟨y, ⟨⟨_, hy_ne⟩, hy_src⟩, hcy⟩
    apply hy_ne
    -- `c y = z₀ = c y₀` with both in source ⟹ `y = y₀`.
    have := c.injOn hy_src (mem_chart_source ℂ y₀) (by rw [hcy])
    simpa using this
  have hz₀_s : z₀ ∈ s := ⟨hz₀_target, hz₀_notBadℂ⟩
  have hs_open : IsOpen s := c.open_target.sdiff hBadℂ_fin.isClosed
  have hs_mem : s ∈ 𝓝 z₀ := hs_open.mem_nhds hz₀_s
  -- On the punctured `s`, the chart preimage avoids the whole branch locus.
  have hpunct_off : ∀ z ∈ s \ {z₀}, c.symm z ∉ branchLocus f ∧ c.symm z ∈ c.source := by
    rintro z ⟨⟨hz_tgt, hz_notBad⟩, hz_ne⟩
    have hsrc : c.symm z ∈ c.source := c.map_target hz_tgt
    refine ⟨fun hzB => ?_, hsrc⟩
    -- if `c.symm z ∈ branchLocus`: either it is `y₀` (forces `z = z₀`) or it lands in `Badℂ`.
    by_cases hzy : c.symm z = y₀
    · exact hz_ne (by rw [Set.mem_singleton_iff, hz₀, ← hzy, c.right_inv hz_tgt])
    · exact hz_notBad ⟨c.symm z, ⟨⟨hzB, hzy⟩, hsrc⟩, c.right_inv hz_tgt⟩
  -- **`G` is complex-differentiable on the punctured `s`.**
  have hG_diff : DifferentiableOn ℂ G (s \ {z₀}) := by
    intro z hz
    obtain ⟨hz_off, hz_src⟩ := hpunct_off z hz
    -- `Hraw` is `ContMDiffAt (c.symm z)`; its `y₀`-chart pullback is differentiable at `c (c.symm z) = z`.
    have hHraw_smooth : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω Hraw (c.symm z) :=
      contMDiffAt_traceLocalCoeff_of_notMem_branchLocus f hf hnonconst α y₀ hz_off hz_src
    have hdiff := differentiableAt_chartPullback_of_contMDiffAt (y₀ := y₀) hHraw_smooth hz_src
    -- `c (c.symm z) = z`, so this is `DifferentiableAt G z`.
    rw [c.right_inv hz.1.1] at hdiff
    exact hdiff.differentiableWithinAt
  -- **`G` is bounded on the punctured `s`** (the crux, restricted to `s \ {z₀} ⊆` the good set).
  have hG_bdd : BddAbove (norm ∘ G '' (s \ {z₀})) := by
    refine (traceLocalCoeff_bddAbove f hf hnonconst α hy₀).mono (Set.image_mono ?_)
    rintro z hz
    obtain ⟨hz_off, _⟩ := hpunct_off z hz
    exact ⟨⟨hz.1.1, hz_off⟩, hz.2⟩
  -- **Removable singularity**: `update G z₀ L` is differentiable on the whole `s`, hence analytic at `z₀`.
  have hupd : DifferentiableOn ℂ (Function.update G z₀ L) s :=
    Complex.differentiableOn_update_limUnder_of_bddAbove hs_mem hG_diff hG_bdd
  have hanalytic : AnalyticAt ℂ (Function.update G z₀ L) z₀ := hupd.analyticAt hs_mem
  -- **`Hext ∘ c.symm` agrees with the analytic extension on a full neighborhood of `z₀`.**
  have hsymm_z₀ : c.symm z₀ = y₀ := by rw [hz₀]; exact c.left_inv (mem_chart_source ℂ y₀)
  have hkey : (Hext ∘ c.symm) =ᶠ[𝓝 z₀] Function.update G z₀ L := by
    -- Off `z₀`: `Hext ∘ c.symm = Hraw ∘ c.symm = G = update G z₀ L`. At `z₀`: both equal `L`.
    have hpunct : (Hext ∘ c.symm) =ᶠ[𝓝[≠] z₀] Function.update G z₀ L := by
      -- On the punctured nbhd `Hext = Hraw` (pull back `traceFunExt =ᶠ traceFun` through `c.symm`).
      have hHeq : (Hext ∘ c.symm) =ᶠ[𝓝[≠] z₀] (Hraw ∘ c.symm) := by
        -- `c.symm` maps the punctured nbhd of `z₀` to the punctured nbhd of `y₀`:
        -- continuous at `z₀` (→ `y₀`) and injective on `c.target`, so `z ≠ z₀ ⟹ c.symm z ≠ y₀`.
        have hcs_cont : Filter.Tendsto c.symm (𝓝 z₀) (𝓝 y₀) := by
          have := (c.continuousAt_symm hz₀_target)
          rw [ContinuousAt, hsymm_z₀] at this; exact this
        have hmap : Filter.Tendsto c.symm (𝓝[≠] z₀) (𝓝[≠] y₀) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨hcs_cont.mono_left nhdsWithin_le_nhds, ?_⟩
          filter_upwards [self_mem_nhdsWithin,
            nhdsWithin_le_nhds (c.open_target.mem_nhds hz₀_target)] with z hz_ne hz_tgt
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          intro hcsy
          exact hz_ne (by rw [Set.mem_singleton_iff, hz₀, ← hcsy, c.right_inv hz_tgt])
        have hHeq' : Hext =ᶠ[𝓝[≠] y₀] Hraw := by
          filter_upwards [eventually_notMem_branchLocus f hf hnonconst y₀] with y hy_off
          simp only [hHext, hHraw, traceLocalCoeff, traceFunExt_of_notMem_branchLocus f α hy_off]
        exact hHeq'.comp_tendsto hmap
      filter_upwards [hHeq, self_mem_nhdsWithin] with z hz hz_ne
      rw [hz]
      simp only [hG, Function.comp_apply, Function.update_of_ne hz_ne]
    -- Patch the value at `z₀`: `(Hext ∘ c.symm) z₀ = Hext y₀ = L = update G z₀ L z₀`.
    have hval : (Hext ∘ c.symm) z₀ = Function.update G z₀ L z₀ := by
      simp only [Function.comp_apply, hsymm_z₀, Function.update_self]
      rw [hHext]; exact hmatch
    exact eventuallyEq_nhds_of_eventuallyEq_nhdsNE hpunct hval
  -- **Conclude**: the extended local coefficient is `ContMDiffAt` at `y₀`.
  refine contMDiffAt_of_analyticAt_chartPullback ?_ ?_
  · -- `ContinuousAt Hext y₀`: `Hext = (Hext ∘ c.symm) ∘ c` near `y₀`; both factors continuous.
    have hcontPull : ContinuousAt (Hext ∘ c.symm) z₀ :=
      (hanalytic.continuousAt).congr hkey.symm
    have hc_contAt : ContinuousAt (c : Y → ℂ) y₀ :=
      (c.continuousOn.continuousAt (c.open_source.mem_nhds (mem_chart_source ℂ y₀)))
    have hcomp : ContinuousAt ((Hext ∘ c.symm) ∘ (c : Y → ℂ)) y₀ := by
      rw [hz₀] at hcontPull; exact hcontPull.comp hc_contAt
    refine hcomp.congr ?_
    filter_upwards [c.open_source.mem_nhds (mem_chart_source ℂ y₀)] with y hy
    simp only [Function.comp_apply, c.left_inv hy, hHext]
  · -- `AnalyticAt (Hext ∘ c.symm) z₀` from the analytic extension.
    rw [← hz₀]
    exact hanalytic.congr hkey.symm

/-- **Existence of the trace** `f₊ : Ω¹(X) →ₗ[ℂ] Ω¹(Y)` as a genuine holomorphic
one-form linear map agreeing with the off-branch fibre sum `traceFun`. Now a one-line
consequence of the fully-proven reduction `exists_traceForm_of_branchExtension` and the
isolated per-branch-point analytic input `traceExtendsAt_branchPoint`. Sound (classically
true; Forster §10, Griffiths–Harris Ch. 2 §2.7). -/
theorem exists_traceForm (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    ∃ T : HolomorphicOneForms X →ₗ[ℂ] HolomorphicOneForms Y,
      ∀ (α : HolomorphicOneForms X) (y : Y), y ∉ branchLocus f →
        (T α).toFun y = traceFun f α y :=
  exists_traceForm_of_branchExtension f hf hnonconst
    (fun α _y₀ hy₀ => traceExtendsAt_branchPoint f hf hnonconst α hy₀)

/-- **Trace (pushforward) of holomorphic one-forms**, `f₊ : Ω¹(X) →ₗ[ℂ] Ω¹(Y)`,
extracted from `exists_traceForm`. Off the branch locus it is the holomorphic
fibre sum `traceFun`; across the (finite) branch locus it is the removable-singularity
extension. -/
noncomputable def traceForm (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    HolomorphicOneForms X →ₗ[ℂ] HolomorphicOneForms Y :=
  (exists_traceForm f hf hnonconst).choose

/-- `traceForm` agrees with the fibre-sum `traceFun` off the branch locus. -/
theorem traceForm_toFun_of_notMem_branchLocus (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X)
    {y : Y} (hy : y ∉ branchLocus f) :
    (traceForm f hf hnonconst α).toFun y = traceFun f α y :=
  (exists_traceForm f hf hnonconst).choose_spec α y hy

/-- **Local sheet decomposition of the trace form.** Off the branch locus there is a
local sheet system `S` at `y₀` over whose base `S.V` the trace one-form is the finite
sum of the per-sheet pullbacks: at every off-branch `y ∈ S.V`,
`(traceForm f hf hnonconst α).toFun y = ∑ᵢ sheetPullback α (S.sheet i) y`.

This is the **per-base-neighborhood input to the period-level projection formula**:
to integrate `traceForm f hf α` along a loop `δ` (which avoids the branch locus),
cover the compact `δ([0,1])` by finitely many such bases, and on each the trace
splits into sheet pullbacks, each of which is `∫_δ sheetPullback = ∫_{sheet∘δ} α`
(`lineIntegral_pullback_section`). Combines `exists_localSheetSystem` (the off-branch
covering) with `LocalSheetSystem.traceFun_eq_sum_sheetPullback` and the off-branch
agreement `traceForm_toFun_of_notMem_branchLocus`. -/
theorem exists_localSheetSystem_traceForm_eq_sum (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (α : HolomorphicOneForms X)
    {y₀ : Y} (hy₀ : y₀ ∉ branchLocus f) :
    ∃ S : LocalSheetSystem f y₀, ∀ y ∈ S.V, y ∉ branchLocus f →
      (traceForm f hf hnonconst α).toFun y = ∑ i, sheetPullback α (S.sheet i) y := by
  obtain ⟨S⟩ := exists_localSheetSystem f hf hnonconst hy₀
  refine ⟨S, fun y hyV hyB => ?_⟩
  rw [traceForm_toFun_of_notMem_branchLocus f hf hnonconst α hyB]
  exact S.traceFun_eq_sum_sheetPullback hf α hyV

/-! ## The projection formula (period level)

The eventual goal is the multi-sheet projection formula
`lineIntegral (traceForm f hf α) δ = ∑ₖ lineIntegral α (liftₖ)`, where `liftₖ` are
the lifts of a closed loop `δ` (off the branch locus) to the sheets of the cover.
The heart is the proven change-of-variables `lineIntegral_pullback`:
`lineIntegral α (f ∘ γ) = lineIntegral (pullbackForm f hf α) γ`.

We prove the **single-sheet** form in full: along one global holomorphic section
`s : Y → X` of `f` (with lift `s ∘ δ`), the line integral of the pulled-back form
`pullbackForm s hs α` over `δ` equals the line integral of `α` over the lift
`s ∘ δ`. The full multi-sheet identity is the sum of these single-sheet identities
over the sheet sections; what is missing is the lift/monodromy assembly producing
the indexed family of global lifts (the loop-lifting `PreimageCycle` machinery in
`PeriodLattice.lean`, gated on `exists_preimageCycle_of_off_branchLocus`). -/

/-- **Single-sheet projection formula (line integral).** For a holomorphic section
`s : Y → X` of `f`, the line integral of the pulled-back form `pullbackForm s hs α`
along a (regular) path `δ` equals the line integral of `α` along the lift `s ∘ δ`.

This is exactly `lineIntegral_pullback` read with the section `s` as the map: it is
the per-sheet term of the projection formula. The lift `s ∘ δ` is the path in `X`
covering `δ` (`f ∘ (s ∘ δ) = δ` since `f ∘ s = id`). -/
theorem lineIntegral_pullback_section (s : Y → X) (hs : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω s)
    (α : HolomorphicOneForms X) (δ : ℝ → Y)
    (hδ_cont : Continuous δ)
    (hδ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (δ t)).toFun ∘ δ) t) :
    lineIntegral (pullbackForm s hs α) δ = lineIntegral α (s ∘ δ) :=
  (lineIntegral_pullback s hs α δ hδ_cont hδ_diff).symm

/-- **Single-sheet projection formula for the trace.** When `f` admits a *global*
holomorphic section `s` and the trace form coincides with the single-sheet pullback
`pullbackForm s hs α` (e.g. a one-sheeted cover, where the fibre over each off-branch
point is the single point `s y`), the line integral of the trace along `δ` equals
the line integral of `α` along the lift `s ∘ δ`.

The coincidence hypothesis `htrace` is what the multi-sheet assembly supplies as a
sum; here we isolate the clean single-sheet consequence of `lineIntegral_pullback`. -/
theorem lineIntegral_traceForm_single_sheet (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) (s : Y → X) (hs : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω s)
    (α : HolomorphicOneForms X) (δ : ℝ → Y)
    (hδ_cont : Continuous δ)
    (hδ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (δ t)).toFun ∘ δ) t)
    (htrace : traceForm f hf hnonconst α = pullbackForm s hs α) :
    lineIntegral (traceForm f hf hnonconst α) δ = lineIntegral α (s ∘ δ) := by
  rw [htrace]
  exact lineIntegral_pullback_section s hs α δ hδ_cont hδ_diff

/-- Evaluating a finite sum of holomorphic one-forms at `y` against a tangent
vector `v` equals the sum of the pointwise evaluations. -/
theorem sum_toFun_apply {k : ℕ} (forms : Fin k → HolomorphicOneForms Y) (y : Y) (v : ℂ) :
    (∑ i, forms i).toFun y v = ∑ i, (forms i).toFun y v := by
  classical
  induction k with
  | zero =>
    show (0 : HolomorphicOneForms Y).toFun y v = 0
    rfl
  | succ m ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, ← ih (fun i => forms i.succ)]
    -- Addition of sections is pointwise; the covector evaluation distributes.
    rfl

/-- Line integral of a finite sum of forms is the sum of line integrals, under
per-form integrability along `γ`. (Finset version of `lineIntegral_add`, by
induction on the index set.) -/
theorem lineIntegral_sum {k : ℕ} (forms : Fin k → HolomorphicOneForms Y) (δ : ℝ → Y)
    (hint : ∀ i, IntervalIntegrable
      (fun t : ℝ => (forms i).toFun (δ t) (pathSpeed δ t)) MeasureTheory.volume 0 1) :
    lineIntegral (∑ i, forms i) δ = ∑ i, lineIntegral (forms i) δ := by
  classical
  induction k with
  | zero => simp [lineIntegral_zero]
  | succ m ih =>
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    have hint_tail : ∀ i : Fin m, IntervalIntegrable
        (fun t : ℝ => (forms i.succ).toFun (δ t) (pathSpeed δ t)) MeasureTheory.volume 0 1 :=
      fun i => hint i.succ
    have hint_head := hint 0
    have hint_tailsum : IntervalIntegrable
        (fun t : ℝ => (∑ i : Fin m, forms i.succ).toFun (δ t) (pathSpeed δ t))
          MeasureTheory.volume 0 1 := by
      have heq : (fun t : ℝ => (∑ i : Fin m, forms i.succ).toFun (δ t) (pathSpeed δ t)) =
          ∑ i : Fin m, (fun t : ℝ => (forms i.succ).toFun (δ t) (pathSpeed δ t)) := by
        funext t; rw [Finset.sum_apply]; exact sum_toFun_apply _ (δ t) (pathSpeed δ t)
      rw [heq]
      exact IntervalIntegrable.sum _ (fun i _ => hint_tail i)
    rw [lineIntegral_add _ _ _ hint_head hint_tailsum, ih (fun i => forms i.succ) hint_tail]

/-- **Multi-sheet projection formula (line integral).** Given a family of global
holomorphic sections `s i : Y → X` whose pullbacks sum to the trace form
(`htrace`), the line integral of the trace along `δ` is the sum over sheets of the
line integrals of `α` along the lifts `s i ∘ δ`. Combines `lineIntegral_sum` with
the single-sheet `lineIntegral_pullback_section`. This is the period-level
projection formula; the remaining classical input is producing the sheet sections
+ the `htrace` decomposition (the loop-lifting machinery). -/
theorem lineIntegral_traceForm_eq_sum_lifts {k : ℕ} (f : X → Y)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (s : Fin k → Y → X) (hs : ∀ i, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (s i))
    (α : HolomorphicOneForms X) (δ : ℝ → Y)
    (hδ_cont : Continuous δ)
    (hδ_diff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (δ t)).toFun ∘ δ) t)
    (hint : ∀ i, IntervalIntegrable
      (fun t : ℝ => (pullbackForm (s i) (hs i) α).toFun (δ t) (pathSpeed δ t))
        MeasureTheory.volume 0 1)
    (htrace : traceForm f hf hnonconst α = ∑ i, pullbackForm (s i) (hs i) α) :
    lineIntegral (traceForm f hf hnonconst α) δ = ∑ i, lineIntegral α (s i ∘ δ) := by
  rw [htrace, lineIntegral_sum _ δ hint]
  exact Finset.sum_congr rfl fun i _ =>
    lineIntegral_pullback_section (s i) (hs i) α δ hδ_cont hδ_diff

/-! ## Covariant functoriality of the trace

`traceForm` is covariant to `f` (a trace sums over the sheets of the cover, and
sheet counts of the identity / a composite cover behave as expected). These are the
two functoriality laws of the genuine geometric trace `f₊`; together with the
single branch-extension input (`traceExtendsAt_branchPoint`) they are the trace's
remaining analytic content. They drive the ambient pullback `Tᵀ` downstream
(`Jacobians/TracePullback.lean`).

Each is stated with the non-constancy hypotheses that `traceForm` itself requires.
The constant-map bookkeeping is handled once, downstream, by the total wrapper
`traceFormTotal` and its laws. -/

/-- **`f₊(id) = id`** — the identity map is a one-sheeted unbranched cover, so its
trace is the identity. Honest sorry: classically true (Forster §10), but in this
formalization `traceForm` is the removable-singularity extension of the off-branch
fibre sum, and proving the extension of the (single-sheet) fibre sum for `id` equals
`id` on *all* of `X` is the identity-theorem upgrade of the off-branch agreement —
the same analytic status as `traceExtendsAt_branchPoint`. -/
theorem traceForm_id (hnonconst : ¬ ∃ x₀ : X, ∀ x, (id : X → X) x = x₀) :
    traceForm (id : X → X) contMDiff_id hnonconst =
      LinearMap.id (R := ℂ) (M := HolomorphicOneForms X) := by
  -- `id` is injective on every neighborhood, so its critical set — hence its branch
  -- locus — is empty. Thus the trace agrees with the fibre sum at *every* point, and
  -- the singleton fibre `id⁻¹'{y} = {y}` collapses the sum to `α y`.
  have hcrit : criticalSet (id : X → X) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    exact hx ⟨Set.univ, Filter.univ_mem, Set.injOn_id _⟩
  have hbranch : branchLocus (id : X → X) = ∅ := by
    rw [branchLocus, hcrit, Set.image_empty]
  refine LinearMap.ext (fun α => ?_)
  refine ContMDiffSection.ext (fun y => ?_)
  show (traceForm (id : X → X) contMDiff_id hnonconst α).toFun y = α.toFun y
  have hy : y ∉ branchLocus (id : X → X) := by rw [hbranch]; exact Set.notMem_empty y
  rw [traceForm_toFun_of_notMem_branchLocus (id : X → X) contMDiff_id hnonconst α hy]
  -- `traceFun id α y = ∑ᶠ x ∈ id⁻¹'{y}, traceSummandAt id α y x`; the fibre is `{y}`.
  show (∑ᶠ (x : X) (_ : x ∈ (id : X → X) ⁻¹' {y}), traceSummandAt (id : X → X) α y x)
      = α.toFun y
  have hfib : (id : X → X) ⁻¹' {y} = {y} := by simp [Set.preimage_id]
  rw [hfib, finsum_mem_singleton]
  show traceSummand (id : X → X) α y = α.toFun y
  show (α.toFun y).comp ((mfderiv 𝓘(ℂ) 𝓘(ℂ) (id : X → X) y).inverse) = α.toFun y
  -- `mfderiv id y = id`, so its inverse is `id` and the comp collapses.
  have hinv : (mfderiv 𝓘(ℂ) 𝓘(ℂ) (id : X → X) y).inverse
      = ContinuousLinearMap.id ℂ (TangentSpace 𝓘(ℂ) y) := by
    rw [mfderiv_id]; exact ContinuousLinearMap.inverse_id
  rw [hinv]; exact ContinuousLinearMap.comp_id _

/-- **Covariance of the trace: `(g ∘ f)₊ = g₊ ∘ f₊`** (sheet counts of composite
covers multiply, and the per-sheet pullbacks compose contravariantly so the traces
compose covariantly). Honest sorry: classically true (Griffiths–Harris Ch. 2 §2.7),
same analytic status as `traceForm_id` / `traceExtendsAt_branchPoint`. -/
theorem traceForm_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (hfnc : ¬ ∃ y₀ : Y, ∀ x, f x = y₀)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (hgnc : ¬ ∃ z₀ : Z, ∀ y, g y = z₀)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f)) (hgfnc : ¬ ∃ z₀ : Z, ∀ x, (g ∘ f) x = z₀) :
    traceForm (g ∘ f) hgf hgfnc =
      (traceForm g hg hgnc).comp (traceForm f hf hfnc) :=
  -- Honest sorry. The intended proof is density + continuity: both sides are
  -- forms whose fibre-component map `z ↦ (·) z : Z → (ℂ →L[ℂ] ℂ)` is continuous,
  -- and they agree off a finite bad set `B` (the union of `branchLocus (g∘f)`,
  -- `branchLocus g`, and the `g`-images of points where some `f`-fibre meets
  -- `branchLocus f`), whose complement is dense (`Y`/`Z` are perfect spaces —
  -- `neBot_nhdsWithin_compl_self`). Two remaining gaps make this too heavy here:
  -- (1) a continuity extractor `Continuous (fun z ↦ (form) z)` for the model-fibre
  --     component of a `ContMDiffSection` into the (only locally trivial) cotangent
  --     hom-bundle — needs the `contMDiffAt_hom_bundle` trivialization machinery,
  --     as in `contMDiffAt_pullback_section`;
  -- (2) the off-branch fibre factorization
  --     `traceFun (g∘f) α z = traceFun g (traceForm f hf hfnc α) z`, via the disjoint
  --     partition `(g∘f)⁻¹'{z} = ⋃_{y∈g⁻¹'{z}} f⁻¹'{y}` (`finsum_mem_biUnion`), the
  --     chain rule `mfderiv (g∘f) x = mfderiv g (f x) ∘ mfderiv f x` (`mfderiv_comp`)
  --     with `(·)⁻¹` of the composite, and pulling the common right-`comp` out of the
  --     inner finsum — the combinatorial finsum-partition step that remains.
  sorry

/-! ## Total trace wrapper (constant-map bookkeeping)

`traceForm` requires `f` non-constant (the off-branch fibre sum is empty of content
for a constant map, whose degree is `0`). The downstream ambient layer needs a map
defined for **every** holomorphic `f`. `traceFormTotal` supplies it: it is `0` on
constant maps (degree `0`, no sheets) and the genuine `traceForm` otherwise. Its
three laws (`_eq_zero_of_const`, `_id`, `_comp`) are the exact drop-in replacements
for the old `pushforwardForm_*`; the constancy case-splits live here, once. -/

/-- **Total trace** `f₊ : Ω¹(X) →ₗ[ℂ] Ω¹(Y)`, defined for every holomorphic `f`:
the genuine `traceForm` when `f` is non-constant, and `0` when `f` is constant
(degree `0`). This is the object the ambient coordinate layer dualizes. -/
noncomputable def traceFormTotal (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    HolomorphicOneForms X →ₗ[ℂ] HolomorphicOneForms Y := by
  classical
  exact if h : ∃ y₀ : Y, ∀ x, f x = y₀ then 0 else traceForm f hf h

/-- **Total trace of a constant map is zero** (degree `0`, no sheets to sum over).
Drop-in replacement for `pushforwardForm_eq_zero_of_const`. -/
theorem traceFormTotal_eq_zero_of_const (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hconst : ∃ y₀ : Y, ∀ x, f x = y₀) :
    traceFormTotal f hf = 0 := by
  classical
  rw [traceFormTotal, dif_pos hconst]

/-- **Off-constant, the total trace is the genuine trace.** -/
theorem traceFormTotal_of_nonconstant (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    traceFormTotal f hf = traceForm f hf hnonconst := by
  classical
  rw [traceFormTotal, dif_neg hnonconst]

/-- A non-constant `f : X → Y` between compact Riemann surfaces is **surjective**
(its image is clopen in connected `Y`). Re-exported here from
`surjective_of_nonconstant` (PeriodLattice) for the composite-non-constancy argument
in `traceFormTotal_comp`. -/
private theorem surjective_of_nonconstant' (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) : Function.Surjective f :=
  surjective_of_nonconstant f hf hnonconst

/-- **`traceFormTotal id = id`** — for an infinite `X` the identity is non-constant,
so `traceFormTotal id = traceForm id`, which is the identity by `traceForm_id`. Drop-in
replacement for `pushforwardForm_id`. -/
theorem traceFormTotal_id : traceFormTotal (id : X → X) contMDiff_id =
    LinearMap.id (R := ℂ) (M := HolomorphicOneForms X) := by
  classical
  haveI : Infinite X := Jacobians.Discharge.ContMDiff.Degree.y_infinite_of_chartedSpace_complex
  have hnc : ¬ ∃ x₀ : X, ∀ x, (id : X → X) x = x₀ := by
    rintro ⟨x₀, hx₀⟩
    obtain ⟨a, b, hab⟩ := exists_pair_ne X
    exact hab ((hx₀ a).trans (hx₀ b).symm)
  rw [traceFormTotal_of_nonconstant (id : X → X) contMDiff_id hnc, traceForm_id hnc]

/-- **Covariance `traceFormTotal (g ∘ f) = traceFormTotal g ∘ₗ traceFormTotal f`.**
Case-splits on constancy: if `f` or `g` is constant the composite is constant and
both sides collapse to `0` (composition with the zero map); otherwise `f` is
surjective, so `g ∘ f` non-constant follows from `g` non-constant, and the law is
`traceForm_comp`. Drop-in replacement for `pushforwardForm_comp`. -/
theorem traceFormTotal_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f)) :
    traceFormTotal (g ∘ f) hgf =
      (traceFormTotal g hg).comp (traceFormTotal f hf) := by
  classical
  by_cases hfc : ∃ y₀ : Y, ∀ x, f x = y₀
  · -- `f` constant ⟹ `g ∘ f` constant; both sides are `0`.
    obtain ⟨y₀, hy₀⟩ := hfc
    have hgfc : ∃ z₀ : Z, ∀ x, (g ∘ f) x = z₀ := ⟨g y₀, fun x => by simp [hy₀ x]⟩
    rw [traceFormTotal_eq_zero_of_const (g ∘ f) hgf hgfc,
      traceFormTotal_eq_zero_of_const f hf ⟨y₀, hy₀⟩, LinearMap.comp_zero]
  · by_cases hgc : ∃ z₀ : Z, ∀ y, g y = z₀
    · -- `g` constant ⟹ `g ∘ f` constant; both sides are `0`.
      obtain ⟨z₀, hz₀⟩ := hgc
      have hgfc : ∃ z₀ : Z, ∀ x, (g ∘ f) x = z₀ := ⟨z₀, fun x => hz₀ (f x)⟩
      rw [traceFormTotal_eq_zero_of_const (g ∘ f) hgf hgfc,
        traceFormTotal_eq_zero_of_const g hg ⟨z₀, hz₀⟩, LinearMap.zero_comp]
    · -- both non-constant: `f` surjective ⟹ `g ∘ f` non-constant; apply `traceForm_comp`.
      have hgfnc : ¬ ∃ z₀ : Z, ∀ x, (g ∘ f) x = z₀ := by
        rintro ⟨z₀, hz₀⟩
        exact hgc ⟨z₀, fun y => by
          obtain ⟨x, rfl⟩ := surjective_of_nonconstant' f hf hfc y
          exact hz₀ x⟩
      rw [traceFormTotal_of_nonconstant (g ∘ f) hgf hgfnc,
        traceFormTotal_of_nonconstant f hf hfc, traceFormTotal_of_nonconstant g hg hgc,
        traceForm_comp f hf hfc g hg hgc hgf hgfnc]

end Jacobians
