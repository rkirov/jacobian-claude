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

/-- **[ISOLATED SORRY — covering trivialization unpacking]** Off the branch locus a
local sheet system exists. This is the *only* irreducible step in the off-branch
construction.

Construction (Forster §4.22; Mathlib `IsCoveringMapOn`/`IsEvenlyCovered`): off the
branch locus `f` is proper + a local homeo, hence restricts to a finite covering
`isCoveringMapOn_compl_branchLocus`. Over `y₀` the fibre is finite
(`fiber_finite_off_branchLocus`); shrinking via `properNbhd` gives an open
`V ∋ y₀` over which `f⁻¹V` splits into `|f⁻¹{y₀}|` disjoint open sheets, each a
graph of a `C^ω` section `sheet i` (from `exists_twoSided_localInverse` at each
fibre point — supplying `sheet_smooth`, `sheet_section`, `sheet_leftInv`). The
covering's even-covering homeomorphism `f⁻¹V ≃ V × fibre` gives `fibre_eq` (the
sheets exhaust each fibre) and `sheet_inj` (distinct sheets stay disjoint).

What is needed to discharge this: extract, from Mathlib's `IsCoveringMapOn` even
covering over `y₀` together with `properNbhd`, the indexed family of section
graphs as functions `Fin n → Y → X`, and transport the trivialization's
`fibre = sheets` bijection through the charts. Bounded but genuinely lengthy
(Forster 4.22–4.23). The per-sheet `C^ω` sections themselves are already available
unconditionally (`exists_twoSided_localInverse`). -/
theorem exists_localSheetSystem (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) {y₀ : Y} (hy₀ : y₀ ∉ branchLocus f) :
    Nonempty (LocalSheetSystem f y₀) :=
  sorry

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

/-! ## Assembling into `HolomorphicOneForms Y` via branch extension

The off-branch fibre sum `traceFun f α` is a holomorphic one-form on `Y ∖ branchLocus f`
(`contMDiffAt_traceFun_of_notMem_branchLocus`). To upgrade it to a *global* element
of `HolomorphicOneForms Y` we must extend across the finite `branchLocus f`. The
trace is bounded near each branch point (a finite sum of bounded local terms — the
ramified sheets), so by Riemann's removable-singularity theorem it extends
holomorphically; the extended value at a branch point is the limit, **not** the
naive `finsum` (which is `0` there when the fibre is infinite). For this reason the
global section's `toFun` is the *extension*, characterized by agreeing with `traceFun`
off the branch locus — we must not assert global smoothness of `traceFun` itself,
which is false at branch points.

We package this honestly as an existence theorem: the genuine trace `LinearMap`
exists and agrees with the proven fibre sum off the branch locus. The single
`sorry` isolates exactly two pieces of classical content:
* the **covering unpacking** (`exists_localSheetSystem`, used off-branch), and
* the **removable-singularity extension** across `branchLocus f`
  (Riemann's theorem; project infra in `Discharge/Manifold/MeromorphicExtension.lean`,
  Mathlib `Complex.differentiableOn_update_limUnder_…`).
Linearity of the trace map follows from the proven pointwise linearity of the fibre
sum (`traceFun_add_of_notMem_branchLocus`, `traceFun_smul_of_notMem_branchLocus`)
together with continuity of the extension; it is bundled into the existence claim. -/

/-- **[ISOLATED SORRY — branch extension + assembly]** The trace
`f₊ : Ω¹(X) →ₗ[ℂ] Ω¹(Y)` exists as a genuine holomorphic one-form linear map,
agreeing with the off-branch fibre sum `traceFun`. Sound (classically true; Forster
§10, Griffiths–Harris Ch. 2 §2.7). The `sorry` covers the removable-singularity
extension across the finite branch locus plus the covering unpacking. -/
theorem exists_traceForm (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hnonconst : ¬ ∃ y₀ : Y, ∀ x, f x = y₀) :
    ∃ T : HolomorphicOneForms X →ₗ[ℂ] HolomorphicOneForms Y,
      ∀ (α : HolomorphicOneForms X) (y : Y), y ∉ branchLocus f →
        (T α).toFun y = traceFun f α y :=
  sorry

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

end Jacobians
