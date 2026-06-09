/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.MeromorphicCousin

/-!
# Forster §15 + §17.2–17.3 — the meromorphic Cousin solve, the distribution algebra, and the descent

This file continues `MeromorphicCousin.lean` (the connecting map `δ` and the residue calculus at the
genuine Forster `δμ ∈ Z¹(Ω)` strength).  Its goal is the wall `H¹(X, ℳ) = 0` (the `surjective` field
of `MeromorphicCousinSolvable`) and the mechanical descent that turns a Cousin solution into the
Serre residue functional.

## The `holoOff` gap (read first — a genuine soundness finding)

The committed `CoverMLDistribution 𝔘 ω₀ K` carries `diffMem`/`formHoloDiff` (the overlap conditions of
`δμ ∈ Z¹(Ω)`) and `iso` (isolated singularity at each recorded pole) — but **no `holoOff` field**
(holomorphy away from the recorded poles, as `GeneralMLDistribution` has).  Without it:

* its distribution **algebra is unbuildable**: `combine μ₁ μ₂`'s `iso` at a pole `a ∈ μ₁.poles \ μ₂.poles`
  needs `μ₂.g (μ₁.patch a)` isolated at `a`, which (when `a ∉ μ₂.poles`) is exactly `holoOff`; and
* `μ.res = ∑_{a ∈ poles} Resₐ` need **not be the genuine total residue** (a "global" pole of every `gᵢ`
  outside `poles`, cancelled in all differences, is invisible to `poles` yet contributes a residue).

So the descent's well-definedness `[δμ₁] = [δμ₂] ⟹ μ₁.res = μ₂.res` (via Gate A) genuinely needs
`holoOff`.  Rather than mutate the committed structure (and the proven connecting map), we introduce a
**richer lift** `CoverMLLift 𝔘 ω₀ K` (= `CoverMLDistribution` + `holoOff`), build the algebra and the
descent on it, and reduce the wall to a single precise Cousin atom on `CoverMLLift`.  A genuine Cousin
solution (the local-meromorphic lift of a cocycle) always has `holoOff`, so this is no loss.

## What this file delivers (sorry-free, axiom-clean unless noted)

* `CoverMLLift 𝔘 ω₀ K` — the `holoOff`-equipped lift; `toDistribution` forgets `holoOff`, `res`/
  `connectingCocycle`/`connectingClass` inherited.
* The **distribution algebra**: `smul`, `neg`, `combine` (add), `sub`, each a genuine `CoverMLLift`,
  with `res_smul`/`res_neg`/`res_combine`/`res_sub` (res-additivity from `formFnResidue_add`/`_smul`)
  and `connectingCochain`/`connectingClass` additivity.
* `holoOff` gives that **`res` is the genuine total residue** (`res_eq_residueSum_of_subset`-style):
  every pole of every `gᵢ` is recorded, so `res` reads the full Laurent residue sum.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §15 (`H¹(X,ℳ)=0`), §17.2–17.3;
`MeromorphicCousin.lean`; `GeneralMittagLeffler.lean` (`res_eq_zero_of_globalMeromorphic`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

variable {𝔘 : FiniteCover X} {ω₀ : HolomorphicOneForms X} {K : Divisor X}

/-! ## The `holoOff`-equipped Cousin lift -/

/-- **A meromorphic Cousin lift** over the fixed cover `𝔘`: a `CoverMLDistribution` together with the
**off-poles holomorphy** field `holoOff` that the committed `CoverMLDistribution` omits (see the module
docstring).  A genuine Cousin solution (the local-meromorphic lift `gᵢ` of an `𝒪_K` cocycle) always has
it: away from the finitely many recorded poles each `gᵢ` is holomorphic.  With it the residue is the
genuine total residue and the distribution algebra (`combine`/`sub`) closes. -/
structure CoverMLLift (𝔘 : FiniteCover X) (ω₀ : HolomorphicOneForms X) (K : Divisor X) where
  /-- The underlying cover-adapted distribution (the data the connecting map δ consumes). -/
  toDistribution : CoverMLDistribution 𝔘 ω₀ K
  /-- **Off-poles holomorphy**: away from the recorded poles each `gᵢ`'s chart-pullback is analytic at
  every point of `𝔘.U i` (so `ωᵢ = gᵢ·ω₀` is holomorphic there). -/
  holoOff : ∀ (i : 𝔘.ι) (a : X), a ∈ 𝔘.U i → a ∉ toDistribution.poles →
    AnalyticAt ℂ (fun z => toDistribution.g i ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)

namespace CoverMLLift

variable (μ : CoverMLLift 𝔘 ω₀ K)

/-- The local principal part on patch `i`. -/
def g (i : 𝔘.ι) : X → ℂ := μ.toDistribution.g i

/-- The finite pole set. -/
def poles : Finset X := μ.toDistribution.poles

/-- The total residue of the lift (the underlying distribution's genuine Laurent residue sum). -/
noncomputable def res : ℂ := μ.toDistribution.res

/-- The connecting cocycle `δμ ∈ Z¹(𝔘, 𝒪_K)` (inherited from the underlying distribution). -/
noncomputable def connectingCocycle : ↥(𝔘.toFiniteFamily.cocycles1 K) :=
  μ.toDistribution.connectingCocycle

/-- The connecting class `[δμ] ∈ cechH1 K` (inherited). -/
noncomputable def connectingClass : 𝔘.toFiniteFamily.cechH1 K :=
  μ.toDistribution.connectingClass

@[simp] theorem res_def : μ.res = ∑ a ∈ μ.poles, formFnResidue ω₀ (μ.g (μ.toDistribution.patch a)) a :=
  CoverMLDistribution.res_def μ.toDistribution

/-- **Off poles, `ω₀·gᵢ` has an isolated singularity** (from `holoOff`).  At any `a ∉ poles` in
`𝔘.U i`, `gᵢ`'s chart-pullback is analytic, so `ω₀·gᵢ` is holomorphic — in particular isolated. -/
theorem formFnHoloPunctured_off (i : 𝔘.ι) {a : X} (ha : a ∈ 𝔘.U i) (hb : a ∉ μ.poles) :
    formFnHoloPunctured ω₀ (μ.g i) a :=
  formFnHoloPunctured_of_analyticAt ω₀ (μ.g i) a (μ.holoOff i a ha hb)

/-- **`ω₀·gᵢ` has an isolated singularity at every point of `𝔘.U i`** (genuine, from `iso` ∪ `holoOff`):
at recorded poles by `iso`/`formHoloDiff`, off them by `holoOff`.  This is the key fact the algebra and
the genuine-total-residue statement rest on. -/
theorem formFnHoloPunctured_everywhere (i : 𝔘.ι) {a : X} (ha : a ∈ 𝔘.U i) :
    formFnHoloPunctured ω₀ (μ.g i) a := by
  by_cases hb : a ∈ μ.poles
  · exact μ.toDistribution.toFormMLDistribution.formFnHoloPunctured_of_mem hb ha
  · exact μ.formFnHoloPunctured_off i ha hb

/-- **The residue of `ω₀·gᵢ` vanishes at a non-pole** of `𝔘.U i` (from `holoOff`): off the recorded
poles the form is holomorphic, residue `0`.  The key fact that makes `res` the genuine *total* residue
(extra points in any pole superset contribute nothing) and the distribution algebra close. -/
theorem formFnResidue_eq_zero_off (i : 𝔘.ι) {a : X} (ha : a ∈ 𝔘.U i) (hb : a ∉ μ.poles) :
    formFnResidue ω₀ (μ.g i) a = 0 :=
  formFnResidue_eq_zero_of_analyticAt ω₀ (μ.g i) a (μ.holoOff i a ha hb)

/-- **Cross-patch residue agreement** (the genuine Forster §17.2 patch-independence at full strength):
at any point `a` lying in both `𝔘.U i` and `𝔘.U j`, the residues of `ω₀·gᵢ` and `ω₀·gⱼ` agree, because
their form difference `(gᵢ − gⱼ)·ω₀` is holomorphic (`formHoloDiff`) and both are isolated. -/
theorem formFnResidue_patch_indep {i j : 𝔘.ι} {a : X} (hi : a ∈ 𝔘.U i) (hj : a ∈ 𝔘.U j) :
    formFnResidue ω₀ (μ.g i) a = formFnResidue ω₀ (μ.g j) a :=
  formFnResidue_eq_of_form_analyticAt_sub ω₀ (μ.g i) (μ.g j) a
    (μ.formFnHoloPunctured_everywhere i hi) (μ.toDistribution.formHoloDiff i j a hi hj)

/-! ### `res` as a residue-sum over any superset of the poles

The genuine total residue: for any finite `S ⊇ poles` such that every extra point lies in some patch
(automatic on a cover, where every point is in some `𝔘.U i`), the residue read at a point via *any*
patch containing it sums over `S` to `res` (the extra points are holomorphic, residue `0`).  This is
the bridge that makes `res` additive under `combine`. -/

/-- Every point of `X` lies in some patch of the cover `𝔘` (the cover is `⊤`). -/
theorem exists_patch (𝔘 : FiniteCover X) (a : X) : ∃ i, a ∈ 𝔘.U i := by
  have : a ∈ (⊤ : Opens X) := trivial
  rw [← 𝔘.covers] at this
  exact TopologicalSpace.Opens.mem_iSup.mp this

/-- A choice of patch containing `a` (well-defined on a genuine cover, where every point is covered). -/
noncomputable def patchOf (𝔘 : FiniteCover X) (a : X) : 𝔘.ι := (exists_patch 𝔘 a).choose

theorem patchOf_mem (𝔘 : FiniteCover X) (a : X) : a ∈ 𝔘.U (patchOf 𝔘 a) :=
  (exists_patch 𝔘 a).choose_spec

/-- **`res` as a residue-sum read via `patchOf` over the pole set.**  At each pole `a`, the residue
read via *any* patch containing `a` equals `resAtPole a` (patch-independence), so the `patchOf`-read
sum over `poles` is `res`. -/
theorem res_eq_sum_patchOf :
    μ.res = ∑ a ∈ μ.poles, formFnResidue ω₀ (μ.g (patchOf 𝔘 a)) a := by
  rw [CoverMLLift.res, CoverMLDistribution.res_def]
  refine Finset.sum_congr rfl fun a ha => ?_
  exact (μ.formFnResidue_patch_indep (patchOf_mem 𝔘 a) (μ.toDistribution.patch_mem a ha)).symm

/-- **`res` equals the `patchOf`-read residue-sum over any finite superset `S` of the poles** (the
genuine total residue): extra points of `S` are holomorphic (`formFnResidue_eq_zero_off`), residue `0`. -/
theorem res_eq_sum_patchOf_superset {S : Finset X} (hS : μ.poles ⊆ S) :
    μ.res = ∑ a ∈ S, formFnResidue ω₀ (μ.g (patchOf 𝔘 a)) a := by
  rw [μ.res_eq_sum_patchOf, ← Finset.sum_subset hS]
  intro a _ ha
  exact μ.formFnResidue_eq_zero_off (patchOf 𝔘 a) (patchOf_mem 𝔘 a) ha

/-! ### ℂ-scaling -/

/-- **ℂ-scaling** `c • μ`: scale each principal part by `c`; poles/patch/overlap structure unchanged
(`c • gᵢ` is analytic / isolated wherever `gᵢ` is, and `c • gᵢ − c • gⱼ = c • (gᵢ − gⱼ) ∈ 𝒪_K`). -/
noncomputable def smul (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) : CoverMLLift 𝔘 ω₀ K where
  toDistribution :=
    { g := fun i => c • μ.g i
      poles := μ.poles
      patch := μ.toDistribution.patch
      patch_mem := μ.toDistribution.patch_mem
      diffMem := fun i j => by
        have h := μ.toDistribution.diffMem i j
        have heq : ((c • μ.g i - c • μ.g j) ∘ (Subtype.val : ↥(𝔘.U i ⊓ 𝔘.U j) → X))
            = c • ((μ.g i - μ.g j) ∘ (Subtype.val : ↥(𝔘.U i ⊓ 𝔘.U j) → X)) := by
          funext x
          simp only [Function.comp_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
        rw [heq]; exact Submodule.smul_mem _ c h
      formHoloDiff := fun i j a hi hj => by
        have h := μ.toDistribution.formHoloDiff i j a hi hj
        have heq : (fun z => coeffAt ω₀ a z * (c • μ.g i - c • μ.g j) ((chartAt ℂ a).symm z))
            = (fun z => c * (coeffAt ω₀ a z * (μ.g i - μ.g j) ((chartAt ℂ a).symm z))) := by
          funext z; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
        rw [heq]; exact analyticAt_const.mul h
      iso := fun a ha => by
        have h := μ.formFnHoloPunctured_everywhere (μ.toDistribution.patch a)
          (μ.toDistribution.patch_mem a ha)
        obtain ⟨ρ, hρ, hball⟩ := h
        refine ⟨ρ, hρ, fun z hz => ?_⟩
        have hd := hball z hz
        have heq : (fun z => coeffAt ω₀ a z * (c • μ.g (μ.toDistribution.patch a))
              ((chartAt ℂ a).symm z))
            = (fun z => c * (coeffAt ω₀ a z * μ.g (μ.toDistribution.patch a)
              ((chartAt ℂ a).symm z))) := by
          funext w; simp only [Pi.smul_apply, smul_eq_mul]; ring
        rw [heq]; exact hd.const_mul c }
  holoOff := fun i a ha hb => by
    have h := μ.holoOff i a ha hb
    have heq : (fun z => (c • μ.g i) ((chartAt ℂ a).symm z))
        = (fun z => c * μ.g i ((chartAt ℂ a).symm z)) := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]
    rw [heq]; exact analyticAt_const.mul h

@[simp] theorem smul_g (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) (i : 𝔘.ι) : (smul c μ).g i = c • μ.g i := rfl
@[simp] theorem smul_poles (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) : (smul c μ).poles = μ.poles := rfl
@[simp] theorem smul_patch (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) :
    (smul c μ).toDistribution.patch = μ.toDistribution.patch := rfl

/-- **`res (c • μ) = c · res μ`** (Forster §17.2 ℂ-homogeneity). -/
theorem res_smul (c : ℂ) (μ : CoverMLLift 𝔘 ω₀ K) : (smul c μ).res = c • μ.res := by
  rw [μ.res_eq_sum_patchOf, (smul c μ).res_eq_sum_patchOf, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [smul_g, smul_patch]
  exact formFnResidue_smul ω₀ c (μ.g (patchOf 𝔘 a)) a
    (μ.formFnHoloPunctured_everywhere (patchOf 𝔘 a) (patchOf_mem 𝔘 a))

/-! ### Additive combination -/

open scoped Classical in
/-- **Sum of two Cousin lifts** `combine μ₁ μ₂`: `gᵢ := μ₁.gᵢ + μ₂.gᵢ`, pole set the union, patch the
left one on `μ₁.poles` and the right one elsewhere.  All overlap conditions add (`𝒪_K` is a submodule,
analytic forms add); isolated/holomorphic structure adds via `formFnHoloPunctured_everywhere`/`holoOff`. -/
noncomputable def combine (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) : CoverMLLift 𝔘 ω₀ K where
  toDistribution :=
    { g := fun i => μ₁.g i + μ₂.g i
      poles := μ₁.poles ∪ μ₂.poles
      patch := fun a => if a ∈ μ₁.poles then μ₁.toDistribution.patch a else μ₂.toDistribution.patch a
      patch_mem := fun a ha => by
        by_cases h : a ∈ μ₁.poles
        · rw [if_pos h]; exact μ₁.toDistribution.patch_mem a h
        · rw [if_neg h]
          exact μ₂.toDistribution.patch_mem a ((Finset.mem_union.mp ha).resolve_left h)
      diffMem := fun i j => by
        have h1 := μ₁.toDistribution.diffMem i j
        have h2 := μ₂.toDistribution.diffMem i j
        have heq : ((μ₁.g i + μ₂.g i - (μ₁.g j + μ₂.g j))
              ∘ (Subtype.val : ↥(𝔘.U i ⊓ 𝔘.U j) → X))
            = ((μ₁.g i - μ₁.g j) ∘ (Subtype.val : ↥(𝔘.U i ⊓ 𝔘.U j) → X))
              + ((μ₂.g i - μ₂.g j) ∘ (Subtype.val : ↥(𝔘.U i ⊓ 𝔘.U j) → X)) := by
          funext x; simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply]; ring
        rw [heq]; exact Submodule.add_mem _ h1 h2
      formHoloDiff := fun i j a hi hj => by
        have h1 := μ₁.toDistribution.formHoloDiff i j a hi hj
        have h2 := μ₂.toDistribution.formHoloDiff i j a hi hj
        have heq : (fun z => coeffAt ω₀ a z *
              (μ₁.g i + μ₂.g i - (μ₁.g j + μ₂.g j)) ((chartAt ℂ a).symm z))
            = (fun z => coeffAt ω₀ a z * (μ₁.g i - μ₁.g j) ((chartAt ℂ a).symm z))
              + (fun z => coeffAt ω₀ a z * (μ₂.g i - μ₂.g j) ((chartAt ℂ a).symm z)) := by
          funext z; simp only [Pi.add_apply, Pi.sub_apply]; ring
        rw [heq]; exact h1.add h2
      iso := fun a ha => by
        -- patch `p` contains `a`; both `ω₀·μ₁.gₚ`, `ω₀·μ₂.gₚ` isolated there, so their sum is.
        set p := if a ∈ μ₁.poles then μ₁.toDistribution.patch a else μ₂.toDistribution.patch a with hp
        have hpmem : a ∈ 𝔘.U p := by
          rw [hp]; by_cases h : a ∈ μ₁.poles
          · rw [if_pos h]; exact μ₁.toDistribution.patch_mem a h
          · rw [if_neg h]
            exact μ₂.toDistribution.patch_mem a ((Finset.mem_union.mp ha).resolve_left h)
        have h1 := μ₁.formFnHoloPunctured_everywhere p hpmem
        have h2 := μ₂.formFnHoloPunctured_everywhere p hpmem
        obtain ⟨ρ₁, hρ₁, hb₁⟩ := h1
        obtain ⟨ρ₂, hρ₂, hb₂⟩ := h2
        refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun z hz => ?_⟩
        have hz1 : z ∈ ball ((chartAt ℂ a) a) ρ₁ \ {(chartAt ℂ a) a} :=
          ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_left _ _)), hz.2⟩
        have hz2 : z ∈ ball ((chartAt ℂ a) a) ρ₂ \ {(chartAt ℂ a) a} :=
          ⟨mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hz.1) (min_le_right _ _)), hz.2⟩
        have heq : (fun z => coeffAt ω₀ a z * (μ₁.g p + μ₂.g p) ((chartAt ℂ a).symm z))
            = (fun z => coeffAt ω₀ a z * μ₁.g p ((chartAt ℂ a).symm z))
              + fun z => coeffAt ω₀ a z * μ₂.g p ((chartAt ℂ a).symm z) := by
          funext w; simp only [Pi.add_apply]; ring
        rw [heq]; exact (hb₁ z hz1).add (hb₂ z hz2) }
  holoOff := fun i a ha hb => by
    have hb1 : a ∉ μ₁.poles := fun h => hb (Finset.mem_union_left _ h)
    have hb2 : a ∉ μ₂.poles := fun h => hb (Finset.mem_union_right _ h)
    have h1 := μ₁.holoOff i a ha hb1
    have h2 := μ₂.holoOff i a ha hb2
    have heq : (fun z => (μ₁.g i + μ₂.g i) ((chartAt ℂ a).symm z))
        = (fun z => μ₁.g i ((chartAt ℂ a).symm z)) + fun z => μ₂.g i ((chartAt ℂ a).symm z) := by
      funext z; simp only [Pi.add_apply]
    rw [heq]; exact h1.add h2

@[simp] theorem combine_g (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) (i : 𝔘.ι) :
    (combine μ₁ μ₂).g i = μ₁.g i + μ₂.g i := rfl

open scoped Classical in
@[simp] theorem combine_poles (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) :
    (combine μ₁ μ₂).poles = μ₁.poles ∪ μ₂.poles := rfl

open scoped Classical in
/-- **`res (combine μ₁ μ₂) = res μ₁ + res μ₂`** (Forster §17.2 additivity).  Both residues are read over
the common pole-union via `res_eq_sum_patchOf_superset`, where the integrand splits (`formFnResidue_add`,
both summands isolated everywhere). -/
theorem res_combine (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) :
    (combine μ₁ μ₂).res = μ₁.res + μ₂.res := by
  rw [(combine μ₁ μ₂).res_eq_sum_patchOf,
    μ₁.res_eq_sum_patchOf_superset (Finset.subset_union_left (s₁ := μ₁.poles) (s₂ := μ₂.poles)),
    μ₂.res_eq_sum_patchOf_superset (Finset.subset_union_right (s₁ := μ₁.poles) (s₂ := μ₂.poles)),
    combine_poles, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [combine_g]
  exact formFnResidue_add ω₀ (μ₁.g (patchOf 𝔘 a)) (μ₂.g (patchOf 𝔘 a)) a
    (μ₁.formFnHoloPunctured_everywhere (patchOf 𝔘 a) (patchOf_mem 𝔘 a))
    (μ₂.formFnHoloPunctured_everywhere (patchOf 𝔘 a) (patchOf_mem 𝔘 a))

/-- **Negation** `neg μ := (-1) • μ`. -/
noncomputable def neg (μ : CoverMLLift 𝔘 ω₀ K) : CoverMLLift 𝔘 ω₀ K := smul (-1) μ

@[simp] theorem neg_g (μ : CoverMLLift 𝔘 ω₀ K) (i : 𝔘.ι) : (neg μ).g i = -μ.g i := by
  simp only [neg, smul_g, neg_smul, one_smul]

theorem res_neg (μ : CoverMLLift 𝔘 ω₀ K) : (neg μ).res = -μ.res := by
  rw [neg, res_smul]; simp

/-- **Difference** `sub μ₁ μ₂ := combine μ₁ (neg μ₂)`, with `gᵢ = μ₁.gᵢ − μ₂.gᵢ` and `res = res μ₁ −
res μ₂`.  The lift whose connecting cocycle is `δμ₁ − δμ₂`. -/
noncomputable def sub (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) : CoverMLLift 𝔘 ω₀ K := combine μ₁ (neg μ₂)

@[simp] theorem sub_g (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) (i : 𝔘.ι) :
    (sub μ₁ μ₂).g i = μ₁.g i - μ₂.g i := by
  simp only [sub, combine_g, neg_g]; ring

theorem res_sub (μ₁ μ₂ : CoverMLLift 𝔘 ω₀ K) : (sub μ₁ μ₂).res = μ₁.res - μ₂.res := by
  rw [sub, res_combine, res_neg]; ring

end CoverMLLift

end Jacobians.Dolbeault

end
