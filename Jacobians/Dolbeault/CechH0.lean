/-
  Dolbeault ladder — the `h⁰ = l(D)` bridge leaf (`h0Dim_eq_lDim`).

  The Čech `H⁰(𝔘, 𝒪_D)` (global matching germ-class sections over a finite cover) is identified with
  the Riemann–Roch linear system `L(D) = linearSystem D` modulo its germ-zero junk. Concretely we
  build a `ℂ`-linear equivalence `L(D) ⧸ germZero ≃ₗ globalSections D` and read off the `finrank`s.

  Math content (the two non-formal pieces):
  * **keystone** `ordU_val_eq_orderW`: the order of a global meromorphic `F` restricted to the open
    submanifold `↥U` (computed in `↥U`'s own chart, `ordU`) equals its global order `orderW F`. Both
    charts are `subtypeRestr`s of the *same* ambient `chartAt ℂ x` (`Opens.chartAt_eq`), exactly as
    `CechSection.restrict_chart_aux`.
  * **gluing** (surjectivity): a matching family of germ-classes glues to a global `MeromorphicFunction`.
    NOTE (correctness): the naive pointwise patch `x ↦ g (idx x) x` is *not* meromorphic at
    cover-boundary points (the per-overlap disagreement set is only codiscrete *within* the overlap, so
    it can accumulate at a boundary point `y ∉ U j`). The fix is to rigidify the representatives via the
    meromorphic normal form read in the shared ambient chart, so they agree *honestly* (not just
    codiscretely) on overlaps; the patch is then chart-locally a single normal-form function.
-/
import Jacobians.Dolbeault.CechComplex

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Keystone: local order on `↥U` = global order on `X` -/

/-- Base-point and chart-pullback agreement between `↥U`'s chart at `u` and `X`'s chart at `u.1`:
`↥U`'s chart is the `subtypeRestr` of the *same* ambient chart `chartAt ℂ u.1` (`Opens.chartAt_eq`),
so it reads any `F : X → ℂ` at the same ambient point near `u`. The `↥U ↪ X` analogue of
`restrict_chart_aux`. -/
private theorem incl_chart_aux {U : Opens X} (F : X → ℂ) (u : U) :
    (chartAt (H := ℂ) u) u = (chartAt (H := ℂ) u.1) u.1 ∧
    ((F ∘ Subtype.val) ∘ (chartAt (H := ℂ) u).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) u) u)]
      (F ∘ (chartAt (H := ℂ) u.1).symm) := by
  have hbase : (chartAt (H := ℂ) u) u = (chartAt (H := ℂ) u.1) u.1 := by
    simp only [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe,
      Set.restrict_apply]
  refine ⟨hbase, ?_⟩
  have ht1 : (chartAt (H := ℂ) u).target ∈ 𝓝 ((chartAt (H := ℂ) u) u) :=
    (chartAt (H := ℂ) u).open_target.mem_nhds
      ((chartAt (H := ℂ) u).map_source (mem_chart_source ℂ u))
  refine Filter.eventuallyEq_of_mem ht1 fun w hw => ?_
  show F (((chartAt (H := ℂ) u).symm w : U) : X) = F ((chartAt (H := ℂ) u.1).symm w)
  congr 1
  have e1 : ((chartAt (H := ℂ) u).symm w).1 = (chartAt (H := ℂ) u.1).symm w := by
    simpa [Function.comp] using
      OpenPartialHomeomorph.subtypeRestr_symm_apply (e := chartAt (H := ℂ) u.1) ⟨u⟩ hw
  rw [e1]

/-- **Keystone.** The order of `F` restricted to the open submanifold `↥U` (in `↥U`'s chart) equals
the global order `orderW F` at the corresponding point. -/
theorem ordU_val_eq_orderW {U : Opens X} (F : MeromorphicFunction X) (u : U) :
    ordU (F.toFun ∘ Subtype.val) u = F.orderW u.1 := by
  obtain ⟨hbase, hev⟩ := incl_chart_aux F.toFun u
  rw [ordU, MeromorphicFunction.orderW, hbase]
  exact meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)

/-- `F : X → ℂ` meromorphic on `X` restricts to a meromorphic function on the open submanifold `↥U`. -/
theorem isMeromorphic_val {U : Opens X} (F : MeromorphicFunction X) :
    IsMeromorphic (U : Type _) (F.toFun ∘ Subtype.val) := by
  intro u
  obtain ⟨hbase, hev⟩ := incl_chart_aux F.toFun u
  have hmer := F.meromorphic u.1
  rw [← hbase] at hmer
  exact hmer.congr (hev.filter_mono nhdsWithin_le_nhds).symm

/-! ### Germ-vanishing ↔ order `⊤` (the kernel characterisation) -/

/-- Chart-transport of an eventually-property across `𝓝[≠]`, for *any* `ℂ`-charted space `Y` (the
repo's `eventually_comp_chart_iff` carries spurious `CompactSpace`/`ConnectedSpace`; the open
submanifold `↥U` has neither). Proof copied verbatim — uses only the chart's local-homeo structure. -/
theorem eventually_comp_chart_iff' {Y : Type*} [TopologicalSpace Y] [ChartedSpace ℂ Y]
    (g : Y → ℂ) (y : Y) (P : ℂ → Prop) :
    (∀ᶠ w in 𝓝[≠] ((chartAt (H := ℂ) y) y), P ((g ∘ (chartAt (H := ℂ) y).symm) w))
      ↔ ∀ᶠ z in 𝓝[≠] y, P (g z) := by
  have hy : y ∈ (chartAt (H := ℂ) y).source := mem_chart_source ℂ y
  have hyt : (chartAt (H := ℂ) y) y ∈ (chartAt (H := ℂ) y).target :=
    (chartAt (H := ℂ) y).map_source hy
  have hey : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) = y :=
    (chartAt (H := ℂ) y).left_inv hy
  rw [eventually_nhdsWithin_iff, eventually_nhdsWithin_iff]
  constructor
  · intro h
    have h2 := ((chartAt (H := ℂ) y).continuousAt hy).eventually h
    filter_upwards [h2, (chartAt (H := ℂ) y).open_source.mem_nhds hy] with z hz hz_src
    intro hz_mem
    have hz_ne : z ≠ y := hz_mem
    have hchart : (chartAt (H := ℂ) y) z ∈ ({(chartAt (H := ℂ) y) y} : Set ℂ)ᶜ :=
      fun heq => hz_ne ((chartAt (H := ℂ) y).injOn hz_src hy heq)
    have := hz hchart
    rwa [Function.comp_apply, (chartAt (H := ℂ) y).left_inv hz_src] at this
  · intro h
    have hsymm : ContinuousAt (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) :=
      (chartAt (H := ℂ) y).continuousAt_symm hyt
    have h2 := hsymm.eventually (p := fun z => z ∈ ({y} : Set Y)ᶜ → P (g z)) (by rw [hey]; exact h)
    filter_upwards [h2, (chartAt (H := ℂ) y).open_target.mem_nhds hyt] with w hw hw_tgt
    intro hw_mem
    have hw_ne : w ≠ (chartAt (H := ℂ) y) y := hw_mem
    have hsymm_ne : (chartAt (H := ℂ) y).symm w ∈ ({y} : Set Y)ᶜ := by
      intro heq
      apply hw_ne
      have hr := (chartAt (H := ℂ) y).right_inv hw_tgt
      rw [Set.mem_singleton_iff.mp heq] at hr
      exact hr.symm
    have := hw hsymm_ne
    rw [Function.comp_apply]; exact this

/-- `ordU g u = ⊤` iff `g` vanishes throughout a punctured neighbourhood of `u` on `↥U`. -/
theorem ordU_eq_top_iff {U : Opens X} (g : U → ℂ) (u : U) :
    ordU g u = ⊤ ↔ ∀ᶠ z in 𝓝[≠] u, g z = 0 := by
  rw [ordU, meromorphicOrderAt_eq_top_iff]
  exact eventually_comp_chart_iff' g u (· = 0)

/-- The germ-class of `g` is `0` iff `g` vanishes near every point (punctured) — i.e. `g` is
germ-zero junk. This is the codiscrete ⟺ `∀ 𝓝[≠]` bridge (here on `T = univ`, so it needs no
meromorphy). -/
theorem toGerm_eq_zero_iff {U : Opens X} (g : U → ℂ) :
    toGerm U g = 0 ↔ ∀ u : U, ∀ᶠ z in 𝓝[≠] u, g z = 0 := by
  show (g : MGerm U) = 0 ↔ _
  rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
  rw [Filter.EventuallyEq, Filter.Eventually, mem_codiscreteWithin_iff_forall_mem_nhdsNE]
  simp only [Pi.zero_apply, Set.mem_univ, forall_const, Set.compl_univ, Set.union_empty]
  rfl

/-! ### Extension-by-zero of an `↥U`-section and the `↥U ↔ X` chart bridge

For the gluing crux we need to talk about a section `g : ↥U → ℂ` as a function on the *ambient* `X`,
so that the per-point normal form (read in `X`'s chart) makes sense. `Gext g` extends `g` by `0`;
`Gext_chart_bridge` is the `↥U ↔ X` chart-pullback agreement (the `Gext` analogue of
`incl_chart_aux`), from which meromorphy / order / normal-form on `X` all transfer from `↥U`. -/

open Classical in
/-- Extend a section on the open submanifold `↥U` by `0` to a function on the whole space `X`. -/
noncomputable def Gext {U : Opens X} (g : U → ℂ) : X → ℂ :=
  fun x => if hx : x ∈ U then g ⟨x, hx⟩ else 0

theorem Gext_comp_val {U : Opens X} (g : U → ℂ) :
    (Gext g) ∘ (Subtype.val : U → X) = g := by
  funext u; simp only [Function.comp_apply, Gext, dif_pos u.2]

theorem Gext_apply_mem {U : Opens X} (g : U → ℂ) {x : X} (hx : x ∈ U) :
    Gext g x = g ⟨x, hx⟩ := by simp only [Gext, dif_pos hx]

/-- The base point and chart-pullback agree between `↥U`'s chart at `⟨y⟩` and `X`'s chart at `y` for
`y ∈ U`: both are `subtypeRestr`s of the *same* ambient chart `chartAt ℂ y` (`Opens.chartAt_eq`), and
`Gext g` agrees with `g` near `y` (the point and its neighbours lie in `U`). The `Gext` analogue of
`incl_chart_aux`. -/
theorem Gext_chart_bridge {U : Opens X} (g : U → ℂ) {y : X} (hy : y ∈ U) :
    (chartAt (H := ℂ) (⟨y, hy⟩ : U)) ⟨y, hy⟩ = (chartAt (H := ℂ) y) y ∧
    (g ∘ (chartAt (H := ℂ) (⟨y, hy⟩ : U)).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) y) y)]
      (Gext g ∘ (chartAt (H := ℂ) y).symm) := by
  set u : U := ⟨y, hy⟩ with hu
  have hbase : (chartAt (H := ℂ) u) u = (chartAt (H := ℂ) y) y := by
    simp only [hu, TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe,
      Set.restrict_apply]
  refine ⟨hbase, ?_⟩
  have ht1 : (chartAt (H := ℂ) u).target ∈ 𝓝 ((chartAt (H := ℂ) u) u) :=
    (chartAt (H := ℂ) u).open_target.mem_nhds
      ((chartAt (H := ℂ) u).map_source (mem_chart_source ℂ u))
  rw [hbase] at ht1
  refine Filter.eventuallyEq_of_mem ht1 fun w hw => ?_
  show g ((chartAt (H := ℂ) u).symm w) = Gext g ((chartAt (H := ℂ) y).symm w)
  have e1 : ((chartAt (H := ℂ) u).symm w).1 = (chartAt (H := ℂ) y).symm w := by
    simpa [Function.comp] using
      OpenPartialHomeomorph.subtypeRestr_symm_apply (e := chartAt (H := ℂ) y) ⟨u⟩ hw
  have hmem : (chartAt (H := ℂ) y).symm w ∈ U := e1 ▸ ((chartAt (H := ℂ) u).symm w).2
  rw [show Gext g ((chartAt (H := ℂ) y).symm w) = g ⟨(chartAt (H := ℂ) y).symm w, hmem⟩ from by
    simp only [Gext, dif_pos hmem]]
  congr 1
  exact Subtype.ext e1

/-- `Gext g` is meromorphic at `y ∈ U` (in `X`'s chart), given `g` meromorphic on `↥U`. -/
theorem Gext_meromorphicAt {U : Opens X} {g : U → ℂ} (hg : IsMeromorphic (U : Type _) g)
    {y : X} (hy : y ∈ U) :
    MeromorphicAt (Gext g ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) := by
  obtain ⟨hbase, hev⟩ := Gext_chart_bridge g hy
  have hmer := hg ⟨y, hy⟩
  rw [hbase] at hmer
  exact hmer.congr (hev.filter_mono nhdsWithin_le_nhds)

/-- The intrinsic order on `↥U` (`ordU g`) equals the order of `Gext g` read in `X`'s chart. -/
theorem ordU_eq_orderAt_Gext {U : Opens X} (g : U → ℂ) {y : X} (hy : y ∈ U) :
    ordU g ⟨y, hy⟩ =
      meromorphicOrderAt (Gext g ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) := by
  obtain ⟨hbase, hev⟩ := Gext_chart_bridge g hy
  rw [ordU, hbase]
  exact meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)

/-- The "normal form at `y`" predicate intrinsic to `X`: `h` read in `X`'s chart at `y` has
meromorphic normal form at the chart centre. -/
def nfX (h : X → ℂ) (y : X) : Prop :=
  MeromorphicNFAt (h ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y)

/-- `Gext g` is in normal form at `y ∈ U` iff `g` is (read in `↥U`'s chart at `⟨y⟩`). -/
theorem nfX_Gext_iff {U : Opens X} (g : U → ℂ) {y : X} (hy : y ∈ U) :
    nfX (Gext g) y ↔
      MeromorphicNFAt (g ∘ (chartAt (H := ℂ) (⟨y, hy⟩ : U)).symm)
        ((chartAt (H := ℂ) (⟨y, hy⟩ : U)) ⟨y, hy⟩) := by
  obtain ⟨hbase, hev⟩ := Gext_chart_bridge g hy
  rw [nfX, hbase, meromorphicNFAt_congr hev]

/-! ### The forward map `L(D) → H⁰(𝔘, 𝒪_D)` -/

namespace FiniteCover

variable (𝔘 : FiniteCover X) (D : Divisor X)

/-- Restrict a global meromorphic function to the cover's germ-class 0-cochains:
`F ↦ (i ↦ [F|_{U i}])`. `ℂ`-linear (depends only on the cover, not on `D`). -/
noncomputable def cechRestrict : MeromorphicFunction X →ₗ[ℂ] 𝔘.Cochain0 where
  toFun F i := toGerm (𝔘.U i) (F.toFun ∘ Subtype.val)
  map_add' F G := by funext i; exact (map_add (toGerm (𝔘.U i)) _ _)
  map_smul' c F := by funext i; exact (map_smul (toGerm (𝔘.U i)) _ _)

@[simp] theorem cechRestrict_apply (F : MeromorphicFunction X) (i : 𝔘.ι) :
    𝔘.cechRestrict F i = toGerm (𝔘.U i) (F.toFun ∘ Subtype.val) := rfl

/-- The restriction of `F ∈ L(D)` is a global matching `𝒪_D`-section: each component is an
`𝒪_D`-germ (keystone: `ordU = orderW ≥ −D`), and the components match on overlaps automatically
(both restrict the *same* `F`). -/
theorem cechRestrict_mem_globalSections {F : MeromorphicFunction X}
    (hF : F ∈ linearSystem D) : 𝔘.cechRestrict F ∈ 𝔘.globalSections D := by
  rw [globalSections, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · -- matching: `cechRestrict F ∈ ker δ⁰`
    rw [LinearMap.mem_ker]
    funext p
    obtain ⟨i, j⟩ := p
    simp only [cechDelta0, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, cechRestrict_apply, rawRestrictG_coe, Pi.zero_apply]
    rw [sub_eq_zero]
    rfl
  · -- sections: each component is an `𝒪_D`-germ
    intro i
    refine ⟨F.toFun ∘ Subtype.val, ⟨isMeromorphic_val F, fun u => ?_⟩, rfl⟩
    rw [ordU_val_eq_orderW]
    exact hF u.1

/-- The forward map `Φ : L(D) →ₗ globalSections D` (domain/codomain restriction of `cechRestrict`). -/
noncomputable def cechRestrictL :
    linearSystem (X := X) D →ₗ[ℂ] ↥(𝔘.globalSections D) :=
  ((𝔘.cechRestrict).domRestrict (linearSystem D)).codRestrict (𝔘.globalSections D)
    fun F => 𝔘.cechRestrict_mem_globalSections D F.2

@[simp] theorem cechRestrictL_coe (F : linearSystem (X := X) D) :
    (𝔘.cechRestrictL D F : 𝔘.Cochain0) = 𝔘.cechRestrict (F : MeromorphicFunction X) := rfl

/-- The restriction of `F` is the zero cochain iff `F` is germ-zero junk everywhere (`orderW ≡ ⊤`).
Uses the keystone (`ordU = orderW`), the germ-zero bridge, and that the `U i` cover `X`. -/
theorem cechRestrict_eq_zero_iff (F : MeromorphicFunction X) :
    𝔘.cechRestrict F = 0 ↔ ∀ x, F.orderW x = ⊤ := by
  rw [funext_iff]
  simp only [cechRestrict_apply, Pi.zero_apply, toGerm_eq_zero_iff, ← ordU_eq_top_iff,
    ordU_val_eq_orderW]
  constructor
  · intro h x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (𝔘.covers ▸ Set.mem_univ x :
      x ∈ ⨆ i, 𝔘.U i)
    exact h i ⟨x, hi⟩
  · intro h i u
    exact h u.1

/-- The kernel of the descended forward map is exactly the germ-zero junk: `Φ` descends to an
*injective* map `L(D) ⧸ germZero ↪ H⁰`. -/
theorem ker_cechRestrictL :
    LinearMap.ker (𝔘.cechRestrictL D) = (germZeroSubmodule).submoduleOf (linearSystem D) := by
  ext F
  rw [LinearMap.mem_ker, ← Submodule.coe_eq_zero, cechRestrictL_coe,
    𝔘.cechRestrict_eq_zero_iff]
  exact Iff.rfl

/-! ### Gluing (surjectivity) — the crux -/

/-- **Gluing.** Every global matching `𝒪_D`-section over the cover glues to a single global
meromorphic function in `L(D)`.

CONSTRUCTION (rigidified normal-form gluing; the naive pointwise patch `x ↦ g_{idx x} x` is *not*
meromorphic at cover-boundary points because the per-overlap disagreement set is only codiscrete
*within* the overlap). Extract honest representatives `g i ∈ OmegaD D (U i)` with `[g i] = f i`
(choice on `OmegaDGerm = map toGerm`). Extend each by `0` to `Gext i : X → ℂ`. Define

  `F.toFun x := toMeromorphicNFAt (Gext (idx x) ∘ (chartAt ℂ x).symm) (chartAt ℂ x x) (chartAt ℂ x x)`

(the per-point normal-form value; `idx x` any index with `x ∈ U i`).
  * **idx-independent**: the nf value at `x` depends only on the germ at `x`; the matching gives
    `Gext i =ᶠ[𝓝[≠] x] Gext j` on overlaps, so (read in the shared chart `chartAt ℂ x`) the nf values
    agree by NF-uniqueness (`MeromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds`).
  * **`F =ᶠ[𝓝[≠] y] Gext i` for `y ∈ U i`**: the normal form repairs only a *codiscrete* set
    (`analyticAt_mem_codiscreteWithin`; `toMeromorphicNFAt = id` on nf-points,
    `eq_nhdsNE_toMeromorphicNFAt`), so `F` and `Gext i` agree off a discrete set ⟹ `F` meromorphic at
    `y` and (keystone `ordU = orderW`) `orderW F ≥ −D` ⟹ `F ∈ L(D)`; and `[F|_{U i}] = [g i] = f i`. -/
theorem cechRestrictL_surjective : Function.Surjective (𝔘.cechRestrictL D) := by
  sorry

/-- `H⁰(𝔘, 𝒪_D) ≅ L(D) ⧸ germZero` as `ℂ`-modules (first isomorphism theorem + `ker = germZero`). -/
noncomputable def globalSectionsEquivQuot :
    (linearSystem (X := X) D ⧸ (germZeroSubmodule (X := X)).submoduleOf (linearSystem D))
      ≃ₗ[ℂ] ↥(𝔘.globalSections D) :=
  (Submodule.quotEquivOfEq _ _ (𝔘.ker_cechRestrictL D).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (𝔘.cechRestrictL_surjective D))

/-- **The bridge leaf** `h⁰(𝔘, 𝒪_D) = l(D)` — Čech global sections agree with the linear system. -/
theorem h0Dim_eq_lDim (D : Divisor X) : 𝔘.h0Dim D = lDim D := by
  rw [h0Dim, lDim]
  exact ((𝔘.globalSectionsEquivQuot D).finrank_eq).symm

end FiniteCover

end Jacobians.Dolbeault
