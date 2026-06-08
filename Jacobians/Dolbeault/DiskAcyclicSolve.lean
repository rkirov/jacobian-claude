/-
  Dolbeault ladder — **Forster 13.4**: genuine disk-acyclicity `H¹(disk, 𝒪) = 0` for a shared-chart
  cover whose chart-images fill the ball, built from the open-disk ∂̄-solver (Forster 13.2,
  `DbarOpenDisk.dbar_solvable_open_disk`).

  This is the sound replacement for the stalled `HasGluedDbarDatum` route: instead of a Bott–Tu
  partition-of-unity datum (which sums to `1` only on a closed core), we use the **open-union**
  partition of unity `coverOpenUnionPoU` (which sums to `1` on all of `↥(⋃Uᵢ)`), whose chart-read
  primitive `openChartPrim` therefore telescopes on EVERY overlap. Its `∂̄` glues to a datum smooth on
  the union's chart-image; when that image is the full ball, Forster 13.2 solves `∂̄u = ω` there, and
  `η̂ᵢ = openChartPrimᵢ − u` are the holomorphic correctors that `analyticAt_compChart_of_differentiableOn`
  turns into `HasChartAnalyticCorrectors` ⟹ `H¹(disk,𝒪)=0`.
-/
import Jacobians.Dolbeault.CechFinitenessBallSolve
import Jacobians.Dolbeault.DbarOpenDisk

open scoped Manifold ContDiff Topology
open Complex Metric Filter
open TopologicalSpace (Opens)

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault
namespace SharedChartCover

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- If `z` is in the chart-image of the open union, its chart-preimage lands in the open union. -/
theorem symm_mem_openUnionU (𝔇 : SharedChartCover X) {z : ℂ} (hz : z ∈ openUnionChartImage 𝔇) :
    (𝔇.φ).symm z ∈ openUnionU 𝔇 := by
  rcases hz with ⟨x, hxU, hxz⟩
  have hsrc : x ∈ (chartAt (H := ℂ) 𝔇.center).source := by
    rcases Set.mem_iUnion.mp hxU with ⟨j, hxj⟩; exact 𝔇.subset_source j hxj
  have hsymm : (chartAt (H := ℂ) 𝔇.center).symm z = x := by
    simpa [hxz] using (chartAt (H := ℂ) 𝔇.center).left_inv hsrc
  show (chartAt (H := ℂ) 𝔇.center).symm z ∈ (openUnionU 𝔇 : Set X)
  rw [hsymm]; exact hxU

/-- The chart-read of the open-union primitive (`ℂ → ℂ`, junk off the union's chart-image). -/
noncomputable def openChartPrim (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) (i : 𝔇.ι) : ℂ → ℂ := by
  classical
  exact fun z => if h : z ∈ openUnionChartImage 𝔇 then
    openUnionCoverPrim 𝔇 s i ⟨(𝔇.φ).symm z, symm_mem_openUnionU 𝔇 h⟩ else 0

/-- On the union's chart-image, `openChartPrim` reads the open-union primitive. -/
theorem openChartPrim_apply_mem (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) (i : 𝔇.ι) {z : ℂ}
    (hz : z ∈ openUnionChartImage 𝔇) :
    openChartPrim 𝔇 s i z = openUnionCoverPrim 𝔇 s i ⟨(𝔇.φ).symm z, symm_mem_openUnionU 𝔇 hz⟩ := by
  simp only [openChartPrim, hz, dif_pos]

/-- **The chart-read difference identity** (holds on EVERY overlap, since the open-union PoU sums to
`1` everywhere — no closed-core restriction).  For `x ∈ Uᵢ ⊓ Uⱼ`,
`openChartPrimⱼ(φx) − openChartPrimᵢ(φx) = holoFn(sᵢⱼ) x`. -/
theorem openChartPrim_diff (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) (i j : 𝔇.ι) {x : X}
    (hx : x ∈ (𝔇.toFiniteFamily.U i ⊓ 𝔇.toFiniteFamily.U j : Opens X)) :
    openChartPrim 𝔇 s j (𝔇.φ x) - openChartPrim 𝔇 s i (𝔇.φ x)
      = holoFn (cocycleComp_mem 𝔇.toFiniteFamily s i j) x := by
  have hxU : x ∈ ⋃ k, (𝔇.U k : Set X) := Set.mem_iUnion.mpr ⟨i, hx.1⟩
  have hxim : 𝔇.φ x ∈ openUnionChartImage 𝔇 := ⟨x, hxU, rfl⟩
  have hsrc : x ∈ (chartAt (H := ℂ) 𝔇.center).source := 𝔇.subset_source i hx.1
  have hsymm : (𝔇.φ).symm (𝔇.φ x) = x := (chartAt (H := ℂ) 𝔇.center).left_inv hsrc
  rw [openChartPrim_apply_mem 𝔇 s j hxim, openChartPrim_apply_mem 𝔇 s i hxim]
  have hpt : (⟨(𝔇.φ).symm (𝔇.φ x), symm_mem_openUnionU 𝔇 hxim⟩ : ↥(openUnionU 𝔇))
      = ⟨x, hxU⟩ := Subtype.ext hsymm
  rw [hpt]
  exact openUnionCoverPrim_diff 𝔇 s i j (x := ⟨x, hxU⟩) hx

/-! ## Step 1 — `openChartPrim` is real-`C^∞` on `Ω_i`

The chart-read open-union primitive is `ContDiffAt ℝ ⊤` at every point of `Ω_i = φ '' U_i`.  We
transfer the manifold smoothness `contMDiffAt_openUnionCoverPrim` (on the open submanifold
`↥(openUnionU 𝔇)`) through the chart `φ.symm` and the open-submanifold inclusion: the lift
`z ↦ ⟨φ.symm z, _⟩` is `ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ)` (its `Subtype.val`-composition is `φ.symm`, smooth
by `contMDiffOn_chart_symm`, so `contMDiffAt_subtype_iff` lifts it into the subtype), and `openChartPrim`
equals `openUnionCoverPrim ∘ lift` near `φ x` (where `φ x ∈ openUnionChartImage`, an open set). -/

/-- The chart-image of the open union is open in `ℂ` (`φ` is an `OpenPartialHomeomorph` and
`openUnionU 𝔇 ⊆ φ.source`). -/
theorem isOpen_openUnionChartImage (𝔇 : SharedChartCover X) :
    IsOpen (openUnionChartImage 𝔇) := by
  refine (chartAt (H := ℂ) 𝔇.center).isOpen_image_of_subset_source (openUnionU 𝔇).isOpen ?_
  rintro x hx
  rcases Set.mem_iUnion.mp hx with ⟨j, hxj⟩
  exact 𝔇.subset_source j hxj

/-- The chart-image of the open union sits inside the chart target. -/
theorem openUnionChartImage_subset_target (𝔇 : SharedChartCover X) :
    openUnionChartImage 𝔇 ⊆ (𝔇.φ).target := by
  rintro z ⟨x, hxU, rfl⟩
  rcases Set.mem_iUnion.mp hxU with ⟨j, hxj⟩
  exact (𝔇.φ).map_source (𝔇.subset_source j hxj)

/-- The lift `ℂ → ↥(openUnionU 𝔇)`, `z ↦ ⟨φ.symm z, _⟩` on the open-union chart image, junking to a
supplied basepoint `p` elsewhere.  Only its germ near a point of `openUnionChartImage` is used; the
basepoint makes it total without a separate inhabitation argument. -/
noncomputable def liftSymm (𝔇 : SharedChartCover X) (p : ↥(openUnionU 𝔇)) (z : ℂ) :
    ↥(openUnionU 𝔇) := by
  classical
  exact if h : z ∈ openUnionChartImage 𝔇 then ⟨(𝔇.φ).symm z, symm_mem_openUnionU 𝔇 h⟩ else p

/-- On the open-union chart image, `liftSymm` is the genuine chart-preimage lift. -/
theorem liftSymm_apply_mem (𝔇 : SharedChartCover X) (p : ↥(openUnionU 𝔇)) {z : ℂ}
    (hz : z ∈ openUnionChartImage 𝔇) :
    liftSymm 𝔇 p z = ⟨(𝔇.φ).symm z, symm_mem_openUnionU 𝔇 hz⟩ := by
  simp only [liftSymm, hz, dif_pos]

/-- **`liftSymm` is `ContMDiffAt`** at every point of the (open) open-union chart image.  Its
`Subtype.val`-composition equals `φ.symm` near `z₀` (`liftSymm_apply_mem` on the open
`openUnionChartImage`), which is `ContMDiffAt` (chart-symm smoothness); `contMDiffAt_subtype_iff`
lifts it into the subtype. -/
theorem contMDiffAt_liftSymm (𝔇 : SharedChartCover X) (p : ↥(openUnionU 𝔇)) {z₀ : ℂ}
    (hz₀ : z₀ ∈ openUnionChartImage 𝔇) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (liftSymm 𝔇 p) z₀ := by
  have hz₀tgt : z₀ ∈ (𝔇.φ).target := openUnionChartImage_subset_target 𝔇 hz₀
  -- `φ.symm` is `ContMDiffAt` at `z₀`.
  have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (𝔇.φ).symm z₀ :=
    (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := 𝔇.center) _ hz₀tgt).contMDiffAt
      ((𝔇.φ).open_target.mem_nhds hz₀tgt)
  -- `Subtype.val ∘ liftSymm =ᶠ[𝓝 z₀] φ.symm` (on the open chart image).
  have hval : (Subtype.val ∘ liftSymm 𝔇 p) =ᶠ[𝓝 z₀] (𝔇.φ).symm := by
    filter_upwards [(isOpen_openUnionChartImage 𝔇).mem_nhds hz₀] with z hz
    simp only [Function.comp_apply, liftSymm_apply_mem 𝔇 p hz]
  have hval' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (Subtype.val ∘ liftSymm 𝔇 p) z₀ :=
    hsymm.congr_of_eventuallyEq hval
  exact (ContMDiffAt.subtypeVal_comp_iff (openUnionU 𝔇) (liftSymm 𝔇 p) z₀).1 hval'

/-- **Step 1 — `openChartPrim 𝔇 s i` is `ContDiffAt ℝ ⊤` on `Ω_i`.**  For `x ∈ U_i`, the chart point
`φ x` lies in `openUnionChartImage`, where `openChartPrim 𝔇 s i = openUnionCoverPrim 𝔇 s i ∘ liftSymm`;
the lift is `ContMDiffAt` (`contMDiffAt_liftSymm`) and the open-union primitive is `ContMDiffAt` over
`U_i` (`contMDiffAt_openUnionCoverPrim`), so the composite is, and `contMDiffAt_iff_contDiffAt`
bridges to `ContDiffAt ℝ`. -/
theorem contDiffAt_openChartPrim (𝔇 : SharedChartCover X)
    (s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X))) (i : 𝔇.ι) {x : X} (hx : x ∈ 𝔇.U i) :
    ContDiffAt ℝ (⊤ : ℕ∞) (openChartPrim 𝔇 s i) (𝔇.φ x) := by
  have hxU : (x : X) ∈ ⋃ k, (𝔇.U k : Set X) := Set.mem_iUnion.mpr ⟨i, hx⟩
  set p : ↥(openUnionU 𝔇) := ⟨x, hxU⟩ with hpdef
  have hsrc : x ∈ (chartAt (H := ℂ) 𝔇.center).source := 𝔇.subset_source i hx
  have hxim : 𝔇.φ x ∈ openUnionChartImage 𝔇 := ⟨x, hxU, rfl⟩
  -- The lift `liftSymm 𝔇 p` is `ContMDiffAt` at `φ x`.
  have hlift : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (liftSymm 𝔇 p) (𝔇.φ x) :=
    contMDiffAt_liftSymm 𝔇 p hxim
  -- `liftSymm 𝔇 p (φ x) = ⟨x, hxU⟩ = p` (so the open-union primitive is smooth at the lift value).
  have hsymm_pt : (𝔇.φ).symm (𝔇.φ x) = x := (chartAt (H := ℂ) 𝔇.center).left_inv hsrc
  have hlift_pt : liftSymm 𝔇 p (𝔇.φ x) = p := by
    rw [liftSymm_apply_mem 𝔇 p hxim]; exact Subtype.ext hsymm_pt
  -- The open-union primitive is `ContMDiffAt` at `p` (point over `U_i`).
  have hprim : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (openUnionCoverPrim 𝔇 s i) p :=
    contMDiffAt_openUnionCoverPrim 𝔇 s i (x₀ := p) hx
  -- Compose, then read `openChartPrim = openUnionCoverPrim ∘ liftSymm` near `φ x`.
  have hcomp : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (openUnionCoverPrim 𝔇 s i ∘ liftSymm 𝔇 p) (𝔇.φ x) :=
    (hlift_pt ▸ hprim).comp (𝔇.φ x) hlift
  have heq : openChartPrim 𝔇 s i =ᶠ[𝓝 (𝔇.φ x)] (openUnionCoverPrim 𝔇 s i ∘ liftSymm 𝔇 p) := by
    filter_upwards [(isOpen_openUnionChartImage 𝔇).mem_nhds hxim] with z hz
    rw [openChartPrim_apply_mem 𝔇 s i hz, Function.comp_apply, liftSymm_apply_mem 𝔇 p hz]
  exact contMDiffAt_iff_contDiffAt.1 (hcomp.congr_of_eventuallyEq heq)

end SharedChartCover
end Jacobians.Dolbeault
