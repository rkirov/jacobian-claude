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

end SharedChartCover
end Jacobians.Dolbeault
