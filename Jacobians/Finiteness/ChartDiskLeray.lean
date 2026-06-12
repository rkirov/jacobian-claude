
open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Metric Complex Filter

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace ChartDiskCover

variable (𝔇 : ChartDiskCover X)

/-! ## The shrinking-level smooth partition of unity (sum-to-one on ALL of `X`)

The covering shrinking sets `shrinkSet a = V_a` (from `ChartDiskFiniteness`) genuinely cover `X`
(`iUnion_shrinkSet_eq_univ`), so a subordinate smooth PoU summing to `1` on all of `X` exists. -/

/-- The shrinking sets as `Opens X` (they are open, `shrinkSet_isOpen`). -/
noncomputable def shrinkSetOpens (a : 𝔇.ι) : Opens X := ⟨𝔇.shrinkSet a, 𝔇.shrinkSet_isOpen a⟩

@[simp] theorem shrinkSetOpens_coe (a : 𝔇.ι) :
    ((𝔇.shrinkSetOpens a : Opens X) : Set X) = 𝔇.shrinkSet a := rfl

/-- **The shrinking-level smooth PoU exists (sum-to-one on all of `X`).** A smooth partition of
unity over `𝓘(ℝ,ℂ)`, subordinate to the covering shrinkings `(V_a)`, summing to `1` on ALL of `X`
(the closed sum-to-one locus is `univ`, since the shrinkings cover `X`). This is the foundation the
Forster 14.6 smooth split consumes: the PoU is subordinate to the SHRINKINGS, where the input
cocycle is defined. -/
theorem exists_shrinkPoU :
    ∃ ρ : SmoothPartitionOfUnity 𝔇.ι 𝓘(ℝ, ℂ) X Set.univ,
      ρ.IsSubordinate (fun a => (𝔇.shrinkSet a)) := by
  refine exists_smoothPartitionOfUnity_core 𝔇.shrinkSetOpens isClosed_univ ?_
  rw [Set.univ_subset_iff]
  simpa only [shrinkSetOpens_coe] using 𝔇.iUnion_shrinkSet_eq_univ

/-- A fixed shrinking-level smooth PoU subordinate to `(V_a)`, summing to `1` on all of `X`. -/
noncomputable def shrinkPoU : SmoothPartitionOfUnity 𝔇.ι 𝓘(ℝ, ℂ) X Set.univ :=
  𝔇.exists_shrinkPoU.choose

/-- The shrinking PoU is subordinate to `(V_a)`: `tsupport ρ_a ⊆ V_a`. -/
theorem shrinkPoU_subordinate :
    (𝔇.shrinkPoU).IsSubordinate (fun a => (𝔇.shrinkSet a)) :=
  𝔇.exists_shrinkPoU.choose_spec

/-- **Sum-to-one EVERYWHERE.**  `∑ a, ρ_a x = 1` for every `x : X`. -/
theorem sum_shrinkPoU_eq_one (x : X) :
    ∑ a, (𝔇.shrinkPoU) a x = 1 :=
  smoothPartitionOfUnity_sum_eq_one_of_mem (𝔇.shrinkPoU) (Set.mem_univ x)

/-- The subordination as a `tsupport` containment: `tsupport (ρ_a) ⊆ V_a`. -/
theorem shrinkPoU_tsupport_subset (a : 𝔇.ι) :
    tsupport (𝔇.shrinkPoU a) ⊆ 𝔇.shrinkSet a :=
  𝔇.shrinkPoU_subordinate a

/-- Each PoU function `ρ_a : X → ℝ` is globally `C^∞` on `X` (over `𝓘(ℝ,ℂ) → 𝓘(ℝ,ℝ)`). -/
theorem contMDiff_shrinkPoU (a : 𝔇.ι) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (𝔇.shrinkPoU a) :=
  (𝔇.shrinkPoU a).contMDiff

/-- `ρ_a x = 0` for `x ∉ tsupport ρ_a`. -/
theorem shrinkPoU_eq_zero_of_notMem (a : 𝔇.ι) {x : X}
    (hx : x ∉ tsupport (𝔇.shrinkPoU a)) : (𝔇.shrinkPoU a) x = 0 :=
  image_eq_zero_of_notMem_tsupport hx

end ChartDiskCover

end Jacobians.Dolbeault
