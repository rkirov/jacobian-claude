/-
  Dolbeault ladder — the Čech finiteness ASSEMBLY (the 14.7 route, D = 0).

  Combines the two now-proven structural pieces with the analytic Montel finiteness:
    * **Forster 12.4** (`refineH1_injective_unconditional`, `CechRefinementInjective`): refinement maps
      on `H¹` are injective UNCONDITIONALLY (germ-class `𝒪_D` sheaf-gluing).
    * **chart-disk refinement existence** (`exists_chartDiskCover_refinement`, `ChartDiskRefinement`):
      every finite cover is refined by a `ChartDiskCover` (ball sets).
    * **Montel finiteness** (`ChartDiskFiniteness.finiteDimensional_cechH1_chartDisk`): `cechH1 𝔇 0` is
      finite-dimensional for a `ChartDiskCover 𝔇` — the analytic heart (Forster 14.6/14.7).

  Given the Montel finiteness, finiteness for an ARBITRARY cover follows by the injection
  `cechH1 𝔘 0 ↪ cechH1 𝔇 0` (12.4) into the finite-dimensional `cechH1 𝔇 0` — NO cover-independence
  isomorphism (hence NO Riemann mapping) is needed.  This is the key to the 14.7 route.

  The Montel finiteness is taken here as an explicit HYPOTHESIS `hMontel` so this assembly file is
  sorry-free and builds independently of the (in-progress) `ChartDiskFiniteness`; the final wiring
  discharges `hMontel` with that theorem.
-/
import Jacobians.Dolbeault.CechRefinementInjective
import Jacobians.Dolbeault.ChartDiskRefinement
import Jacobians.Dolbeault.CechModelArtificial

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Finiteness of `H¹(𝔘, 𝒪)` for an arbitrary finite cover, from the chart-disk Montel finiteness.**
`cechH1 𝔘 0 ↪ cechH1 𝔇 0` (Forster 12.4 injectivity along a chart-disk refinement `𝔇 ⪯ 𝔘`) injects
into the finite-dimensional `cechH1 𝔇 0`; a linear injection into a finite-dimensional space has a
finite-dimensional domain.  No cover-independence isomorphism is used. -/
theorem finiteDimensional_cechH1_zero_of_chartDiskMontel
    (hMontel : ∀ 𝔇 : ChartDiskCover X, FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 (0 : Divisor X)))
    (𝔘 : FiniteCover X) :
    FiniteDimensional ℂ (𝔘.cechH1 (0 : Divisor X)) := by
  obtain ⟨𝔇, r, hr⟩ := exists_chartDiskCover_refinement 𝔘
  haveI : FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 (0 : Divisor X)) := hMontel 𝔇
  have hinj : Function.Injective (hr.refineH1 (0 : Divisor X)) :=
    FiniteCover.IsRefinement.refineH1_injective_unconditional (D := (0 : Divisor X)) hr
  exact FiniteDimensional.of_injective _ hinj

/-- **`exists_cechModel 𝔘 0` from the chart-disk Montel finiteness (the 14.7 route, D = 0).**  Combines
the arbitrary-cover finiteness above with the artificial single-point model
(`exists_cechModel_of_finiteDimensional`).  This discharges `CechFinitenessWiring.exists_cechModel 𝔘 0`
for every finite cover `𝔘`, modulo only the Montel hypothesis `hMontel`. -/
theorem exists_cechModel_zero_of_chartDiskMontel
    (hMontel : ∀ 𝔇 : ChartDiskCover X, FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 (0 : Divisor X)))
    (𝔘 : FiniteCover X) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d),
      Nonempty (𝔘.cechH1 (0 : Divisor X) ≃ₗ[ℂ] c.supH1) :=
  haveI : FiniteDimensional ℂ (𝔘.cechH1 (0 : Divisor X)) :=
    finiteDimensional_cechH1_zero_of_chartDiskMontel hMontel 𝔘
  exists_cechModel_of_finiteDimensional 𝔘 (0 : Divisor X)

end Jacobians.Dolbeault
