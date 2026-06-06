/-
  Čech finiteness — instantiating the acyclic `exists_cechModel` via the completed disk-acyclicity.

  `CechFinitenessWiring.exists_cechModel` is the single remaining finiteness sorry (Forster 14.9):
  every finite cover `𝔘` admits a chart-disk Leray model (`DiskOverlapData` + `Coboundaries`, including
  the `leray` disk-acyclicity field) whose sup-norm `H¹` is `ℂ`-linearly isomorphic to the genuine
  germ-class `𝔘.cechH1 D`.  As scoped in `CechRefinement.lean`'s `## PLAN`, the FULL statement
  (arbitrary `𝔘`, arbitrary `D`) is blocked by STEP B — Leray cover-INDEPENDENCE (`refineH1` being an
  iso for a strictly-finer Leray refinement), a greenfield ~several-hundred-LoC piece on top of the
  proven disk ∂̄-atoms.  That is NOT what the newly-completed disk-acyclicity unblocked.

  `CechFinitenessWiring` already banks (sorry-free) the END-TO-END model assembly for the ACYCLIC case:
  `exists_cechModel_of_subsingleton` discharges `exists_cechModel 𝔘 D` whenever `𝔘.cechH1 D` is a
  SUBSINGLETON, via the trivial model `DiskOverlapData.empty.trivialCoboundaries` (whose `leray` field
  is discharged and whose `supH1 = 0`) and `LinearEquiv.ofSubsingleton`.

  THIS FILE supplies the geometric INSTANTIATION that the new disk-acyclicity makes possible
  (`exists_cechModel_of_sharedChart_zero`): for a `SharedChartCover 𝔇` at `D = 0`, the subsingleton
  hypothesis is discharged by the COMPLETED disk-acyclicity `SharedChartCover.hasGluedDbarDatum` (commit
  61484f5) — `H¹(disk, 𝒪) = 0` — so the disk `∂̄`-solvability engine is wired through the
  model-construction front door:
      `dbar_solvable_ball` ⟹ `HasGluedDbarDatum` ⟹ `H¹(disk, 𝒪) = 0` ⟹ `exists_cechModel 𝔇 0`.
  (It lives here, not in `CechFinitenessWiring`, because it needs the `GluedDbarDatum` /
  `CechFinitenessBallSolve` closure, which imports — and so cannot be imported by — `CechComplex`'s
  downstream `CechFinitenessWiring`.)

  WHY THE GENERAL `exists_cechModel` STAYS A SORRY (the exact remaining obstruction):  an arbitrary
  Leray `𝔘` is NOT a `SharedChartCover` and its `cechH1 𝔘 D` is NOT a subsingleton (for high genus /
  general `D`), so the subsingleton route does not apply.  Closing the general statement needs the
  comparison `cechH1 𝔘 D ≃ₗ supH1` for a NON-acyclic `supH1` — the genuine Montel-model comparison +
  Leray cover-independence STEP B (`CechRefinement.lean`'s `## PLAN`, `CechRefinementLeray.lean`'s
  `## SURJECTIVITY`).  The forward `germ → BddHol` cochain map is built for `D = 0`
  (`CechModelCochain`/`CechModelDatum`); the inverse, the δ-square, and STEP B are not.

  All declarations here are sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
import Jacobians.Dolbeault.CechFinitenessWiring
import Jacobians.Dolbeault.CechModelDifferential
import Jacobians.Dolbeault.GluedDbarDatum
import Jacobians.Dolbeault.ChartCoverDbarGlue
import Jacobians.Dolbeault.CechModelHolomorphic

open scoped Manifold ContDiff Topology

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **`exists_cechModel` for a shared-chart disk cover at `D = 0` (the disk-acyclicity wiring).**  For
any `SharedChartCover 𝔇` (a finite cover whose sets sit in one chart with chart-images in a fixed
ball), `exists_cechModel 𝔇.toFiniteCover 0` holds.  The subsingleton hypothesis of
`exists_cechModel_of_subsingleton` is discharged by the COMPLETED disk-acyclicity
`cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 (𝔇.hasGluedDbarDatum)` (commit 61484f5): every class of
`𝔇.toFiniteCover.cechH1 0` is `0`, so that `H¹` is a subsingleton.

This wires the newly-unblocked `leray`/disk-acyclicity piece through the model-construction front
door: the disk `∂̄`-solvability (`dbar_solvable_ball`) ⟹ `HasGluedDbarDatum` ⟹ `H¹(disk, 𝒪) = 0` ⟹ the
assembled `exists_cechModel` on the shared-chart cover (the trivial acyclic model + the
`LinearEquiv.ofSubsingleton` comparison). -/
theorem exists_cechModel_of_sharedChart_zero (𝔇 : SharedChartCover X)
    (H : HasGluedDbarDatum 𝔇) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d),
      Nonempty (𝔇.toFiniteFamily.cechH1 (0 : Divisor X) ≃ₗ[ℂ] c.supH1) := by
  haveI : Subsingleton (𝔇.toFiniteFamily.cechH1 (0 : Divisor X)) :=
    subsingleton_iff.mpr fun a b => by
      rw [cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 H a,
        cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 H b]
  exact exists_cechModel_of_subsingleton 𝔇.toFiniteFamily 0

/-- **`exists_holomorphicCechModel` for a shared-chart disk cover at `D = 0` (the corrected branch).**
This is the same disk-acyclicity wiring as the older wrapper above, but routed to the corrected
holomorphic-shrinking model. -/
theorem exists_holomorphicCechModel_of_sharedChart_zero (𝔇 : SharedChartCover X)
    (H : HasGluedDbarDatum 𝔇) :
    ∃ (d : HolomorphicDiskOverlapData) (c : HolomorphicCoboundaries d),
      Nonempty (𝔇.toFiniteFamily.cechH1 (0 : Divisor X) ≃ₗ[ℂ] c.supH1) := by
  haveI : Subsingleton (𝔇.toFiniteFamily.cechH1 (0 : Divisor X)) :=
    subsingleton_iff.mpr fun a b => by
      rw [cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 H a,
        cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 H b]
  exact HolomorphicDiskOverlapData.exists_holomorphicCechModel_of_subsingleton 𝔇.toFiniteFamily 0

/-- The sound interior-core glued datum witness, re-exposed at the model-construction layer so the
rebased branch is available from the consumer side. -/
theorem hasGluedDbarDatumOnInteriorCore (𝔇 : SharedChartCover X) :
    ∀ s : ↥(𝔇.toFiniteFamily.cocycles1 (0 : Divisor X)),
      ∃ dbarDatum : ℂ → ℂ, ContDiff ℝ (⊤ : ℕ∞) dbarDatum ∧
        ∀ i, ∀ z ∈ Metric.ball 𝔇.ballCenter 𝔇.radius ∩ 𝔇.Ω i ∩ (𝔇.φ '' interior 𝔇.core),
          DbarDisk.dbar (chartPrim 𝔇 s i) z = dbarDatum z := by
  intro s
  refine ⟨𝔇.dbarDatum s, 𝔇.contDiff_dbarDatum s, ?_⟩
  intro i z hz
  have hzΩ : z ∈ 𝔇.Ω i := hz.1.2
  have hzcoreimg : z ∈ (𝔇.φ '' interior 𝔇.core) := hz.2
  rcases hzΩ with ⟨x₁, hxU, rfl⟩
  rcases hzcoreimg with ⟨x₂, hxcore, hφ⟩
  have hsrc₁ : x₁ ∈ (𝔇.φ).source := 𝔇.subset_source i hxU
  have hxunion : x₂ ∈ ⋃ i, (𝔇.U i : Set X) := 𝔇.core_subset (interior_subset hxcore)
  rcases Set.mem_iUnion.mp hxunion with ⟨j, hxj⟩
  have hsrc₂ : x₂ ∈ (𝔇.φ).source := 𝔇.subset_source j hxj
  have hxEq : x₁ = x₂ := by
    apply (𝔇.φ).injOn hsrc₁ hsrc₂
    simpa using hφ.symm
  subst hxEq
  exact 𝔇.dbarDatum_agrees_on_interiorCore s i hxU hxcore

end Jacobians.Dolbeault
