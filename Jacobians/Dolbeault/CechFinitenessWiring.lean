/-
  Dolbeault ladder — Čech finiteness node, TOP LAYER: the keystone `exists_cechModel` (now PROVEN)
  and the assembled finiteness theorem `finiteDimensional_cechH1_wired` (Forster 14.9).

  This is the thin top layer over `CechModelBase` (the sup-norm Montel model TYPES + abstract
  finiteness spine: `DiskOverlapData`, `Coboundaries`, `rhoRaw`/`rhoRaw_compact`, the cocycle spaces,
  `finiteDimensional_supH1`, `leray_surjective`, the trivial acyclic model, and the acyclic
  `exists_cechModel_of_subsingleton`).  It imports `CechFinitenessDtwist`, which supplies the proven
  general-divisor term `exists_cechModel_general`, and re-exports it as the keystone `exists_cechModel`.

  WHAT IS PROVEN HERE (axiom-clean, `[propext, Classical.choice, Quot.sound]`):
    * `exists_cechModel`            — the chart-disk Leray model existential, for an ARBITRARY finite
      cover and divisor, re-exporting `CechFinitenessDtwist.exists_cechModel_general`.  The analytic
      content is `finiteDimensional_cechH1_general` (general-divisor Čech `H¹` finiteness via the §16
      skyscraper reduction on the proven `D = 0` base) plus the artificial single-point Montel model
      `CechModelArtificial.exists_cechModel_of_finiteDimensional`.
    * `cechH1_linearEquiv_supH1`    — the correctly-scoped comparison consumer.
    * `finiteDimensional_cechH1_wired` — the finiteness node, assembled: `H¹(𝔘, 𝒪_D)` is
      finite-dimensional.  This discharges the exact statement of `DolbeaultLadder.finiteDimensional_cechH1`.

  Splitting the model types into `CechModelBase` (this file's import) is what lets `exists_cechModel`
  re-export the proven `exists_cechModel_general`: the latter's artificial model
  (`CechModelArtificial`) imports the model types, so before the split those types could not import the
  general term back (a cycle).  There is NO new mathematics in this file.
-/
import Jacobians.Dolbeault.CechModelBase
import Jacobians.Dolbeault.CechFinitenessDtwist

open Jacobians.Dolbeault.CechFiniteness ContinuousLinearMap
open BoundedContinuousFunction
open scoped Manifold ContDiff Topology

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### STEP 6a — existence of the chart-disk Leray model (PROVEN, re-exporting the general term) -/

/-- **STEP 6a — the chart-disk Leray model exists and computes `cechH1` (PROVEN, axiom-clean).**
Every finite cover `𝔘` admits, for any divisor `D`, a `DiskOverlapData` + `Coboundaries` bundle whose
sup-norm `H¹` is `ℂ`-linearly isomorphic to the genuine germ-class `𝔘.cechH1 D`.

The comparison is bundled into the conclusion (rather than a free-`c` standalone) precisely because
`supH1` depends only on the model and `cechH1 D` only on `(𝔘, D)`: the isomorphism holds only for the
model *built from* `(𝔘, D)`.

This is now PROVEN by re-exporting `CechFinitenessDtwist.exists_cechModel_general`.  Its analytic
content is the general-divisor Čech `H¹` finiteness `finiteDimensional_cechH1_general` (the §16
skyscraper reduction climbing the proven `D = 0` base `finiteDimensional_cechH1_zero` one point at a
time) combined with the artificial single-point Montel model
`CechModelArtificial.exists_cechModel_of_finiteDimensional` (a one-point shrinking keeps the shrinking
cochains finite-dimensional, so the compact-`rhoRaw` `leray` field is consistent and provable). -/
theorem exists_cechModel (𝔘 : FiniteCover X) (D : Divisor X) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d), Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1) :=
  exists_cechModel_general 𝔘 D

/-! ### STEP 6b — the comparison to the germ-class `cechH1` (consumer of `exists_cechModel`)

SOUNDNESS NOTE.  The comparison is bundled into `exists_cechModel`'s conclusion (above) rather than
stated as a standalone equivalence `(𝔘 D d c) → 𝔘.cechH1 D ≃ₗ c.supH1`.  The latter is FALSE for a
free `c`: `supH1` depends only on the model `c` while `cechH1 D` depends only on `(𝔘, D)`, so for an
unrelated acyclic model (e.g. one chart-disk with `supH1 = 0`) against a high-genus `(𝔘, D)` the two
sides have different dimensions.  The equivalence holds only for the model that is *built from*
`(𝔘, D)` — hence the existential `∃ d c, …` tying `c` to `(𝔘, D)`.  `cechH1_linearEquiv_supH1` below
is the corresponding correctly-scoped *consumer* (it extracts the bundled equivalence), kept as a
named, inspectable entry point. -/

/-- **STEP 6b — comparison `cechH1 ≃ₗ supH1` (consumer of `exists_cechModel`, sorry-free).** For the
chart-disk Leray model produced by `exists_cechModel 𝔘 D`, the genuine germ-class `H¹` is
`ℂ`-linearly isomorphic to the sup-norm `H¹` of that model.  This simply repackages the bundled
equivalence.  Stated as an existence of *a* model with the comparison, so it cannot be vacuously
discharged by an unrelated finite-dimensional model. -/
theorem cechH1_linearEquiv_supH1 (𝔘 : FiniteCover X) (D : Divisor X) :
    ∃ (d : DiskOverlapData) (c : Coboundaries d), Nonempty (𝔘.cechH1 D ≃ₗ[ℂ] c.supH1) :=
  exists_cechModel 𝔘 D

/-! ### STEP 7 — discharge `finiteDimensional_cechH1` -/

/-- **The finiteness node, assembled.** `H¹(𝔘, 𝒪_D)` is finite-dimensional: take the chart-disk Leray
model with its comparison (`exists_cechModel`, now PROVEN); its sup-norm `H¹` is finite-dimensional by
`finiteDimensional_supH1` (STEP 5; `ρ` compact via the proven Montel atom + the PROVEN Leray
surjectivity `leray_surjective`); and the bundled comparison `cechH1 ≃ₗ supH1` transports finiteness
back to the germ-class `cechH1`. This discharges the exact statement of
`DolbeaultLadder.finiteDimensional_cechH1`. -/
theorem finiteDimensional_cechH1_wired (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.cechH1 D) := by
  obtain ⟨d, c, ⟨e⟩⟩ := exists_cechModel 𝔘 D
  haveI : FiniteDimensional ℂ c.supH1 := c.finiteDimensional_supH1 (leray_surjective d c)
  exact e.symm.finiteDimensional

end Jacobians.Dolbeault
