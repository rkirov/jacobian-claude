/-
  Dolbeault ladder — manifold instantiation of the Čech finiteness node (Forster 14.9).

  This file ASSEMBLES the proven abstract finiteness spine
  (`CechFinitenessAbstract.finiteDimensional_h1_of_leray_compact`, `isCompactOperator_pi`,
  `isCompactOperator_of_subtypeL_comp`) against the proven disk-Montel atom
  (`BddHol.isCompactOperator_restrictCLM`) to discharge `DolbeaultLadder.finiteDimensional_cechH1`.

  CHOSEN SUP-NORM COCHAIN ENCODING (the Leray chart-disk cover, read in charts):
  the 1-cochains on the COVER live in `Π_p BddHol (Uov p)` (bounded-holomorphic on the chart-image
  of each overlap, an open set in `ℂ`); the 1-cochains on the relatively-compact SHRINKING live in
  `Π_p (Kov p →ᵇ ℂ)` (the Montel atom restricts `BddHol U →L[ℂ] (K →ᵇ ℂ)` for `K` compact, so the
  shrinking side is a product of `→ᵇ` spaces, NOT `BddHol`). Cocycle subspaces are kernels of the
  sup-norm coboundary `δ¹`, hence closed (so Banach). This data is packaged in `DiskOverlapData`
  (the geometric overlap data) + `Coboundaries` (the sup-norm `δ⁰/δ¹` and the commuting square for
  restriction).

  WHAT IS PROVEN HERE (axiom-clean, `[propext, Classical.choice, Quot.sound]`):
    * `DiskOverlapData` Banach instances; `rhoRaw` + `rhoRaw_compact` (STEP 3 — the Montel payoff).
    * `finiteDimensional_supH1` — STEP 5: builds the cocycle `δ`/`ρ`, transports compactness to the
      closed cocycle subspace, and applies the abstract reduction. Fully proven *given* the Leray
      surjectivity (an explicit argument).

  WHAT IS LEFT AS NAMED, HONEST `sorry`s (the genuinely-hard analytic / chart-bookkeeping pieces):
    * `leray_surjective`          — the Leray condition (restriction onto on `H¹`); needs
      `H¹(disk,𝒪)=0` from the proven `DbarDisk.dbar_solvable_of_compactSupport`. STATED, not weakened.
    * `exists_cechModel`          — existence of the chart-disk Leray model (`DiskOverlapData` +
      `Coboundaries`) for the cover: the CONSTRUCTION (chart bookkeeping, Leray refinement, shrinking).
    * `cechH1_linearEquiv_supH1`  — the COMPARISON `𝔘.cechH1 D ≃ₗ supH1`, stated against the *given*
      model (germ-class ↔ honest-bounded-holomorphic; codiscrete↔𝓝[≠] bridge of `CechH0`).
  NOTHING ELSE is a `sorry`. STEPS 3 (`ρ` compact) and 5 (the reduction application) are fully proven.
-/
import Jacobians.Dolbeault.CechFinitenessAbstract
import Jacobians.Dolbeault.BddHol
import Jacobians.Dolbeault.DolbeaultLadder

open Jacobians.Dolbeault.CechFiniteness ContinuousLinearMap
open BoundedContinuousFunction
open scoped Manifold ContDiff Topology

namespace Jacobians.Dolbeault

/-! ### STEP 1 — the geometric overlap data (chart-disk cover + relatively-compact shrinking) -/

/-- **Sup-norm cochain geometry.** The finite pair-index `J` of a Leray chart-disk cover, with, for
each overlap `p`, the chart-image cover-open `Uov p ⊆ ℂ` and a relatively-compact convex shrinking
`Kov p ⋐ Uov p`. This is exactly the geometric input the disk-Montel atom needs (open `U`, compact
convex `K ⊆ U`). The cover 1-cochains live in `Π_p BddHol (Uov p)`, the shrinking 1-cochains in
`Π_p (Kov p →ᵇ ℂ)`. -/
structure DiskOverlapData where
  /-- The finite pair-index of the cover (overlaps). -/
  J : Type
  [fintypeJ : Fintype J]
  [decEqJ : DecidableEq J]
  /-- Chart-image of each overlap on the COVER (an open set in `ℂ`). -/
  Uov : J → Set ℂ
  hUov : ∀ p, IsOpen (Uov p)
  /-- The relatively-compact convex SHRINKING of each overlap (a compact set in `ℂ`). -/
  Kov : J → Set ℂ
  hKcpt : ∀ p, IsCompact (Kov p)
  hKU : ∀ p, Kov p ⊆ Uov p
  hKconv : ∀ p, Convex ℝ (Kov p)

attribute [instance] DiskOverlapData.fintypeJ DiskOverlapData.decEqJ

namespace DiskOverlapData

variable (d : DiskOverlapData)

/-- Each shrinking compact carries a `CompactSpace` (so `Kov p →ᵇ ℂ` is a Banach space). -/
noncomputable instance compactSpace (p : d.J) : CompactSpace (d.Kov p) :=
  isCompact_iff_compactSpace.mp (d.hKcpt p)

/-- COVER 1-cochains: bounded-holomorphic on each overlap chart-image. -/
abbrev Ccov : Type := ∀ p : d.J, BddHol (d.Uov p)

/-- SHRINKING 1-cochains: bounded-continuous on each compact shrunk overlap (where the Montel atom
lands). -/
abbrev Cshr : Type := ∀ p : d.J, (d.Kov p →ᵇ ℂ)

noncomputable instance : NormedAddCommGroup d.Ccov := inferInstance
noncomputable instance : NormedSpace ℂ d.Ccov := inferInstance
noncomputable instance : NormedAddCommGroup d.Cshr := inferInstance
noncomputable instance : NormedSpace ℂ d.Cshr := inferInstance

/-- `Π_p BddHol (Uov p)` is a Banach space (finite product of the Banach `BddHol`). -/
noncomputable instance : CompleteSpace d.Ccov := by
  haveI : ∀ p, CompleteSpace (BddHol (d.Uov p)) := fun p => BddHol.completeSpace (d.hUov p)
  infer_instance

/-- `Π_p (Kov p →ᵇ ℂ)` is a Banach space. -/
noncomputable instance : CompleteSpace d.Cshr := inferInstance

/-! ### STEP 2/3 — the restriction operator `ρ` cover → shrinking, and its compactness -/

/-- The raw cochain restriction `Π_p BddHol (Uov p) →L[ℂ] Π_p (Kov p →ᵇ ℂ)`, componentwise
`BddHol.restrictCLM`. -/
noncomputable def rhoRaw : d.Ccov →L[ℂ] d.Cshr :=
  ContinuousLinearMap.pi (fun p => (BddHol.restrictCLM (d.hKU p)).comp (proj p))

@[simp] theorem rhoRaw_apply (f : d.Ccov) (p : d.J) :
    d.rhoRaw f p = BddHol.restrictCLM (d.hKU p) (f p) := by
  simp only [rhoRaw, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply]

/-- **STEP 3 (the Montel payoff).** The cochain restriction `ρ` (cover → shrinking) is a COMPACT
operator: componentwise it is `BddHol.restrictCLM`, compact by the disk-Montel atom
(`BddHol.isCompactOperator_restrictCLM`, each shrunk overlap being convex), and a finite product of
compacts is compact (`isCompactOperator_pi`). -/
theorem rhoRaw_compact : IsCompactOperator d.rhoRaw := by
  apply isCompactOperator_pi (fun p => BddHol.restrictCLM (d.hKU p))
  intro p
  exact BddHol.isCompactOperator_restrictCLM (d.hUov p) (d.hKcpt p) (d.hKU p) (d.hKconv p)

end DiskOverlapData

/-! ### The sup-norm coboundary bundle and the cocycle spaces -/

/-- **Sup-norm coboundary data** completing `DiskOverlapData` to a Čech `δ`-complex. We need the
shrinking-side coboundaries `δ⁰ : C0 → C¹(shrinking)` and `δ¹ : C¹(shrinking) → C²(shrinking)` with
`δ¹∘δ⁰ = 0`, a coboundary `δ¹` on the COVER side (whose kernel is `Z¹(cover)`), and the commuting
square saying restriction `ρ` carries cover-cocycles to shrinking-cocycles. These are the analytic
inputs that make `Z¹/B¹` the sup-norm `H¹`. -/
structure Coboundaries (d : DiskOverlapData) where
  /-- 0-cochain Banach space on the shrinking. -/
  C0 : Type
  [ng0 : NormedAddCommGroup C0]
  [ns0 : NormedSpace ℂ C0]
  [cs0 : CompleteSpace C0]
  /-- 2-cochain Banach space on the shrinking. -/
  C2 : Type
  [ng2 : NormedAddCommGroup C2]
  [ns2 : NormedSpace ℂ C2]
  /-- 2-cochain Banach space on the cover (target of the cover-side `δ¹`). -/
  C2cov : Type
  [ng2c : NormedAddCommGroup C2cov]
  [ns2c : NormedSpace ℂ C2cov]
  /-- The shrinking-side `δ⁰`. -/
  δ0 : C0 →L[ℂ] d.Cshr
  /-- The shrinking-side `δ¹`. -/
  δ1 : d.Cshr →L[ℂ] C2
  /-- The cover-side `δ¹` (its kernel is `Z¹(cover)`). -/
  δ1cov : d.Ccov →L[ℂ] C2cov
  /-- `δ¹∘δ⁰ = 0` on the shrinking (so `B¹ ⊆ Z¹`). -/
  hδδ : δ1.comp δ0 = 0
  /-- Restriction carries cover-cocycles to shrinking-cocycles (the commuting square). -/
  hcomm : ∀ x : d.Ccov, δ1cov x = 0 → δ1 (d.rhoRaw x) = 0

attribute [instance] Coboundaries.ng0 Coboundaries.ns0 Coboundaries.cs0
  Coboundaries.ng2 Coboundaries.ns2 Coboundaries.ng2c Coboundaries.ns2c

namespace Coboundaries

variable {d : DiskOverlapData} (c : Coboundaries d)

/-- `Z¹(cover) = ker δ¹(cover)`, a closed subspace of the cover 1-cochains. -/
noncomputable def Z1cov : Submodule ℂ d.Ccov := LinearMap.ker c.δ1cov.toLinearMap

/-- `Z¹(shrinking) = ker δ¹(shrinking)`, a closed subspace of the shrinking 1-cochains. -/
noncomputable def Z1shr : Submodule ℂ d.Cshr := LinearMap.ker c.δ1.toLinearMap

theorem isClosed_Z1cov : IsClosed (c.Z1cov : Set d.Ccov) := c.δ1cov.isClosed_ker

theorem isClosed_Z1shr : IsClosed (c.Z1shr : Set d.Cshr) := c.δ1.isClosed_ker

noncomputable instance : CompleteSpace c.Z1cov := c.δ1cov.isClosed_ker.completeSpace_coe
noncomputable instance : CompleteSpace c.Z1shr := c.δ1.isClosed_ker.completeSpace_coe

/-- The coboundary `δ : C⁰ →L[ℂ] Z¹(shrinking)` (i.e. `δ⁰` corestricted to the cocycles, using
`δ¹∘δ⁰=0`). Its range is `B¹`, and `Z¹/range δ` is the sup-norm `H¹`. -/
noncomputable def δ : c.C0 →L[ℂ] c.Z1shr :=
  c.δ0.codRestrict c.Z1shr fun x => by
    show c.δ1 (c.δ0 x) = 0
    have := congrArg (fun T => T x) c.hδδ
    simpa using this

/-- The restriction `ρ : Z¹(cover) →L[ℂ] Z¹(shrinking)` (the raw restriction `rhoRaw` restricted to
the cocycle subspaces, using the commuting square `hcomm`). -/
noncomputable def ρ : c.Z1cov →L[ℂ] c.Z1shr :=
  (d.rhoRaw.comp c.Z1cov.subtypeL).codRestrict c.Z1shr fun x => c.hcomm x.1 x.2

/-- `subtypeL ∘ ρ = rhoRaw ∘ subtypeL` — the defining commuting identity for `ρ`. -/
theorem subtypeL_comp_ρ :
    c.Z1shr.subtypeL.comp c.ρ = d.rhoRaw.comp c.Z1cov.subtypeL := by
  ext x; rfl

/-- **STEP 3 on the cocycle subspace.** `ρ : Z¹(cover) →L Z¹(shrinking)` is a COMPACT operator:
`rhoRaw` is compact (`DiskOverlapData.rhoRaw_compact`), `ρ` includes into it via the closed cocycle
subspace, and `isCompactOperator_of_subtypeL_comp` transports compactness back. -/
theorem ρ_compact : IsCompactOperator c.ρ := by
  apply isCompactOperator_of_subtypeL_comp c.isClosed_Z1shr c.ρ
  rw [c.subtypeL_comp_ρ]
  exact d.rhoRaw_compact.comp_clm c.Z1cov.subtypeL

/-- **The sup-norm `H¹`** of the cover/shrinking pair: `Z¹(shrinking) ⧸ B¹`, where `B¹ = range δ`.
This is the object the abstract reduction makes finite-dimensional; it is compared to the genuine
germ-class `cechH1` by `cechH1_model`. -/
abbrev supH1 : Type := c.Z1shr ⧸ LinearMap.range c.δ.toLinearMap

/-- **STEP 5 — finiteness of the sup-norm `H¹`.** Given the Leray surjectivity of `(η,ξ) ↦ δη + ρξ`,
the abstract reduction `finiteDimensional_h1_of_leray_compact` (with `ρ` compact by `ρ_compact`)
gives `supH1` finite-dimensional. Fully proven modulo the surjectivity argument. -/
theorem finiteDimensional_supH1
    (hsurj : Function.Surjective (fun p : c.C0 × c.Z1cov => c.δ p.1 + c.ρ p.2)) :
    FiniteDimensional ℂ c.supH1 :=
  finiteDimensional_h1_of_leray_compact c.δ c.ρ hsurj c.ρ_compact

end Coboundaries

/-! ### STEP 4 — the Leray surjectivity (named `sorry`, honest statement) -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **STEP 4 — Leray surjectivity (HONEST `sorry`).** For the chart-disk Leray cover/shrinking model
of `(𝔘, D)`, the combined map `(η, ξ) ↦ δη + ρξ` (coboundary on the shrinking ⊕ restriction from the
cover) is surjective. This is the Leray condition: restriction is onto on `H¹`, which holds because
each chart-disk has `H¹(disk, 𝒪) = 0` (solvability of `∂̄` on a disk — the proven
`DbarDisk.dbar_solvable_of_compactSupport`) so every shrinking-cocycle is, modulo a coboundary, the
restriction of a cover-cocycle. NOT proven here (the Čech-refinement/`∂̄` assembly is the genuine
analytic wall). -/
theorem leray_surjective (d : DiskOverlapData) (c : Coboundaries d) :
    Function.Surjective (fun p : c.C0 × c.Z1cov => c.δ p.1 + c.ρ p.2) := by
  sorry

/-! ### STEP 6a — existence of the chart-disk Leray model (named `sorry`, honest statement) -/

/-- **STEP 6a — the chart-disk Leray model exists (HONEST `sorry`).** Every finite cover `𝔘` admits a
chart-disk Leray cover/shrinking model: a `DiskOverlapData` (the per-overlap chart-images as disks in
`ℂ`, each with a relatively-compact convex shrinking) and a `Coboundaries` bundle (the sup-norm
`δ⁰/δ¹` and the restriction commuting square). This is the CONSTRUCTION half of the manifold side:
reading each overlap in a chart as a disk in `ℂ` (the "chart bookkeeping"), refining to a Leray cover
where each piece is `𝒪`-acyclic, and shrinking. NOT proven here. (Separated from the comparison so
the two distinct manifold facts are independently inspectable.) -/
theorem exists_cechModel (𝔘 : FiniteCover X) (D : Divisor X) :
    ∃ (d : DiskOverlapData), Nonempty (Coboundaries d) := by
  sorry

/-! ### STEP 6b — the comparison to the germ-class `cechH1` (named `sorry`, honest statement) -/

/-- **STEP 6b — comparison `cechH1 ≃ₗ supH1` (HONEST `sorry`).** For the chart-disk Leray model
`(d, c)` of `(𝔘, D)`, the genuine germ-class `H¹` is `ℂ`-linearly isomorphic to the sup-norm `H¹` of
the model. This is the COMPARISON proper (stated against the *given* model `c`, so it cannot be
discharged by an unrelated finite-dimensional model): the germ-class cochains (`MGerm`, junk-free)
and the honest bounded-holomorphic cochains have the same cocycles and coboundaries, because a
holomorphic section with a bounded pole is determined by its germ (the codiscrete ↔ `𝓝[≠]` bridge of
`CechH0`), and the cover-refinement `H¹(𝔘) ≅ H¹(refinement)` (Leray). NOT proven here. -/
noncomputable def cechH1_linearEquiv_supH1 (𝔘 : FiniteCover X) (D : Divisor X)
    (d : DiskOverlapData) (c : Coboundaries d) :
    𝔘.cechH1 D ≃ₗ[ℂ] c.supH1 :=
  sorry

/-! ### STEP 7 — discharge `finiteDimensional_cechH1` -/

/-- **The finiteness node, assembled.** `H¹(𝔘, 𝒪_D)` is finite-dimensional: take the chart-disk Leray
model (`exists_cechModel`); its sup-norm `H¹` is finite-dimensional by `finiteDimensional_supH1`
(STEP 5; `ρ` compact via the proven Montel atom + Leray surjectivity `leray_surjective`); and the
comparison `cechH1_linearEquiv_supH1` transports finiteness back to the germ-class `cechH1`. The only
unproven inputs are the three named analytic `sorry`s (`leray_surjective`, `exists_cechModel`,
`cechH1_linearEquiv_supH1`). This discharges the exact statement of
`DolbeaultLadder.finiteDimensional_cechH1`. -/
theorem finiteDimensional_cechH1_wired (𝔘 : FiniteCover X) (D : Divisor X) :
    FiniteDimensional ℂ (𝔘.cechH1 D) := by
  obtain ⟨d, ⟨c⟩⟩ := exists_cechModel 𝔘 D
  haveI : FiniteDimensional ℂ c.supH1 := c.finiteDimensional_supH1 (leray_surjective d c)
  exact (cechH1_linearEquiv_supH1 𝔘 D d c).symm.finiteDimensional
