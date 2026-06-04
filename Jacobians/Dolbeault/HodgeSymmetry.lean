/-
  Hodge symmetry and the `D = 0` Serre nugget, split into its two isomorphisms.

  ## Why this file exists

  `DolbeaultLadder.arithmeticGenus_eq_genus : 𝔘.h1Dim 0 = genus X` (Serre duality at `D = 0`) is the
  Serre input the forward headline `genus 0 → S²` needs. Its classical proof is the chain of two
  isomorphisms
  ```
        H¹(X, 𝒪)   ≅   H^{0,1}(X)   ≅   H^{1,0}(X) = Ω(X)
        └─ FIRST iso ─┘   └─ SECOND iso ─┘
  ```
  The earlier ladder leaf bundled BOTH isos into one opaque "Dolbeault nugget" `sorry`. But the **first
  iso is already proven** — it is the Dolbeault comparison
  `DolbeaultComparisonEquiv.cechH1_dolbeault_comparison_proof` (sorry-free, axiom-clean), which gives
  `finrank ℝ (DolbeaultH01 X) = 2 · finrank ℂ (𝔇.cechH1 0)` for a chart-disk Leray cover `𝔇`. So the
  genuine remaining content of `arithmeticGenus_eq_genus` is *exactly* the **second iso**, the **Hodge
  symmetry** `dim_ℂ H^{0,1}(X) = dim_ℂ H^{1,0}(X) = g`.

  This file makes that separation explicit in Lean: it isolates the Hodge symmetry as the single named
  classical kernel `hodge_symmetry`, and proves that the `D = 0` Serre nugget reduces to it *sorry-free
  given the kernel*, by composing with the already-proven comparison. For a chart-disk cover this needs
  NOTHING else (`arithmeticGenus_eq_genus_chartDisk`); for an arbitrary Leray cover it additionally
  needs the cover-independence comparison `cechH1_dolbeault_comparison` (itself a separate named gap),
  exhibited by `arithmeticGenus_eq_genus_of_hodge`.

  ## Status of `hodge_symmetry` (the genuine wall)

  `finrank ℝ (DolbeaultH01 X) = 2 · genus X`, i.e. `dim_ℂ H^{0,1} = dim_ℂ H^{1,0}`. This is a true
  classical theorem (Hodge symmetry on a compact Riemann surface) but has no Mathlib scaffolding. The
  natural map is the conjugation `Φ : Ω(X) → H^{0,1}(X)`, `ω ↦ [ω̄]` (conjugate of a holomorphic
  `(1,0)`-form is a `∂̄`-closed `(0,1)`-form), which is conjugate-`ℂ`-linear. The two directions:
    * `g ≤ dim H^{0,1}` (`Φ` injective): the EASY half, via the `L²` positivity
      `(i/2)∫_X ω̄ ∧ ω > 0` for `ω ≠ 0` (Stokes + positivity; shared with `#7`'s period engine);
    * `dim H^{0,1} ≤ g` (`Φ` surjective): the HARD half = the existence side of Hodge/Serre
      (residue-pairing perfectness, Forster §17; or Hodge decomposition).
  Both directions still require analysis the repo does not yet have (manifold integration / the §17
  residue pairing), so the symmetry stays a single honest `sorry` here. See
  `docs/hodge_bridge_research.md` §2 for the full route.

  ## References
  * Forster, *Lectures on Riemann Surfaces*, §17 (Serre duality), §19 (harmonic forms / Hodge symmetry).
  * Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 (Hodge symmetry on curves).
-/
import Jacobians.Dolbeault.DolbeaultComparisonEquiv
import Jacobians.Genus

open scoped Manifold ContDiff Topology

-- Matches the transparency setting the Dolbeault-comparison files use, so the `DolbeaultH01`
-- hom-bundle abbrev elaborates against the same `ℂ`-`ℝ`-module instances (see `RealForms`).
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Hodge symmetry on a compact Riemann surface — the genuine remaining Serre wall at `D = 0`.**
`finrank ℝ (DolbeaultH01 X) = 2 · genus X`, i.e. `dim_ℂ H^{0,1}(X) = dim_ℂ H^{1,0}(X) = g`.

This is the **second** of the two isomorphisms `H¹(𝒪) ≅ H^{0,1} ≅ Ω(X)` underlying Serre duality at
`D = 0`; the **first** (`H¹(𝒪) ≅ H^{0,1}`) is the already-proven Dolbeault comparison
`cechH1_dolbeault_comparison_proof`. Stated with the real-vs-complex factor `2 ·` because
`DolbeaultH01 X` carries only `Module ℝ` (the hom-bundle ℂ-action is not propagated to the section
space — see the SCALAR NOTE in `DolbeaultComparison.lean`), while `genus X = finrank ℂ Ω(X)`; both
sides equal `2g`.

A true classical theorem with no Mathlib scaffolding. The natural map is the conjugation
`ω ↦ [ω̄] : Ω(X) → H^{0,1}(X)`; injectivity (`g ≤ dim H^{0,1}`) is the EASY half via `L²` positivity,
surjectivity (`dim H^{0,1} ≤ g`) is the HARD half (Hodge/Serre existence). Left as the single honest
`sorry`. See the file header and `docs/hodge_bridge_research.md`. -/
theorem hodge_symmetry (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
    Module.finrank ℝ (DolbeaultH01 X) = 2 * genus X :=
  sorry

/-- **The `D = 0` Serre nugget for a chart-disk cover, reduced to Hodge symmetry (sorry-free given it).**
For a chart-disk Leray cover `𝔇`, `𝔇.h1Dim 0 = genus X`. Proof: the proven Dolbeault comparison gives
`finrank ℝ (DolbeaultH01 X) = 2 · 𝔇.h1Dim 0`, and `hodge_symmetry` gives
`finrank ℝ (DolbeaultH01 X) = 2 · genus X`; cancel the `2`. This is the forward-headline-aligned form
(the headline's cleanest path restates the ladder over a chart-disk cover — the "partial sidestep" of
`CechRefinement.lean`'s PLAN — so no cover-independence is needed). The ONLY analytic input is the
single named `hodge_symmetry` kernel. -/
theorem arithmeticGenus_eq_genus_chartDisk (𝔇 : ChartDiskCover X)
    (hL : 𝔇.toFiniteCover.IsLeray) :
    𝔇.toFiniteCover.h1Dim 0 = genus X := by
  have hcomp : Module.finrank ℝ (DolbeaultH01 X) = 2 * 𝔇.toFiniteCover.h1Dim 0 :=
    cechH1_dolbeault_comparison_proof 𝔇 hL
  have hkey : 2 * 𝔇.toFiniteCover.h1Dim 0 = 2 * genus X := by
    rw [← hcomp, hodge_symmetry X]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hkey

/-- **The `D = 0` Serre nugget for an arbitrary Leray cover = Hodge symmetry + cover-independence.**
`𝔘.h1Dim 0 = genus X` for any Leray cover `𝔘`, reduced (sorry-free in this proof) to the two named
kernels it genuinely rests on: `hodge_symmetry` (the second iso) and `cechH1_dolbeault_comparison`
(the arbitrary-cover Dolbeault comparison — the cover-independence gap, proven sorry-free only for the
chart-disk cover via `cechH1_dolbeault_comparison_proof`). This is exactly the statement of
`DolbeaultLadder.arithmeticGenus_eq_genus`, here exhibited as the composite of two crisp named inputs
rather than one opaque nugget. -/
theorem arithmeticGenus_eq_genus_of_hodge (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) :
    𝔘.h1Dim 0 = genus X := by
  have hcomp : Module.finrank ℝ (DolbeaultH01 X) = 2 * 𝔘.h1Dim 0 :=
    cechH1_dolbeault_comparison 𝔘 hL
  have hkey : 2 * 𝔘.h1Dim 0 = 2 * genus X := by
    rw [← hcomp, hodge_symmetry X]
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) hkey

end Jacobians.Dolbeault
