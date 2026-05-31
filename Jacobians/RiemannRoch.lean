/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Roadmap
import Jacobians.MeromorphicLiouville

/-!
# Riemann–Roch layer — finer reduction of the #1 input (TEMPORARY scaffold)

This refines `Jacobians.Roadmap.exists_simplePole_of_genus_zero` (the Riemann–Roch consequence
behind #1 `genus_eq_zero_iff_homeo`) into two cleaner, separately-fillable pieces:

* `exists_poleBounded_nonconstant_of_genus_zero` — the **pure Riemann–Roch output**: genus `0` ⟹ a
  non-constant meromorphic function whose poles are bounded by a single point `P` (i.e. `l(P) ≥ 2`).
  This is the genuine RR content (Forster §16, `l(P) = deg P + 1 − g + l(K−P) = 2`), resting on the
  Dolbeault/Serre wall.
* `exists_pole_of_nonconstant` — **compact Liouville** for meromorphic functions: a non-constant
  meromorphic function on a compact surface must have a pole. Mathlib *has* the holomorphic Liouville
  (`MDifferentiable.exists_eq_const_of_compactSpace`); this is its meromorphic corollary, fillable
  without the Dolbeault wall.

From these the simple-pole existence is **proven** (`isSimplePole_of_poleBounded_nonconstant` +
`exists_simplePole_of_genus_zero`): a pole-bounded non-constant function has its (forced) pole exactly
at `P` with order `−1`, i.e. a degree-1 map to `ℂℙ¹`.

## Why no full `l(D)`/`K` Riemann–Roch yet
Stating RR as the equality `l(D) − l(K−D) = deg D + 1 − g` needs:
* the linear-system dimension `l(D) = finrank ℂ L(D)` — `L(D)` is a `ℂ`-submodule of meromorphic
  functions, which first needs an **algebra/module structure on `MeromorphicFunction`** (the repo has
  only `IsMeromorphic.zero`; `IsMeromorphic.add`/`.smul` must be lifted from Mathlib's
  `MeromorphicAt.add` through charts) plus the **valuation closure** `orderAtPoint(f+g) ≥
  min(orderAtPoint f, orderAtPoint g)` (Mathlib's `meromorphicOrderAt_add_of_ne` /
  `MeromorphicOn.min_divisor_le_divisor_add`, lifted through charts);
* the **canonical divisor `K`** — the divisor of a *meromorphic 1-form*, which the repo does not yet
  have (it has holomorphic 1-forms only).

That foundation (~300–500 LoC of chart-lifting plumbing) is its own focused build; until then the
RR content is pinned at the function-existence interface above, which is exactly what #1 consumes.
The proof chain *behind* `exists_poleBounded_nonconstant_of_genus_zero` is the Dolbeault → finiteness
of `H¹(X,𝒪)` (Montel — the repo has Montel) → `χ`-additivity → Serre duality → RR layer (Phase 1/2).
-/

set_option linter.unusedSectionVars false

namespace Jacobians.Roadmap

open scoped Manifold ContDiff
open Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- `f` is **non-constant** (order-based): it has a genuine zero or pole somewhere,
`∃ x, f.orderAtPoint x ≠ 0`.

This is the *junk-immune* notion. A value-based `¬ ∃ c, ∀ x, f.toFun x = c` is too weak: the repo's
`MeromorphicFunction.toFun` can carry **removable-singularity junk** (`MeromorphicAt` does not pin the
value at the center), so a "constant + one junk value" function would be value-non-constant yet
pole-free — breaking `exists_pole_of_nonconstant`. At the order level there is no junk: `orderAtPoint`
depends only on the germ, and `orderAtPoint ≡ 0 ⟺ f` is a (non-vanishing) constant or the zero
function, so `∃ x, orderAtPoint x ≠ 0` is exactly honest non-constancy. -/
def IsNonConstant (f : MeromorphicFunction X) : Prop :=
  ∃ x, f.orderAtPoint x ≠ 0

/-- `f` has **poles bounded by the single point `P`**: holomorphic off `P` and at most a simple pole
at `P` (`div f ≥ −P`, i.e. `f ∈ L(P)`). -/
def IsPoleBoundedBy (f : MeromorphicFunction X) (P : X) : Prop :=
  (∀ x, x ≠ P → 0 ≤ f.orderAtPoint x) ∧ -1 ≤ f.orderAtPoint P

/-- **[INPUT — compact Liouville (no Dolbeault)]** A non-constant meromorphic function on a compact
Riemann surface has a pole. Meromorphic corollary of holomorphic Liouville
(`MDifferentiable.exists_eq_const_of_compactSpace`): with no poles `f` is holomorphic, hence constant.
Fillable from Mathlib + the repo's chart/meromorphic API — independent of the Dolbeault wall. -/
theorem exists_pole_of_nonconstant (f : MeromorphicFunction X) (hf : IsNonConstant f) :
    ∃ x, f.orderAtPoint x < 0 :=
  f.exists_pole_of_nonconstant hf

/-- **[INPUT — Riemann–Roch output]** Genus `0` yields a non-constant meromorphic function with poles
bounded by a single point (`l(P) ≥ 2`). The genuine RR content (Forster §16), resting on the
Dolbeault/Serre wall (Phase 1/2). -/
theorem exists_poleBounded_nonconstant_of_genus_zero (h : genus X = 0) :
    ∃ (P : X) (f : MeromorphicFunction X), IsPoleBoundedBy f P ∧ IsNonConstant f :=
  sorry

/-- **Liouville localization (PROVEN).** A non-constant function with poles bounded by `P` has its
pole *exactly* at `P` with order `−1` — a single simple pole, i.e. a degree-1 map to `ℂℙ¹`. (The
forced pole from `exists_pole_of_nonconstant` can only sit at `P`, where the bound `≥ −1` pins it to
`−1`.) -/
theorem isSimplePole_of_poleBounded_nonconstant (f : MeromorphicFunction X) {P : X}
    (hpb : IsPoleBoundedBy f P) (hnc : IsNonConstant f) :
    IsSimplePoleFunction f P := by
  obtain ⟨x, hx⟩ := exists_pole_of_nonconstant f hnc
  obtain ⟨hpb1, hpb2⟩ := hpb
  refine ⟨?_, hpb1⟩
  have hxP : x = P := by
    by_contra hne; exact absurd (hpb1 x hne) (not_le.mpr hx)
  rw [hxP] at hx
  omega

/-- **`exists_simplePole_of_genus_zero`, REDUCED** to the pure RR output
(`exists_poleBounded_nonconstant_of_genus_zero`) + compact Liouville (`exists_pole_of_nonconstant`),
via the proven localization. This supersedes the monolithic `Roadmap.exists_simplePole_of_genus_zero`
(same statement, finer inputs); filling those two inputs discharges the #1 chain. -/
theorem exists_simplePole_of_genus_zero_via_RR (h : genus X = 0) :
    ∃ (P : X) (f : MeromorphicFunction X), IsSimplePoleFunction f P := by
  obtain ⟨P, f, hpb, hnc⟩ := exists_poleBounded_nonconstant_of_genus_zero h
  exact ⟨P, f, isSimplePole_of_poleBounded_nonconstant f hpb hnc⟩

/-- **#1 fully reduced through the RR layer.** `genus_zero_iff_homeo_via_RR` with the RR consequence
replaced by its finer inputs: genus `0` ⟺ `X ≃ₜ S²`, modulo
`exists_poleBounded_nonconstant_of_genus_zero` (RR), `exists_pole_of_nonconstant` (Liouville),
`homeo_sphere_of_exists_simplePole` (ℂℙ¹ endgame), `genus_zero_of_homeo_sphere` (Ω(ℂℙ¹)=0). -/
theorem genus_zero_iff_homeo_via_RR' :
    genus X = 0 ↔ Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ⟨fun h => homeo_sphere_of_exists_simplePole (exists_simplePole_of_genus_zero_via_RR h),
   genus_zero_of_homeo_sphere⟩

end Jacobians.Roadmap
