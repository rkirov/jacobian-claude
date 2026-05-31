/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Abel
import Jacobians.Genus
import Jacobians.Degree

/-!
# Sorry-free roadmap — the analytic frontier, scaffolded in code

This file encodes the plan for a **fully sorry-free** project (see
`docs/{abel_riemannroch,riemann_roch,dolbeault_hodge_feasibility,loop_off_branch}_research.md`)
as Lean declarations, so the dependency structure lives in code, not only in docs. The headline
sorries (#1 `genus_eq_zero_iff_homeo`, #3 `abelJacobi_twoPoint_ne_zero`) are here **reduced** —
*proven* — to a small set of named analytic inputs, each a precise `sorry` to be filled bottom-up.

> **⚠ TEMPORARY SCAFFOLD — not the permanent home.** This single file is a *staging area* for the
> plan. As each input gets filled, it should be **moved into the project's proper module/directory
> structure** — e.g. `Jacobians/ProjectiveLine.lean` (the ℂℙ¹ manifold), `Jacobians/Dolbeault/…`,
> `Jacobians/RiemannRoch/…`, `Jacobians/Hodge/…` — and the headline theorems discharged in their own
> modules (`Genus.lean`, `Abel.lean`), not here. This file is imported by nothing and carries no
> load; entries should be deleted as they graduate to real modules. Do not let it become a dumping
> ground or a parallel source of truth.

**The shared wall.** #1, #3, and #7 all bottom out in **Dolbeault ∂̄-solvability + de Rham/Hodge**
on the surface (Mathlib has none of it for manifolds). This is the dominant, unavoidable cost of a
zero-axiom project. We de-risk it with two bounded Phase-0 probes below before committing.

## Phase 0 — bounded de-risking probes (no Dolbeault)
* `dbar`, `dbar_disk_solvable` — the planar ∂̄ (Cauchy transform) on a disk; scopes whether the
  global Dolbeault layer is ~3k or ~6k+ LoC.
* `homeo_sphere_of_exists_simplePole` — folds the complex-ℂℙ¹ shim + "degree-1 map ⟹ biholomorphism"
  endgame into one input (shared by #1 and #3). The ℂℙ¹ manifold (Mathlib has no complex `ℙ¹`) is the
  most-leveraged buildable piece and is internal to this input.
* #6 `exists_loop_off_branchLocus` — independent of the Dolbeault wall (manifold-Stokes-on-a-square);
  handled separately (see `docs/loop_off_branch_research.md`).

## Phase 1 — the wall
Global Dolbeault ∂̄-solvability / finiteness of `H¹(X,𝒪)` (Forster §14, Montel-based; the repo already
has Montel). Behind `exists_simplePole_of_genus_zero` (via Riemann–Roch) and
`exists_meromorphic_of_abelJacobi_zero` (Abel sufficiency). Not yet stated formally here — its faithful
statement needs sheaf-cohomology/`𝒪_D` defs to be built first; tracked as the next scaffolding layer.

## Phase 2 — build on the wall
de Rham/Hodge → #7 via the Hodge–Riemann relations (supersedes the cut-surface/`exists_cutSurface`
route; the `CutSurface` `boundaryForm`/Green stack is reused in Serre duality's residue pairing) →
Serre duality → Riemann–Roch → discharge `exists_simplePole_of_genus_zero`,
`exists_meromorphic_of_abelJacobi_zero`, `meromorphic_div_deg_zero`.

Every `sorry` here is a precise, named classical input; none is load-bearing for the existing
challenge build (this file is downstream and imported by nothing).
-/

set_option linter.unusedSectionVars false

namespace Jacobians.Roadmap

open scoped Manifold ContDiff Topology
open Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Phase 0 — the ∂̄-on-a-disk probe (planar, no manifolds) -/

/-- The Cauchy–Riemann **∂̄ operator** (Wirtinger derivative) of `f : ℂ → ℂ`:
`∂̄f = ½(∂f/∂x + i·∂f/∂y)`, written via the real Fréchet derivative (`1` = `∂/∂x` direction,
`I` = `∂/∂y` direction). `f` is holomorphic at `z` iff `∂̄f z = 0`. -/
noncomputable def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I)

/-- **Phase-0 probe: ∂̄ is solvable on a disk** (the Cauchy transform). For continuous `g` on a
closed disk there is a `C¹` `f` with `∂̄f = g` on the open disk. This is the *local* heart of
Dolbeault — elementary planar complex analysis — and proving it scopes the cost of the global
`H¹(X,𝒪)` layer (Phase 1). (Classical: `f(z) = (1/2πi)∬ g(ζ)/(ζ−z) dζ∧dζ̄`.) -/
theorem dbar_disk_solvable {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : ContinuousOn g (Metric.closedBall 0 r)) :
    ∃ f : ℂ → ℂ, (∀ z ∈ Metric.ball (0 : ℂ) r, DifferentiableAt ℝ f z) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) r, dbar f z = g z :=
  sorry

/-! ## The common endgame — "degree-1 meromorphic function ⟹ sphere"

A non-constant meromorphic function with a single simple pole is a degree-1 holomorphic map
`X → ℂℙ¹`, hence (proper, degree 1) a biholomorphism, so `X` is homeomorphic to the 2-sphere. This
single input is shared by both #1 and #3 and *contains* the complex-ℂℙ¹ manifold shim (Phase 0). -/

/-- A meromorphic function with a **single simple pole** at `P` and holomorphic elsewhere — i.e. a
degree-1 map `X → ℂℙ¹`. -/
def IsSimplePoleFunction (f : MeromorphicFunction X) (P : X) : Prop :=
  f.orderAtPoint P = -1 ∧ ∀ x, x ≠ P → 0 ≤ f.orderAtPoint x

/-- **[INPUT — Phase 0, contains the ℂℙ¹ shim]** A single-simple-pole function forces `X` to be the
sphere. (Degree-1 holomorphic map to `ℂℙ¹` ⟹ biholomorphism ⟹ `X ≃ₜ S²`; Forster §4.24 + the ℂℙ¹
manifold, which Mathlib lacks.) -/
theorem homeo_sphere_of_exists_simplePole
    (h : ∃ (P : X) (f : MeromorphicFunction X), IsSimplePoleFunction f P) :
    Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  sorry

/-- **[INPUT — Phase 2, the converse half]** The sphere has genus `0`: `Ω(ℂℙ¹) = 0`. Mechanical once
the ℂℙ¹ manifold + `Ω(ℂℙ¹)=0` are built (Phase 0/2). -/
theorem genus_zero_of_homeo_sphere
    (h : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    genus X = 0 :=
  sorry

/-! ## #1 — genus 0 ⟺ sphere, REDUCED (proven from the inputs above) -/

/-- **[INPUT — Phase 1/2, Riemann–Roch]** Genus `0` ⟹ a degree-1 meromorphic function exists. This is
the Riemann–Roch consequence `l(P) = 2` (Forster §16: `l(P) = deg P + 1 − g + l(K−P) = 1+1−0+0`),
resting on the Dolbeault/Serre wall. -/
theorem exists_simplePole_of_genus_zero (h : genus X = 0) :
    ∃ (P : X) (f : MeromorphicFunction X), IsSimplePoleFunction f P :=
  sorry

/-- **#1 `genus_eq_zero_iff_homeo`, REDUCED.** Proven from the Riemann–Roch consequence
(`exists_simplePole_of_genus_zero`), the degree-1-⟹-sphere endgame
(`homeo_sphere_of_exists_simplePole`), and `Ω(ℂℙ¹)=0` (`genus_zero_of_homeo_sphere`). Filling those
three inputs discharges `Jacobians.genus_eq_zero_iff_homeo`. -/
theorem genus_zero_iff_homeo_via_RR :
    genus X = 0 ↔ Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  ⟨fun h => homeo_sphere_of_exists_simplePole (exists_simplePole_of_genus_zero h),
   genus_zero_of_homeo_sphere⟩

/-! ## #3 — Abel non-vanishing, REDUCED (proven from Abel sufficiency + the endgame) -/

/-- **[INPUT — Phase 1/2, Abel sufficiency]** If `abelJacobi D = 0` then `D` is principal: some
meromorphic `f` has divisor exactly `D` (Abel 1826, Forster §20.7a — the hard half, needing
weak-solutions + Dolbeault, or third-kind differentials + Riemann–Roch). -/
theorem exists_meromorphic_of_abelJacobi_zero (D : DivisorOfDegZero X)
    (h : abelJacobi D = 0) :
    ∃ f : MeromorphicFunction X, f.div = (D : Divisor X) :=
  sorry

/-- The divisor of a single-simple-pole/zero function realizing `P − Q` (`P ≠ Q`) gives a
single-simple-pole function at `Q`. -/
theorem isSimplePole_of_div_twoPoint {P Q : X} (hPQ : P ≠ Q)
    (f : MeromorphicFunction X) (hf : f.div = twoPointDivisor X P Q) :
    IsSimplePoleFunction f Q := by
  classical
  have hkey : ∀ x, f.orderAtPoint x = (twoPointDivisor X P Q) x := by
    intro x; rw [← hf]; rfl
  constructor
  · rw [hkey]
    simp [twoPointDivisor, Finsupp.sub_apply, hPQ]
  · intro x hx
    rw [hkey]
    simp only [twoPointDivisor, Finsupp.sub_apply, Finsupp.single_apply,
      if_neg (fun h : Q = x => hx h.symm)]
    split <;> omega

/-- **#3 `abelJacobi_twoPoint_ne_zero`, REDUCED.** Proven from Abel sufficiency
(`exists_meromorphic_of_abelJacobi_zero`) + the degree-1-⟹-sphere endgame + `Ω(ℂℙ¹)=0`: if
`abelJacobi (P−Q) = 0` then `P−Q` is principal, giving a degree-1 function, forcing `genus X = 0`,
contradicting `0 < genus X`. -/
theorem abelJacobi_twoPoint_ne_zero_via_abel
    (hg : 0 < genus X) {P Q : X} (hPQ : P ≠ Q) :
    abelJacobi ⟨twoPointDivisor X P Q, twoPointDivisor_mem_degZero X P Q⟩ ≠ 0 := by
  intro hzero
  obtain ⟨f, hf⟩ := exists_meromorphic_of_abelJacobi_zero
    ⟨twoPointDivisor X P Q, twoPointDivisor_mem_degZero X P Q⟩ hzero
  have hsphere := homeo_sphere_of_exists_simplePole
    ⟨Q, f, isSimplePole_of_div_twoPoint hPQ f hf⟩
  exact absurd (genus_zero_of_homeo_sphere hsphere) hg.ne'

/-! ## #7 (Hodge route) and `deg(div f)=0` — Phase 2 leaves

`exists_periodLattice_realBasis` (#7) is currently proven via the cut-surface route modulo
`exists_cutSurface` (surface classification). On Path 1 it switches to the **Hodge–Riemann** route
(`dim H¹ = 2g` + period-pairing nondegeneracy), built on the same Dolbeault/de-Rham foundation; not
yet stated here (needs the de Rham / harmonic-forms defs). -/

/-- **[INPUT — Phase 2]** Every principal divisor has degree `0` on a compact Riemann surface
(Forster Cor 4.25; sum of residues of `df/f` is `0`). Needed by both #1 and #3 endgames. -/
theorem meromorphic_div_deg_zero (f : MeromorphicFunction X)
    (hf : ∃ x, f.toFun x ≠ 0) :
    Divisor.deg X f.div = 0 :=
  sorry

end Jacobians.Roadmap
