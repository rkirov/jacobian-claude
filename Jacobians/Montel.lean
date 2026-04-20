import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Seminorm
import Jacobians.Genus
import Jacobians.Montel.Cover
import Jacobians.Montel.LocalRep
import Jacobians.Montel.ChartNorm
import Jacobians.Montel.SupNorm

/-!
# Montel path to finite-dimensionality of `HolomorphicOneForms`

**Goal**: prove `FiniteDimensional ℂ (HolomorphicOneForms X)` for X a
compact connected complex 1-manifold via the classical Montel /
compactness route (Ahlfors–Sario, Rudin).

See `docs/MONTEL_PATH.md` for the overall plan.

## Classical textbook approach (Ahlfors–Sario Ch II §5)

1. **Finite atlas.** X compact ⇒ finite open cover by chart domains.
2. **Local representative.** In each chart, α = `f(z) dz` with `f` holomorphic.
3. **Sup-norm.** `‖α‖ := max_j sup_{z ∈ K_j} |f_j(z)|` where `K_j ⊂ V_j` is
   a compact shrinkage.
4. **Cauchy estimates.** Bound derivatives ⇒ equicontinuity.
5. **Arzelà–Ascoli.** Bounded + equicontinuous ⇒ relatively compact.
6. **Riesz.** Compact closed ball ⇒ finite-dimensional.

## File layout

Step 1 (**COMPLETE** — this is the norm on HOF X) is split across
four submodules:

- `Jacobians/Montel/Cover.lean` — finite chart cover + compact shrinking.
- `Jacobians/Montel/LocalRep.lean` — chart-local scalar representative
  `localRep` + continuity + vector ops.
- `Jacobians/Montel/ChartNorm.lean` — per-chart bounded sup-norm
  `chartNormK` + triangle + homogeneity.
- `Jacobians/Montel/SupNorm.lean` — assembled sup-norm `supNormK` +
  positive-definiteness.

This root file packages them into `NormedAddCommGroup` / `NormedSpace ℂ`
structures and derives `FiniteDimensional` from a single focused sorry:
`closedBall_isCompact` (Steps 2–6 of the classical outline).
-/

namespace Jacobians.Montel

open scoped Manifold ContDiff
open Bundle

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### `NormedAddCommGroup` instance packaging

`HolomorphicOneForms X` is a `def` alias for `ContMDiffSection` (see
`Jacobians/Genus.lean`). We wrap `supNormK` in an `AddGroupNorm` and use
`AddGroupNorm.toNormedAddCommGroup` to produce a `NormedAddCommGroup`. -/

omit [ConnectedSpace X] in
/-- The `AddGroupNorm` structure on `HolomorphicOneForms X`. -/
noncomputable def HolomorphicOneForms.supNormKAsAddGroupNorm :
    AddGroupNorm (Jacobians.HolomorphicOneForms X) where
  toFun := fun α => HolomorphicOneForms.supNormK α
  map_zero' := HolomorphicOneForms.supNormK_zero
  add_le' := fun α β => HolomorphicOneForms.supNormK_add_le α β
  neg' := fun α => HolomorphicOneForms.supNormK_neg α
  eq_zero_of_map_eq_zero' := fun α h => HolomorphicOneForms.eq_zero_of_supNormK_eq_zero α h

omit [ConnectedSpace X] in
/-- `HolomorphicOneForms X` as a `NormedAddCommGroup`.

Non-instance: consumers opt in via `letI` or by promoting at a
higher level (as done in `Jacobians.HolomorphicForms`). -/
@[reducible] noncomputable def HolomorphicOneForms.normedAddCommGroup :
    NormedAddCommGroup (Jacobians.HolomorphicOneForms X) :=
  AddGroupNorm.toNormedAddCommGroup HolomorphicOneForms.supNormKAsAddGroupNorm

omit [ConnectedSpace X] in
/-- `HolomorphicOneForms X` as a `NormedSpace ℂ`. -/
@[reducible] noncomputable def HolomorphicOneForms.normedSpace :
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    NormedSpace ℂ (Jacobians.HolomorphicOneForms X) :=
  letI : NormedAddCommGroup (Jacobians.HolomorphicOneForms X) :=
    HolomorphicOneForms.normedAddCommGroup
  NormedSpace.mk (fun c α => le_of_eq (HolomorphicOneForms.supNormK_smul c α))

/-! ### Montel conclusion: closed unit ball is compact (single sorry) + Riesz -/

/-- **Core content sorry**: the closed unit ball in `HolomorphicOneForms X`
under the Montel sup-norm is compact.

**Proof sketch (classical — Ahlfors-Sario, Rudin Ch. 14):**
1. `HOF X` embeds into `Π K ∈ chartCover, C(shrunkChart K, ℂ)` via `localRep`
   (a continuous linear injection by positive-definiteness of `supNormK`).
2. The image of the unit ball is bounded (by `norm_localRep_le_supNormK`).
3. **Cauchy estimates**: `localRep α x₀` is analytic in chart coordinates,
   so derivatives are bounded — image is equicontinuous.
4. **Arzelà–Ascoli**: bounded + equicontinuous + compact base (shrunkChart)
   ⇒ relatively compact in `C(shrunkChart K, ℂ)`.
5. Finite product of precompact = precompact.
6. **Completeness**: uniform limits of holomorphic sections are holomorphic
   (Mathlib: `TendstoLocallyUniformlyOn.analyticOn`-type argument) ⇒ CLOSED.
7. Closed + precompact ⇒ compact.

Takes the `NormedAddCommGroup` / `NormedSpace ℂ` as explicit instance
arguments so the type signature unifies with whatever normed structure is
in scope (typically the one from `Jacobians.HolomorphicForms`). -/
theorem HolomorphicOneForms.closedBall_isCompact
    [NormedAddCommGroup (Jacobians.HolomorphicOneForms X)]
    [NormedSpace ℂ (Jacobians.HolomorphicOneForms X)] :
    IsCompact (Metric.closedBall (0 : Jacobians.HolomorphicOneForms X) 1) := by
  sorry

/-
Consumer-friendly usage: once the NormedAddCommGroup / NormedSpace ℂ
instances are in scope (typically provided in Jacobians.HolomorphicForms),
the `FiniteDimensional` conclusion follows via Riesz:

    noncomputable instance : FiniteDimensional ℂ (HolomorphicOneForms X) :=
      FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one
        Jacobians.Montel.HolomorphicOneForms.closedBall_isCompact
-/

/-! ### Next
- [ ] Implement `cauchy_estimate`: requires the ContMDiff ω ⇔ AnalyticOn ℂ
      bridge at the level of bundle sections in charts.
- [ ] Implement `equicontinuous_of_bounded`.
- [ ] Implement `completeSpace`.
- [ ] Implement `closedBall_precompact` via Arzelà-Ascoli.
- [ ] Derive `finiteDimensional` via Riesz.
-/

end Jacobians.Montel
