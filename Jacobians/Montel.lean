import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Seminorm
import Jacobians.Genus
import Jacobians.Montel.Cover
import Jacobians.Montel.LocalRep
import Jacobians.Montel.ChartNorm
import Jacobians.Montel.SupNorm
import Jacobians.Montel.Compactness

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

/-! ### Embedding norm bound (B.9 step 3b — boundedness)

Under the canonical supNormK-based `NormedAddCommGroup`, each
per-chart bcf component of the embedding satisfies `‖·‖ ≤ ‖α‖`. This
is the boundedness that gives continuity of the linear embedding
(Φ α x₀ := `mkOfCompact (localRepOnInnerShrunk α x₀)`) into the
product space. -/

/-- **Boundedness of the bcf-embedding component.**
Under `HolomorphicOneForms.normedAddCommGroup`, the norm of
`mkOfCompact (localRepOnInnerShrunk α x₀)` is bounded by `‖α‖`. -/
theorem norm_mkOfCompact_localRepOnInnerShrunk_le
    (α : Jacobians.HolomorphicOneForms X) (x₀ : X) :
    letI := innerShrunkChart_compactSpace (X := X) x₀
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    ‖BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀)‖ ≤ ‖α‖ := by
  letI := innerShrunkChart_compactSpace (X := X) x₀
  letI := HolomorphicOneForms.normedAddCommGroup (X := X)
  -- BCF norm via mkOfCompact equals ContinuousMap norm.
  rw [BoundedContinuousFunction.norm_mkOfCompact]
  by_cases hx₀ : x₀ ∈ (chartCover : Finset X)
  · exact norm_localRepOnInnerShrunk_le_supNormK α hx₀
  · -- Out of chartCover: innerShrunkChart empty, continuous map is 0.
    have h_iso : IsEmpty (innerShrunkChart (X := X) x₀) :=
      Set.isEmpty_coe_sort.mpr (innerShrunkChart_eq_empty x₀ hx₀)
    have h0 : localRepOnInnerShrunk α x₀ = 0 := by
      ext y; exact h_iso.false y |>.elim
    rw [h0, norm_zero]
    exact norm_nonneg _

/-! ### The per-chart continuous linear embedding (B.9 step 3b)

Packages the embedding `α ↦ mkOfCompact (localRepOnInnerShrunk α x₀)`
as a `ContinuousLinearMap` from `HOF X` (with the supNormK-based
normed structure) to `innerShrunkChart x₀ →ᵇ ℂ`. Continuity follows
from the boundedness `‖·‖ ≤ ‖α‖` via `LinearMap.mkContinuous`. -/

/-- Per-chart bcf-embedding as a `ContinuousLinearMap`. -/
noncomputable def HolomorphicOneForms.embedInnerBcf (x₀ : X) :
    letI := innerShrunkChart_compactSpace (X := X) x₀
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    letI := HolomorphicOneForms.normedSpace (X := X)
    Jacobians.HolomorphicOneForms X →L[ℂ]
      BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ := by
  letI := innerShrunkChart_compactSpace (X := X) x₀
  letI := HolomorphicOneForms.normedAddCommGroup (X := X)
  letI := HolomorphicOneForms.normedSpace (X := X)
  refine LinearMap.mkContinuous
    { toFun := fun α => BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀)
      map_add' := ?_
      map_smul' := ?_ } 1 ?_
  · intro α β
    apply BoundedContinuousFunction.ext_iff.mpr
    intro y
    have hfn : localRepOnInnerShrunk (α + β) x₀ =
        localRepOnInnerShrunk α x₀ + localRepOnInnerShrunk β x₀ :=
      localRepOnInnerShrunk_add α β x₀
    simp only [BoundedContinuousFunction.mkOfCompact_apply,
      BoundedContinuousFunction.coe_add, Pi.add_apply, hfn,
      ContinuousMap.add_apply]
  · intro c α
    apply BoundedContinuousFunction.ext_iff.mpr
    intro y
    have hfn : localRepOnInnerShrunk (c • α) x₀ = c • localRepOnInnerShrunk α x₀ :=
      localRepOnInnerShrunk_smul c α x₀
    simp only [BoundedContinuousFunction.mkOfCompact_apply,
      BoundedContinuousFunction.coe_smul, RingHom.id_apply, hfn,
      ContinuousMap.smul_apply]
  · intro α
    calc ‖BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀)‖
        ≤ ‖α‖ := norm_mkOfCompact_localRepOnInnerShrunk_le α x₀
      _ = 1 * ‖α‖ := (one_mul _).symm

/-- The continuous linear map's value at α is `mkOfCompact (localRepOnInnerShrunk α x₀)`. -/
theorem HolomorphicOneForms.embedInnerBcf_apply (x₀ : X) (α : Jacobians.HolomorphicOneForms X) :
    letI := innerShrunkChart_compactSpace (X := X) x₀
    letI := HolomorphicOneForms.normedAddCommGroup (X := X)
    letI := HolomorphicOneForms.normedSpace (X := X)
    (HolomorphicOneForms.embedInnerBcf x₀ : _ →L[ℂ] _) α =
      BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α x₀) := rfl

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

/-! ### Current state of the closedBall_isCompact proof

**Arzelà–Ascoli infrastructure — COMPLETE** (see `Jacobians/Montel/Compactness.lean`):
- [x] B.3 `localRep_analyticOn_chartTarget` (ContMDiff ω ⇔ AnalyticOn ℂ
      bridge at bundle-section level).
- [x] B.4 `exists_cauchy_deriv_bound` (uniform derivative bound on
      compact ⊂ open).
- [x] B.5 `exists_cauchy_lipschitz_bound` (uniform Lipschitz on convex
      compact).
- [x] B.6 `uniformEquicontinuousOn_of_bounded_analyticOn` (uniform
      equicontinuity on convex compacta).
- [x] B.7b `equicontinuousAt_localRep_on_innerShrunkChart` + its
      `Equicontinuous` form (pointwise equicontinuity on innerShrunkChart,
      the Arzelà-ready domain).
- [x] B.8 `isCompact_closure_image_inner_bcf` (per-chart Arzelà
      relative compactness).
- [x] B.9 step 1 `isCompact_univ_pi_closure_image_inner_bcf` (univ-pi
      product compactness).
- [x] B.9 step 2 `embedding_in_univ_pi_closure` (embedding lands in
      compact product).
- [x] B.9 step 3a `eq_of_mkOfCompact_localRepOnInnerShrunk_eq`
      (embedding injectivity via 1-dim tangent argument).
- [x] Linearity: `localRepOnInnerShrunk_add` / `..._smul`.

**Infrastructure refactor** — Cover.lean now provides inner/outer
double shrinkage via `exists_subset_iUnion_closure_subset` applied
twice: `innerShrunkChart ⊆ chartOpen ⊆ shrunkChart ⊆ chartSource`,
with `chartOpen` open.

**Remaining steps to close this sorry:**
- [ ] B.9 step 3b: **Embedding continuity.** Bound `‖Φ α x₀‖_{bcf} ≤ ‖α‖`
      and package as `ContinuousLinearMap`. Best done here (Montel.lean)
      since `HolomorphicOneForms.normedAddCommGroup` is in scope.
- [ ] B.10: **Closedness of embedded closedBall.** Uniform limits of
      holomorphic sections are holomorphic via
      `TendstoLocallyUniformlyOn.analyticOn`. The subtle piece: glue
      per-chart limits into a global bundle section. Requires
      reconstructing α from its chart-local representatives and showing
      smoothness class ω preserved under uniform limits.
- [ ] Final assembly: `IsCompact (closedBall 0 1)` via closed subset of
      compact image under the continuous embedding.

**Estimated scope**: B.10 is the main content — multi-session work,
requiring an `AnalyticOn`-to-`ContMDiffSection ω` transfer at the bundle
level. B.9 step 3b + Assembly are mechanical once B.10 lands.
-/

end Jacobians.Montel
