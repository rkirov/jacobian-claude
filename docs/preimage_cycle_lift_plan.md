# Preimage-cycle lift — completion plan

Continuation plan for `exists_preimageCycle_of_off_branchLocus`
(`Jacobians/TracePullback.lean`), the geometric heart of the Jacobian
pushforward∘pullback = degree identity. This is the "§3 / loop-lifting machinery"
referenced throughout the codebase. Written 2026-05-30 after sub-piece A landed.

## Goal

`exists_preimageCycle_of_off_branchLocus (f hf hnonconst) (δ) (hδ : IsClosedSmoothLoop δ)
(havoid : ∀ t, δ t ∉ branchLocus f) : Nonempty (PreimageCycle f hf δ)`.

A `PreimageCycle` bundles: `n`, `loops : Fin n → ℝ → X`, `loops_smooth` (each
`IsClosedSmoothLoop`), `coeffs : Fin n → ℤ`, `sheets : ℕ`, and the two identities
- `pullback_eq : ambientPullbackJac f hf (periodVec δ) = ∑ i, coeffs i • periodVec (loops i)`
- `pushforward_eq : ∑ i, coeffs i • periodVec (f ∘ loops i) = (sheets : ℤ) • periodVec δ`.

## Status

- **A — continuous path-lift: DONE, sorry-free** (`exists_continuous_lift_off_branchLocus`,
  commit `32d435e`). `δ` off-branch lifts through the proven covering via Mathlib's
  `IsCoveringMap.liftPath`, repackaged to `ℝ → X` with `Set.projIcc`. `#print axioms` =
  `[propext, Classical.choice, Quot.sound]`. (Added `import Mathlib.Topology.Homotopy.Lifting`.)
- **B — smoothness of the lift: DONE, sorry-free**
  (`differentiableAt_chart_lift_of_notMem_criticalSet`). A continuous lift `Γ` of `δ`
  through a non-critical point is chart-pullback-differentiable wherever `δ` is.
  Proof exactly as planned: two-sided local inverse `g` at `Γ t₀`, `Γ =ᶠ g∘δ` near `t₀`
  (no lift-uniqueness needed), `G∘d` chart factorization, `g` holomorphic ⇒ `ℝ`-diff via
  `writtenInExtChartAt`+`restrictScalars`. `#print axioms` = `[propext, Classical.choice,
  Quot.sound]`. Compiled essentially first-try (mirrors `IsClosedSmoothLoop.comp`).

## Proven infrastructure to build on

- **Covering**: `isCoveringMap_restrictPreimage_compl_branchLocus` (PeriodLattice) — a genuine
  `IsCoveringMap` of `(univ \ branchLocus f).restrictPreimage f` on subtypes. Mathlib
  `IsCoveringMap.liftPath` / `liftPath_trans` / `liftPath_apply_one_eq_of_homotopicRel`
  (`Mathlib.Topology.Homotopy.Lifting`). NB: `IsCoveringMap` unfolds to a Pi type, so
  dot-notation fails — use explicit `IsCoveringMap.liftPath cov …`.
- **Local sections**: `exists_twoSided_localInverse` (TraceForm.lean) — at any non-critical
  `x₀`, a holomorphic `g` with `f∘g=id` on open `V∋f x₀`, `g∘f=id` near `x₀`, `g(f x₀)=x₀`,
  `g` `C^ω` on `V`. Also `exists_holo_localInverse_of_notMem_criticalSet`, `isLocalHomeoOffCritical`.
- **Fibre finiteness**: `fiber_finite_off_branchLocus` (PeriodLattice) — `(f⁻¹'{y}).Finite` off-branch
  (= the sheet count, classically `deg f`).
- **Line-integral change of variables**: `lineIntegral_pullback` (LineIntegral.lean, PROVEN),
  `periodVec_comp_eq_lineIntegral_pullback`, `periodVec_pushforward` (PeriodLattice).
- **Trace off-branch**: `traceForm_toFun_of_notMem_branchLocus` (TraceForm.lean) — off-branch
  `traceForm = traceFun = ∑ sheets sheetPullback`.
- **Chart chain-rule template**: `pathSpeed_comp_eq_mfderiv` (LineIntegral.lean:492-576) — the
  `chartY ∘ map ∘ chartX.symm` differentiability pattern, to be mirrored in B.

## Remaining steps

### B — smoothness of the lift — **DONE, sorry-free**
`differentiableAt_chart_lift_of_notMem_criticalSet` (TracePullback.lean): given `Γ`
continuous at `t₀`, `∀ᶠ t in 𝓝 t₀, f (Γ t) = δ t`, `Γ t₀ ∉ criticalSet f`, and
`δ` chart-pullback-diff at `t₀`, then `Γ` is chart-pullback-diff at `t₀`. Proof exactly
as the plan predicted (two-sided inverse `g`, `Γ =ᶠ g∘δ`, `G∘d` factorization,
`writtenInExtChartAt`+`restrictScalars`). Compiled essentially first-try. **NB the
hypothesis is `ContinuousAt Γ t₀` + the *eventually* `f∘Γ=δ`** — for A's `projIcc`-clamped
lift this `∀ᶠ` holds only for `t₀ ∈ (0,1)` (open interval), NOT at the endpoints `0,1`,
because outside `[0,1]` the clamped lift is constant while `δ` is not. So **B gives lift
differentiability on `(0,1)` only**; the endpoint/seam differentiability is the C difficulty.

### D-algebra — period-level matrix↔integral bridge — **DONE, sorry-free**
`ambientPullbackJac_periodVec_apply_eq_lineIntegral_traceFormTotal` (TracePullback.lean):
`(ambientPullbackJac f hf (periodVec δ))_i = ∫_δ traceFormTotal f hf (ωᵢ^X)`. Pure linear
algebra + `lineIntegral` linearity, dual to `periodVec_pushforward`. **This reduces
`pullback_eq` to the geometric projection identity** `∫_δ trace(ωᵢ) = ∑_loops coeffs·∫_loop ωᵢ`.

### D-geom infra — local sheet decomposition — **DONE, sorry-free**
`exists_localSheetSystem_traceForm_eq_sum` (TraceForm.lean): off-branch there is a local
sheet system `S` at `y₀` with, for off-branch `y ∈ S.V`,
`(traceForm f hf hnonconst α).toFun y = ∑ᵢ sheetPullback α (S.sheet i) y`. The per-base
input to the projection formula.

### C — seam smoothness **SOLVED, sorry-free**; monodromy/orbit + integrability still open
**Seam-smoothness fix — DONE** (`flatEndReparam` + `exists_smoothLift_flatEnd_off_branchLocus`,
sorry-free, axioms `[propext, Classical.choice, Quot.sound]`). The gating sub-problem the earlier
plan flagged is resolved by a *better choice of reparametrization*: `flatEndReparam` is **constant
near the endpoints** (a genuine plateau, `Real.smoothTransition (2t−1/2)`), NOT merely zero-derivative
like the cubic `smoothStep01`. Lifting `δ ∘ flatEndReparam` from a fibre point `e` then gives a lift
that is literally *constant* near `0,1` (continuity + local injectivity of `f`, using A's now-exposed
`projIcc` clamp facts `Γ≡e on (-∞,0]`, `Γ≡Γ 1 on [1,∞)`) — hence two-sided differentiable with zero
velocity there, with NO one-sided gluing; the interior is plain B. Output: `Γ` continuous, `Γ 0 = e`,
`f(Γ t)=δ(flatEndReparam t)` on `[0,1]`, chart-diff on all `[0,1]`, `pathSpeed Γ 0 = pathSpeed Γ 1 = 0`,
and `f(Γ 1)=δ 0` (monodromy target in the fibre). (A was extended to expose its clamp; no callers broke.)

**Still open for C:**
 1. **Integrability** of the lift's integrand `t ↦ ωᵢ(Γ t)(pathSpeed Γ t)` on `[0,1]` — the one
    `IsSmoothPath` field not yet provided. Hard part is the middle `[1/4,3/4]` (plateau ends give `0`);
    there `Γ = g∘δr` locally ⇒ integrand `= (pullbackForm g ωᵢ)(δr ·)(pathSpeed δr ·)`, a ℂ-combination
    of `δ`-basis integrands reparametrized by `flatEndReparam` — reduce to `δ`'s given integrability via
    a change-of-variables/`comp`-integrability lemma. (Patchwork of local `g`'s ⇒ needs a cover/partition.)
 2. **Monodromy permutation** `σ : F → F`, `σ e = Γ_e 1`, on the finite fibre `F=f⁻¹'{δ 0}`
    (`fiber_finite_off_branchLocus` ⇒ `Fintype`); bijective by lift uniqueness (`IsCoveringMap` /
    reversed-loop lift). Package `e ↦ Γ_e` as a function (choice over the fibre).
 3. **Orbit concatenation** into closed loops via `IsSmoothPath.concat` (zero junction velocities ✓
    from the seam fix) + `periodVec_concat_of_smooth`; `n`=#orbits, `coeffs i = 1`, `sheets = card F`.
 4. **Reparam-invariance** `periodVec (δ ∘ flatEndReparam) = periodVec δ` (change of variables for
    `lineIntegral` under the monotone reparam fixing `0,1`) — to transport the final `PreimageCycle`
    from `δ∘flatEndReparam` back to `δ` (via `PreimageCycle.congr_periodVec`).

### D-geom — projection formula (open; infra now all present)
Goal `∫_δ traceFormTotal f hf ωᵢ = ∑_loops coeffs·periodVec(loop)_i` (then `pullback_eq`
via D-algebra). Partition `[0,1]` by `exists_nbhd_cover` (Lebesgue, uniform `k/n` grid) so each
segment `δ|[k/n,(k+1)/n]` lands in some base `S_k.V` (from `exists_localSheetSystem_traceForm_eq_sum`).
On each segment `∫ trace(ωᵢ) = ∑_sheets ∫ sheetPullback = ∑_sheets ∫_{sheet∘δ|seg} ωᵢ`
(`lineIntegral_pullback_section`). **Remaining bookkeeping:** the per-segment sheet pieces
`sheet∘δ|seg` match across segment boundaries (lift continuity/uniqueness) and reassemble into the
global lifts `Γ_e`, then group by `σ`-orbit into the `loops`. This index-matching is the combinatorial
heart shared with C. Off-branch throughout ⇒ **no branch-point continuity needed** (unlike `traceForm_comp`).

### E — pushforward_eq (open; reduces to concat bookkeeping)
`∑ coeffs • periodVec (f ∘ loops) = sheets • periodVec δ`. Each `f∘loop` over an orbit of length
`ℓ` is `δ` traversed `ℓ` times (`f∘Γ_e=δ`); `periodVec(f∘loop)=ℓ•periodVec δ` via
`periodVec_concat_of_smooth`; `∑_orbits ℓ = card F = sheets`.

### F — assemble `PreimageCycle` from C–E and conclude `Nonempty`.

## Infrastructure confirmed available (2026-05-30 audit)
All non-monodromy ingredients are now proven: A (`exists_continuous_lift_off_branchLocus`),
B (`differentiableAt_chart_lift_of_notMem_criticalSet`), the matrix↔integral bridge,
`exists_localSheetSystem`(+`_traceForm_eq_sum`), `exists_nbhd_cover` (partition),
`lineIntegral_pullback_section`, `IsSmoothPath.concat`/`periodVec_concat_of_smooth`,
`fiber_finite_off_branchLocus`. **The sole remaining content is the monodromy/seam/reassembly
combinatorics (C + D-geom + E + F), one interconnected argument — the seam-smoothness fix (C
option i) is the gating sub-problem.**

## Separately recorded: `traceForm_comp` is infrastructure-blocked

The other open trace gap, `traceForm_comp` (TraceForm.lean, the `(g∘f)₊ = g₊∘f₊` functoriality
law), is NOT a quick win. Both a density+continuity proof and the `exists_traceForm` framework
need `ContinuousAt` of an opaque `traceForm.choose`'s *coefficient* at branch points — i.e. a
general **cotangent-hom-bundle coefficient-continuity extractor** (`contMDiffAt_hom_bundle`-style,
~40-80 lines of bundle work). Two subagents stalled there. Unlike D above, `traceForm_comp` cannot
avoid branch-point continuity. `traceForm_id` IS done (commit `2c2ad32`) because `branchLocus(id)=∅`.
