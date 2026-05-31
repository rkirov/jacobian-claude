# Plan — discharge #4 `traceExtendsAt_branchPoint` (the trace's branch-point extension)

**Goal** (`Jacobians/TraceForm.lean:843`): for a branch point `y₀ ∈ branchLocus f`,
the canonical extension `traceFunExt f α` is, at `y₀`,
* `ContMDiffAt` as a cotangent-bundle section (`traceTotalSpaceMk (traceFunExt f α)`), **and**
* `ContinuousAt` as a coefficient `Y → (ℂ →L[ℂ] ℂ)`.

Discharging this is the **single remaining analytic fact** of the trace; everything
downstream (regluing, ℂ-linearity, `exists_traceForm`) is already proven via
`exists_traceForm_of_branchExtension`.

## What we have
- `traceFunExt f α y := if y ∈ branchLocus f then limUnder (𝓝[≠] y) (traceFun f α) else traceFun f α y`
  (TraceForm.lean:604). So at a branch point the value **is** the punctured-limit.
- `traceFunExt_eventuallyEq_traceFun`: `traceFunExt =ᶠ[𝓝[≠] y₀] traceFun` (TraceForm.lean:636).
- Off-branch **section**-smoothness machinery (TraceForm.lean:642+) — the template to mirror
  at the branch point (chart-coefficient analyticity ⟹ section `ContMDiffAt` via the
  cotangent-hom-bundle).
- `finite_branchLocus_of_nonconstant`, `eventually_notMem_branchLocus`.
- Local normal form `Discharge/Manifold/LocalNormalForm.lean:exists_local_normal_form`
  (`w ↦ wᵉ` model for the map near a ramification point); `AnalyticKthRoot.lean`.
- Off-branch local sheet system (`exists_localSheetSystem`).

## Decomposition

### Phase B — the bridge (tractable; isolates the crux). PROVE `traceExtendsAt_branchPoint`
assuming a clean **local-boundedness** input:

> `traceFun_chart_bounded` : in a chart `c = chartAt ℂ y₀`, the coefficient
> `z ↦ (traceFun f α (c.symm z)) 1 : ℂ` (the value of the 1-form on the basis vector)
> is **holomorphic on a punctured disk** around `c y₀` and **bounded** there.

From that:
1. Mathlib removable singularity — `Complex.differentiableOn_update_limUnder_of_bddAbove`
   / `analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`
   (`Mathlib/Analysis/Complex/RemovableSingularity.lean`) gives an analytic extension whose
   value at `c y₀` is `limUnder`, hence `ContinuousAt` of the coefficient, and analyticity.
2. Lift through the chart + the cotangent-hom-bundle (`contMDiffAt_hom_bundle`, mirror the
   off-branch machinery at TraceForm.lean:642+) to get the section `ContMDiffAt`.
3. `traceFunExt = limUnder` at `y₀` (def) matches the removable extension's value, so both
   conjuncts transfer from `traceFun` to `traceFunExt` via `traceFunExt_eventuallyEq_traceFun`.

**Deliverable:** `traceExtendsAt_branchPoint` proven *modulo* `traceFun_chart_bounded`
(sorry-split: the bridge is done, the analytic crux is isolated and crisply stated).

### Phase A — the analytic crux (hard; the genuine frontier). PROVE `traceFun_chart_bounded`.
Near `y₀` with ramification orders `eᵢ` on the colliding sheets, in a chart `z`:
- **A1** local normal form: each ramified sheet is `w = ζ^k z^{1/e}` (e branches of `z^{1/e}`)
  via `exists_local_normal_form` + `AnalyticKthRoot`.
- **A2** the trace = `∑` over sheets of `(α(sheet) ∘ mfderiv sheet)`; in coordinates the
  per-sheet term is `(1/e) ∑ₙ aₙ ζ^{k(n+1)} z^{(n+1)/e - 1}` where `α = (∑ₙ aₙ wⁿ) dw` locally.
- **A3** roots-of-unity cancellation: `∑ₖ ζ^{k(n+1)} = e·[e ∣ n+1]`, so summing over `k`
  kills every term except `n+1 = e·m`, leaving `∑_{m≥1} a_{em-1} z^{m-1}` — a **holomorphic**
  power series in `z` (no negative/fractional powers) ⇒ bounded near `0`, value `a_{e-1}` at `0`.
  (Newton-symmetric-function / Puiseux computation; not in Mathlib or `Discharge/`.)

Split A into A1 (local k-th-root branches), A2 (per-sheet coordinate form), A3 (the
roots-of-unity sum identity + holomorphy of the result). A3's core sum identity
`∑_{k<e} ζ^{km} = e·[e∣m]` is elementary (`Finset.geom_sum_eq` / `rootsOfUnity`); the
work is plumbing it through the per-sheet pullback coordinates.

## Status
- Phase B: **DONE** — `traceExtendsAt_branchPoint` is proven (no `sorry` in it) from two
  isolated inputs; `lake build Jacobians.TraceForm` succeeds. The bridge infrastructure is all
  proven: `traceLocalCoeff` (the right object — the trace read in the *fixed `y₀`-chart*),
  `contMDiffAt_traceTotalSpaceMk_of_localCoeff` (scalar local-coeff smoothness ⟹ section
  smoothness, via `op = (op 1) • id` + `contMDiffAt_hom_bundle`),
  `contMDiffAt_traceLocalCoeff_of_notMem_branchLocus` (off-branch local-coeff smoothness),
  the two scalar manifold↔chart bridges, and the removable-singularity assembly
  (`Complex.differentiableOn_update_limUnder_of_bddAbove` + `DifferentiableOn.analyticAt`).
- **Two isolated `sorry`s remain** (the analytic frontier + a design gap):
  1. `traceLocalCoeff_bddAbove` — **the intended Phase-A crux**: local boundedness of the trace
     near the branch point, read in the `y₀`-chart. Genuinely missing analytic content
     (roots-of-unity/Puiseux). This is the *right* object: boundedness of the **local**
     coefficient (not the raw operator) is exactly what the removable-singularity bridge needs.
  2. `traceFunExt_branchValue_correct` — **a `traceFunExt`-DESIGN gap, NOT implied by
     boundedness**. The conclusion of `traceExtendsAt_branchPoint` references the branch value
     `traceFunExt f α y₀`, which the current `traceFunExt` *defines* as the **raw-operator**
     `limUnder (𝓝[≠] y₀) (traceFun f α)`. The raw operator `traceFun f α y ∈ ℂ →L ℂ` is read in
     the *varying chart at `y`* — it equals `inCoordinates(…) ∘ clmAt(tangentTriv y₀) y`, whose
     chart-transition factor is **discontinuous** for a non-trivial tangent bundle (genus ≥ 2;
     the obstruction in `CotangentCoeff.lean`). So the raw `limUnder` need not converge (and its
     frame mismatches the local-coefficient extension). This lemma packages the two facts the
     current statement needs (raw convergence for `ContinuousAt`; local-coeff matching for the
     analytic-extension value).
- **Recommended fix (Phase A / refactor):** redefine `traceFunExt` at branch points via the
  **local coefficient** (or as the *bundle-limit* of the section `traceTotalSpaceMk`), not the
  raw-operator `limUnder`. Then `traceFunExt_branchValue_correct` becomes provable **from
  boundedness alone** (the section converges in the bundle; its limit value read locally is the
  analytic extension), collapsing Phase B to the single genuine crux `traceLocalCoeff_bddAbove`.
  This also fixes `exists_traceForm_of_branchExtension`, which consumes the raw convergence via
  `htendsto`/`hext.2`.
- Phase A: not started (the crux; multi-session) — `traceLocalCoeff_bddAbove`.

Refs: Forster §10 (the trace), §4.22–4.25 (local normal form `wᵉ`); Griffiths–Harris Ch.2 §2.7.
