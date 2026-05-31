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
- Phase B: **in progress** (background agent).
- Phase A: not started (the crux; multi-session).

Refs: Forster §10 (the trace), §4.22–4.25 (local normal form `wᵉ`); Griffiths–Harris Ch.2 §2.7.
