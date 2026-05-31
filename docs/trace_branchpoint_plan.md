# Plan — discharge #4 `traceExtendsAt_branchPoint` (the trace's branch-point extension)

**Goal**: for a branch point `y₀ ∈ branchLocus f`, the canonical extension `traceFunExt f α`
is, at `y₀`,
* `ContMDiffAt` as a cotangent-bundle section (`traceTotalSpaceMk (traceFunExt f α)`), **and**
* `ContinuousAt` **in the fixed `y₀`-frame**, i.e. the local coefficient
  `y ↦ traceLocalCoeff (traceFunExt f α) y₀ y` is `ContinuousAt y₀`.

Discharging this is the **single remaining analytic fact** of the trace; everything
downstream (regluing, ℂ-linearity, `exists_traceForm`) is already proven via
`exists_traceForm_of_branchExtension`.

## 2026-05-31 SOUNDNESS REFACTOR — the branch value is now in the fixed frame (DONE)

The prior design defined `traceFunExt` at a branch point as the **raw-operator** limit
`limUnder (𝓝[≠] y₀) (traceFun f α)`, read in the *varying* chart at `y`. That operator is
**provably discontinuous** for a non-trivial tangent bundle (genus ≥ 2 — the
`CotangentCoeff.lean` obstruction), so:
* the raw `limUnder` need not converge (junk value), and
* the old conjunct-2 `ContinuousAt (traceFunExt f α) y₀` (raw operator) and the
  `htendsto` raw-operator convergence used for ℂ-linearity were **unsound** (relied on a
  false convergence). `traceFunExt_branchValue_correct` (which packaged those facts) was the
  isolated design-gap sorry.

**Fix (implemented).** The branch value is now `traceBranchValue f α y₀ := L • id`, where
`L := limUnder (𝓝[≠] (c y₀)) (z ↦ traceLocalCoeff (traceFun f α) y₀ (c.symm z))` is the
chart-pullback removable-singularity limit of the **local coefficient** (trace read in the
*fixed* `y₀`-trivialization). Key new lemmas:
* `tangent_continuousLinearMapAt_center`, `tangent_symmL_center`, `inCoordinates_center_self`:
  the fixed `y₀`-trivialization coordinate change is the **identity at the center `y₀`**
  (`D(chart∘chart.symm)(y₀) = id`). Hence `traceLocalCoeff coeff y₀ y₀ = (coeff y₀) 1`
  (`traceLocalCoeff_center`).
* `traceFunExt_branchValue_correct` (now **PROVEN, no analytic input**): the local coefficient
  of the extension at `y₀` is exactly `L` — a definitional consequence of the center identity
  (`(L • id) 1 = L`).
* `traceFunExt_branchPoint_eq_smul_id`: at a branch point the operator equals
  `(traceLocalCoeff (traceFunExt f α) y y) • id`, turning operator ℂ-linearity into *scalar*
  local-coefficient ℂ-linearity.
* `inCoordinates_apply_one_add/smul`, `traceLocalCoeff_add/smul`: the local coefficient is
  ℂ-linear in the operator value (since `inCoordinates` is `clEquiv ∘ · ∘ clEquiv.symm`).

**Statement changes (soundness-justified).**
* `traceExtendsAt_branchPoint` conjunct 2: `ContinuousAt (traceFunExt f α) y₀` (raw, FALSE)
  → `ContinuousAt (fun y => traceLocalCoeff (traceFunExt f α) y₀ y) y₀` (fixed frame, TRUE —
  the *shadow* of conjunct 1: section `ContMDiffAt` ⟹ local-coeff continuity).
* `exists_traceForm_of_branchExtension` hypothesis `hext` conjunct 2: matched to the above.
  Its ℂ-linearity (`hadd`/`hsmul`) is re-derived **in the fixed frame** via
  `htendstoLC` (local-coefficient convergence, which genuinely holds) + `tendsto_nhds_unique`
  + `traceFunExt_branchPoint_eq_smul_id` — replacing the unsound raw-operator `htendsto`.
* `exists_traceForm`, `traceForm`, and all public API: **unchanged signatures**; off-branch
  agreement `(T α).toFun y = traceFun f α y` for `y ∉ branchLocus f` is preserved verbatim.

**Result.** `traceFunExt_branchValue_correct` and `exists_traceForm_of_branchExtension` are now
`sorryAx`-free; `exists_traceForm`/`traceExtendsAt_branchPoint` carry `sorryAx` *only* via the
one genuine crux `traceLocalCoeff_bddAbove`. Axioms (all four):
`[propext, Classical.choice, Quot.sound, sorryAx]` — no custom axioms.

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

## 2026-05-31 (later) — LITTLE-O REFORMULATION + ANALYTIC HEART PROVEN

The Phase-A crux was **reformulated and largely discharged**, replacing the
roots-of-unity/Puiseux route (A1–A3 above) with a far simpler one.

**The reformulation (user-approved).** The old `traceLocalCoeff_bddAbove` asserted *global*
`BddAbove` of `|G|` over the whole chart target. That is (a) likely **false** — the chart
codomain need not be relatively compact, so `G` need not be bounded out to `∂ c.target` — and
(b) needlessly hard (it forces the symmetric-function cancellation). Mathlib has a *second*
removable-singularity lemma, `Complex.differentiableOn_update_limUnder_insert_of_isLittleO`,
needing only the **local little-o** `G =o[𝓝[≠] z₀] (·−z₀)⁻¹`, i.e. `(z−z₀)·G(z) → 0`. The crux
is now `traceLocalCoeff_mul_sub_tendsto_zero` (that tendsto), and `traceExtendsAt_branchPoint`
consumes it via the `isLittleO` lemma. **No roots-of-unity, no `zᵉ`-sheets, no Newton symmetric
functions.**

**Why it is now easy.** `‖traceFun f α y‖ ≤ ∑_{x∈f⁻¹y} ‖α x‖·‖(mfderiv f x)⁻¹‖`, and near each
branch preimage the crude per-sheet estimate `|z−z₀|·‖(mfderiv f x)⁻¹‖ = |F(w)−z₀|/|F'(w)| → 0`
(triangle inequality only). The cancellation that the Puiseux route extracted by hand is *not
needed* for the little-o.

**Proven this pass (all axiom-clean, `lake build Jacobians.TraceForm` green):**
- `sub_div_deriv_tendsto_zero` — the **one-variable analytic heart**: for `F` analytic at `w₀`,
  `F w₀ = z₀`, not locally constant, `(F w − z₀)/F'(w) → 0` as `w → w₀`. Via `F − z₀ =
  (w−w₀)^(d+1)·g` (`g w₀ ≠ 0`) the ratio is `(w−w₀)·g/((d+1)g + (w−w₀)g') → 0`.
- The crux reduction: `traceLocalCoeff_mul_sub_tendsto_zero` (the `z`-statement) is proven from
  the `Y`-statement `traceLocalCoeff_mul_sub_tendsto_zero_Y` by composing with `c.symm`
  (`Tendsto c.symm (𝓝[≠] z₀) (𝓝[≠] y₀)`), fully proven.

**One isolated `sorry` remains — `traceLocalCoeff_mul_sub_tendsto_zero_Y`** (the manifold side):
`(c y − c y₀)·traceLocalCoeff (traceFun f α) y₀ y → 0` as `y → y₀`. Its internal decomposition
(recorded in its docstring) is now **soft** (no missing analytic content):
1. *Norm bound* `‖traceLocalCoeff coeff y₀ y‖ ≤ B·‖coeff y‖` near `y₀` — `B` bounds the fixed
   trivialization `symmL` near `y₀` (`= id` at `y₀` by `tangent_symmL_center`). [needs general
   `symmL` continuity for the ℂ tangent bundle — Mathlib's `Riemannian.lean` has only the real
   inner-product version; mild plumbing.]
2. *Per-preimage estimate* via the **scalar map `g := c ∘ f : X → ℂ`** (model-space target ⟹
   trivial target chart, avoiding the varying-chart problem): `mfderiv g x = fderiv ℂ F (c_{x_j}
   x)` for the FIXED `F = c∘f∘chart_{x_j}.symm` (the `LineIntegral.lean` `h_mfderiv` pattern), and
   `mfderiv g = mfderiv c · mfderiv f` gives `‖(mfderiv f x)⁻¹‖ = |mfderiv c (fx)|·|F'(w)|⁻¹`;
   feed `sub_div_deriv_tendsto_zero` (PROVEN) + boundedness of `mfderiv c` near `y₀`.
3. *Assembly*: properness (`X` compact ⟹ `f⁻¹W ⊆ ⋃_j U_j` near `y₀`) + uniform off-branch fibre
   cardinality (`= deg f`; repo degree theory) reduce the finite fibre sum to finitely many
   `→ 0` terms.

(The pre-existing #5 sorry `traceForm_comp` is unrelated to this plan and untouched.)

Refs: Forster §10 (the trace), §4.22–4.25 (local normal form `wᵉ`); Griffiths–Harris Ch.2 §2.7.
