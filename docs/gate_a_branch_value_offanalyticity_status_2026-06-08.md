# Gate A — `hT_off` at branch values via the planar removable engine: status (2026-06-08)

**Task.**  Close Gate A (`∑Res(α) = 0`, `α = ω₀·g`) via the RE-POINTED path that feeds
`globalTrace_of_glue` an arbitrary value-chart trace `T : ℂ → ℂ` (not `valueChartTrace`/`Φ`), with the
genuine full trace built from the PROVEN `TraceForm` boundedness — sidestepping the false
`BranchAwareTraceSelection.hbranch` route.

**Headline.**  This session **closed the analytic frontier of `hT_off` at branch values** — the
re-pointed plan's step 2 ("the genuinely-new analysis") — by building a sound **planar
removable-extension engine** (axiom-clean) and wiring it to the geometric trace.  The remaining work is
re-pointed precisely: the §VIII.3 **boundedness crux** at branch values + the **monodromy
germ-coherence** (the long-standing open frontier) + genus-0/junk.

Gate A `∑Res = 0` is **NOT yet unconditional**; the minimal obligation is sharpened (below).

---

## What was built this session (axiom-clean `[propext, Classical.choice, Quot.sound]`)

Two new files, both verified via authoritative `lake env lean` `#print axioms`, zero custom axioms,
zero `sorry`:

### 1. `Jacobians/Dolbeault/FormTraceBranchPlanarExtend.lean` — the planar engine

* **`analyticAt_update_of_punctured_diff_of_tendsto_zero`** — the planar removable singularity: a
  function `T₀` complex-differentiable on a *punctured* neighbourhood of `b₀` with the boundedness
  crux `(z − b₀)·T₀ z → 0` has `Function.update T₀ b₀ (limUnder …)` `AnalyticAt b₀`.  Built on Mathlib's
  `Complex.differentiableOn_update_limUnder_insert_of_isLittleO` via the little-o bridge
  `isLittleO_sub_of_tendsto_zero`.  This is the **planar shadow of the bundle-side
  `TraceForm.traceExtendsAt_branchPoint`**, stated on `ℂ → ℂ` so it applies directly to the
  value-chart geometric trace.
* **`analyticAt_of_eventuallyEq_of_tendsto_zero`** / **`…_of_value_…`** — germ forms (the exact
  `globalTrace_of_glue.hT_off`-at-a-branch-value shape): if `T` carries the correct limit value at
  `b₀` and germ-equals `T₀` off `b₀`, then `T` is `AnalyticAt b₀`.
* **`tendsto_zero_section_deriv`** — the per-sheet boundedness atom, **discharged from the proven
  `TraceForm.sub_div_deriv_tendsto_zero`**: for a regular-fibre section `s` (local inverse of `f`'s
  chart-pullback `F` at a ramification point, `F ∘ s = id`, `F w₀ = b₀`), `(z − b₀)·deriv s z → 0`.
  Composes the proven ratio atom with the section pushforward `s : 𝓝[≠] b₀ → 𝓝[≠] w₀`
  (`tendsto_section_nhdsNE`) and the chain-rule identity `deriv s z = 1/F'(s z)`.
* **`tendsto_zero_perSheet`** / **`tendsto_zero_fibreSum`** — assemble the per-sheet atom over the
  finite fibre into the fibre-sum boundedness crux `(z − b₀)·∑ᵢ coeffᵢ(sᵢ z)·deriv sᵢ z → 0`.

### 2. `Jacobians/Dolbeault/FormTraceBranchValueOff.lean` — wiring to the geometric trace

* **`valueChartTrace_branchExtension`** — the geometric trace patched to its punctured limit at a
  branch value `b₀` (the **value-correct** trace there, the planar analogue of `traceFunExt`).
* **`analyticAt_branchExtension_valueChartTrace`** — at a branch value `b₀`, this patched extension is
  `AnalyticAt b₀`, from (i) punctured analyticity of `valueChartTrace` (off-branch regular-fibre
  coherence) + (ii) the boundedness crux.  **This is the value-correct sound discharge of `hT_off` at a
  branch value** — replacing the structurally-impossible demand that the regular-fibre selection *host*
  the branch value (the `BranchAwareTraceSelection` obstruction from the prior session).
* **`tendsto_zero_valueChartTrace_of_fibreGerm`** — reduces the boundedness crux to the per-sheet atom
  *when* `valueChartTrace` germ-equals a fixed regular-fibre fibre-sum off `b₀`.

**Interface checks pass** (`lake env lean`, scratch): the output `AnalyticAt ℂ T b₀` is exactly the
shape `globalTrace_of_glue.hT_off` demands at an off-centre value, and the boundedness crux genuinely
reduces to `tendsto_zero_section_deriv` (proven) given the section/chain-rule data.

---

## Why this is the correct re-pointing (and what it fixes)

The prior session found `valueChartTrace ω₀ f Φ` (via a regular-fibre selection `Φ`) **cannot host the
branch-value value**: at a branch value the selected fibre has fewer sheets, so the value is the
*partial* sum, not the analytic-continuation limit.  This is fatal for both `hbranch` *and* `hT_off`
(which needs a genuine `AnalyticAt`, hence the correct value at `b₀`).

The fix — exactly the re-pointed plan — is to **patch** the trace to its removable limit at each branch
value (`valueChartTrace_branchExtension`), precisely as the bundle trace `traceFunExt` does.  The patch
is value-correct *by construction* (it IS the limit), and `analyticAt_branchExtension_valueChartTrace`
proves it analytic from punctured-analyticity + boundedness.  The patch only changes the value at the
(finitely many) branch values, so the extension shares all the finite/∞ glue with `valueChartTrace`
(`valueChartTrace_branchExtension_eventuallyEq`).

---

## The minimal remaining obligation (precise + re-pointed)

With the analytic/removable-extension half now proven, Gate A `∑Res = 0` is reduced — axiom-clean — to
the **globally-patched trace** `Tᵉˣᵗ` (= `valueChartTrace` patched at every branch value), feeding
`globalTrace_of_glue`, with these honest inputs:

1. **The boundedness crux at each branch value** — `(z − b₀)·valueChartTrace z → 0` as `z → b₀`.  This
   is the §VIII.3 analytic heart.  *Status:* reduced **sheet-by-sheet to the proven ratio atom**
   `tendsto_zero_section_deriv` *for a fixed regular fibre* (`tendsto_zero_valueChartTrace_of_fibreGerm`).
   The genuine remaining content is that near a branch value the *moving* selection `Φ b'` (`b' ≠ b₀`)
   germ-agrees with a fibre-sum whose per-sheet section derivatives are controlled by the ramification
   normal form — i.e. supplying the per-sheet section data `(s_i, F_i)` with `F_i ∘ s_i = id` and
   `F_i w₀ = b₀` uniformly over the colliding sheets.  This is the *same* content the bundle proof
   `TraceForm.traceLocalCoeff_mul_sub_tendsto_zero_Y` discharges (uniform fibre-cardinality bound +
   finite subcover); porting it to the planar moving selection is the focused remaining analysis.

2. **The monodromy germ-coherence** (`hglue_fin`/`hglue_inf` and the per-regular-value `hreg`) — the
   geometric trace germ-equals the local fibre traces off the exceptional set.  *Status:* the
   **long-standing open frontier** across all prior sessions (the branched-cover sheet-gluing); NOT
   touched here.  The bundle `TraceForm.traceForm` provides it for the holomorphic frame; the
   function-weighted/meromorphic case is the remaining geometric frontier.

3. **Punctured analyticity** `∀ᶠ z in 𝓝[≠] b₀, AnalyticAt ℂ valueChartTrace z` at each branch value —
   from the per-regular-value coherence (`analyticAt_valueChartTrace_of_eventuallyEq`,
   `FormTraceGlobalGeometric`) applied at the nearby regular values.  Reducible to (2).

4. **Junk-freeness + genus-0 `∞`-vanishing** — `coeffAt_eq_zero_of_sphereForm`
   (`H⁰(ℂℙ¹, Ω) = 0`) and the reciprocal-chart data, unchanged and independent of the above.

The **net effect of this session**: the *removable-extension / analyticity* obstruction at branch
values — the piece the re-pointed plan named as the genuinely-new analysis — is **closed** (sound,
axiom-clean, value-correct).  What remains is the boundedness crux (now precisely isolated + partially
reduced to the proven atom) and the monodromy germ-coherence (the pre-existing frontier).

---

## Soundness

No custom axiom, no `sorry` on a false statement.  Both new files re-grepped `^axiom ` (empty) and
verified `[propext, Classical.choice, Quot.sound]` via authoritative `lake env lean` `#print axioms`.
The patch is **value-correct** (the limit, not a partial sum) — it does NOT revive the false
`hbranch`/host-the-branch-value route; it patches to the genuine removable limit.  Non-vacuity is
preserved: over the empty-pole case `valueChartTrace ≡ 0`, the extension is `≡ 0`, analytic everywhere.
Full targeted builds green; the new modules are in the lakefile glob (no orphan).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §10, §17.
* `Jacobians/TraceForm.lean` — the bundle-side `traceExtendsAt_branchPoint` /
  `sub_div_deriv_tendsto_zero` (the proven analytic core this session's planar engine shadows/reuses).
