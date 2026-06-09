# Gate A (`∑Res(α) = 0`) — sound value-correct (branch-patched) close (2026-06-09)

**Status:** Gate A is **NOT yet unconditional**, but the previously-identified sound `∞`-foundation now
has a **sound, value-correct, axiom-clean** reduction whose `hentire` (the genus-`0` entire-remainder
content) is **proven internally** rather than assumed — closing a latent false-field risk in the prior
raw-trace constructor — and whose remaining surface is a precise list of genuine §VIII.3 geometric
residuals + Wall-1 genericity.

All new declarations are axiom-clean `[propext, Classical.choice, Quot.sound]` (authoritative
`#print axioms`, NOT LSP). New file only: `Jacobians/Dolbeault/FormTraceRationalityNFPatched.lean`.

## The soundness finding (a latent false field in the raw-trace constructor)

`FormTraceFullFibre.traceRationalityDataNF_ofMovingData` (the proven sound-`∞` constructor in
`FormTraceCoherenceFromMovingNF.lean`) takes, as a **caller hypothesis**,

> `hentire : … → AnalyticOnNhd ℂ (valueChartTrace ω₀ f Φ − L.R) Set.univ`

against the **raw** geometric trace `valueChartTrace ω₀ f Φ`. This is **unsatisfiable for any cover
with branch points** (genus ≥ 1): at a branch value the raw trace takes a *partial-sum* value, **not**
the removable-singularity limit, so it is *discontinuous* across the branch and cannot be entire. The
repo already records the same fact at `FormTraceGlobalTPatched.lean:432–433` (it flags
`BranchAwareTraceSelection.hbranch` — continuity of the raw trace at a branch value — as **false** and
introduces `valueChartTracePatched` precisely to fix it). The constructor itself is sound (it only
*consumes* `hentire`); the falsity is in *supplying* it for the canonical full-fibre selection. This is
exactly the `T := valueChartTrace` "Puiseux trap" the plan warned about, surfacing at the entire-step.

**Fix (the plan's `T := traceFun`).** Use the **branch-patched** trace
`T := valueChartTracePatched ω₀ f Φ br` (raw off `br`, the punctured limit at each branch value) — the
*planar shadow* of the proven bundle trace `traceFun` extension
(`TraceForm.traceExtendsAt_branchPoint`, axiom-clean). With this `T`, `hentire` becomes a **theorem**.

## What is proven (axiom-clean)

In `FormTraceRationalityNFPatched.lean`, namespace `Jacobians.Dolbeault.FormTraceFullFibre`:

- `traceRationalityDataNF_ofPatched` — builds the SOUND `TraceRationalityDataNF` (the sound target,
  reused not edited) with `T := valueChartTracePatched`. `hentire` is **proven** via
  `analyticOnNhd_remainder_of_junkFree'` ∘ `hT_off_patched`
  (`analyticAt_valueChartTracePatched_off_centres`: regular values by the moving coherence, branch
  values by the value-correct removable extension — boundedness, NOT continuity); `hrecip_cont` is
  `continuousAt_recipCoeff_of_vanishing`; the Liouville `T = L.R` is
  `coeff_eq_of_entire_diff_of_recipCoeff_continuousAt`; `agree`/`agree_infty` from `T = L.R` + the
  per-pole moving coherence / the sound `∞`-coherence.
- `residueSum_eq_zero_of_patchedTraceRationalityNF` — Gate A `∑Res = 0` from the above.
- `hbnd_of_eventual_sphereCoherence` — the branch-value boundedness crux `(z − b₀)·valueChartTrace → 0`
  from the **bundle trace SUM** (`tendsto_zero_valueChartTrace_of_bundleGerm`, on the axiom-clean
  `traceLocalCoeff_mul_sub_tendsto_zero`) + the bundle germ bridge
  (`hbridgeBr_of_eventual_sphereCoherence`) — Miranda's "the SUM extends across branch points", no
  individual colliding sheet. This is the `T := traceFun` discharge of the genus-`0` analyticity.
- `hreg_of_movingDatum` — regular-value analyticity from the symmetric-lever moving coherence.
- `inftyMovingSumNF` + `recipCoeff_inftyMovingSumNF_eq_traceCoeff` + `hcoh_inf_of_inftyMovingCoherenceNF`
  — the **sound `∞`-coherence engine**: the `dζ`-Jacobian reparametrization identity against the
  *repaired* `inftyFibreTraceNF` (the genuinely-analytic reciprocal, `FormTraceInftyFibreNF`), a verbatim
  transcription of the proven buggy-side `recipCoeff_inftyMovingSum_eq_traceCoeff` (structure-driven —
  only the `FibreTrace` interface). Reduces `hcoh_inf` to the single `∞`-moving coherence residual `hcoh`,
  **never touching the buggy `InftyFibreData`**.
- `residueSum_eq_zero_of_patchedGeometry` — the **top-level sound assembly**: wires all the helpers, so
  Gate A rests on the precise residuals below.
- `residueSum_eq_zero_of_patchedTraceRationalityNF_holomorphic` — end-to-end **non-vacuity** (empty
  pole set, `br = ∅`), confirming the reduction is honest (not a disguised `False`).

## Where Gate A now rests (precise remaining obligations, sound `∞` + value-correct trace)

`residueSum_eq_zero_of_patchedGeometry` reduces Gate A `∑Res = 0` — soundly, axiom-clean — to, for a
nonconstant cover `f` (`hncF`):

1. **Wall 2 (global selection + per-pole/per-regular moving coherence).** `Φ` (the canonical full-fibre
   selection, *proven* in `FormTraceGlobalFibreSelection`) with the per-pole `Cfin` and per-regular `Creg`
   moving coherence data (from `MovingCoherenceDatum.ofSphereSheetSystemSet`/`ofSheetSectionsSet`, the
   symmetric lever — *proven*). Only the wiring into the patched constructor remains; the connector
   signatures match (`hreg_of_movingDatum`).

2. **Genus-`0` branch analyticity geometry (`hbnd` inputs).** Per branch value `b₀`: a local holomorphic
   `αBr b₀` representing `α = ω₀·g` near the fibre, and the **eventual sphere-sheet coherence** `hevBr`
   (the geometric trace equals the sphere-sheet planar fibre trace near `b₀`, with `αBr = ω₀·g` at the
   fibre). This is the *standard regular-value sphere coherence* — already discharged by the
   `Sreg`/`Creg` machinery (`valueChartTrace_eq_sphereSheetFibreTrace`, *proven*); wiring remains.

3. **Sound `∞`-fibre (`Dinf` + `hcoh`).** Simple `∞`-poles `hsimpleInf` (for `InftyFibreDataNF.ofRegular`,
   *proven*) and the `∞`-moving coherence `hcoh` (`recipCoeff (valueChartTracePatched) =ᶠ recipCoeff
   (inftyMovingSumNF …)` — the `∞`-analogue of the finite moving coherence). Genuine `∞`-moving residual,
   but now against the SOUND reciprocal.

4. **Junk-freeness `hcont_int` + genus-`0` `∞`-vanishing `R₀`.** `T − L.R` continuous at each centre
   (junk-freeness) and `recipCoeff (T − L.R) =ᶠ R₀` with `R₀ 0 = 0` (the genus-`0` `H⁰(ℂℙ¹,Ω)=0` content,
   `coeffAt_eq_zero_of_sphereForm`). These remain residual *everywhere in the repo* (only the empty case
   discharges them); not specific to this route.

5. **Wall 1 (genericity).** The nonconstant cover `f` (`hncF`, *free* from the proven Riemann inequality
   `exists_riemannRoch_divisor`) and the adapted-cover separation (poles vs branch locus; simple
   `∞`-poles). Per `docs/gate_a_cover_genericity_textbook_2026-06-08.md`, NO Riemann–Roch-with-jets is
   needed — the book needs only "a nonconstant `f` exists" (already proven) + the §VIII.3 generic
   adaptation.

**Net:** residuals 1, 2 are *proven elsewhere in the repo and need only wiring*; residual 4 is the
repo-wide genus-`0` junk/sphere-form content; residuals 3 (the `∞`-moving coherence `hcoh`) and 5
(genericity) are the genuine remaining geometric content. The deep analytic frontier — the trace's
extension across branch points — is **proven and axiom-clean** (`traceLocalCoeff_mul_sub_tendsto_zero` /
`traceExtendsAt_branchPoint`), and is wired in via `hbnd_of_eventual_sphereCoherence`. The `hentire`
false-field risk of the raw route is **eliminated**.

## Soundness audit (active review)

- **No `axiom`, no `sorry`** in the new file (grep clean; the 6 "axiom" hits are docstring "axiom-clean").
- **All 10 public declarations** authoritatively `[propext, Classical.choice, Quot.sound]` (no `sorryAx`,
  no `Lean.ofReduceBool`).
- **`hentire` is now PROVEN, not a field** — the latent false field of the raw route is removed.
- **Every structure field supplied is genuinely satisfiable**: the residuals' building blocks have
  non-vacuity witnesses in the repo (`movingCoherenceDatum_empty`, `emptyInftyFibreDataNF`); the
  end-to-end empty-pole witness `residueSum_eq_zero_of_patchedTraceRationalityNF_holomorphic` is
  axiom-clean.
- **The buggy `InftyFibreData` is never used** — the `∞`-coherence runs entirely through the sound
  `inftyFibreTraceNF` / `inftyMovingSumNF`.

## References

- Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3.
- Forster, GTM 81, §17.
- `docs/gate_a_sound_infty_reduction_2026-06-09.md` (the sound `∞`-fibre fix).
- `docs/gate_a_cover_genericity_textbook_2026-06-08.md` (genericity: no RR-with-jets).
