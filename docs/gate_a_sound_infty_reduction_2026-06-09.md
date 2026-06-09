# Gate A (`∑Res(α) = 0`) — sound `∞`-fibre reduction (2026-06-09)

**Status:** Gate A is **NOT yet unconditional**, but the previously-unsound `∞`-fibre foundation is now
**fixed**, and a **sound** Gate-A reduction (axiom-clean `[propext, Classical.choice, Quot.sound]`) is in
place. This session did *not* close the genericity; it found and fixed a deeper soundness landmine that
the original close-Gate-A plan (Miranda §VIII.3) had not anticipated.

## The critical finding (soundness)

The existing `Jacobians.Dolbeault.FormTraceInftyFibre.InftyFibreData` (`FormTraceInftyFibre.lean:99`)
models the `∞`-fibre trace through the **literal** reciprocal `z ↦ (f.holoRepr (chart⁻¹ z))⁻¹`, with two
fields that are **provably false for a genuine `∞`-pole**:

- `hrecip_an : AnalyticAt ℂ (fun z => (f.holoRepr (chart⁻¹ z))⁻¹) (chart (xs i))` — at a pole `xs i`,
  `f.holoRepr (xs i) = limUnder (𝓝[≠] xs i) f.toFun` is a *junk* value (the limit does not exist at a
  pole; `holoRepr` is only repaired where order ≥ 0). The literal reciprocal agrees with its analytic
  representative only on `𝓝[≠]`, not at the centre, so it is not `AnalyticAt` there.
- `hrecip_val : (f.holoRepr (xs i))⁻¹ = 0` — needs `f.holoRepr (xs i) = 0` (since `0⁻¹ = 0` in Mathlib),
  but at a pole `holoRepr` is junk, generically ≠ 0.

Evidence it was never real: **every** `InftyFibreData` in the repo is the *empty* one
(`emptyInftyFibreData`); there is no non-empty instance. The `∞`-fibre trace `inftyFibreTrace` consumes
these fields via `exists_planar_section` (which needs literal `AnalyticAt` of the sheet), so the falsity
is load-bearing.

**Consequence:** the existing wall-2-closed result
`FormTraceGlobalFibreSelection.residueSum_eq_zero_of_canonicalSelection` carries `hglue_inf` *against the
buggy `inftyFibreTrace`*, so for any non-empty `∞`-fibre that hypothesis is **unsatisfiable** — the
"wall 2 closed" path could not actually be completed to unconditional Gate A.

## The fix (3 new files, all axiom-clean, no proven file touched)

1. `Jacobians/Dolbeault/FormTraceInftyFibreNF.lean` — `InftyFibreDataNF` carries the **repaired
   reciprocal** `h := toMeromorphicNFAt (f.holoRepr∘chart⁻¹)⁻¹` (from the proven
   `ProperMapDegreeSheets.exists_reciprocal_NF`) as *data*, with a germ-link `hrecip_germ` to the literal
   `1/f` off the centre. `h` is genuinely analytic at the centre, vanishes there, has analytic order =
   pole order. `inftyFibreTraceNF` is the sound `∞`-fibre `FibreTrace`; `resAt_traceCoeff_inftyFibreTraceNF`
   is the sound `∞`-fibre Lemma 3.2; `infty_eq_of_agreeNF` is the precise `GlobalTraceData.infty_eq`
   conclusion. `InftyFibreDataNF.ofRegular` builds the datum from a **simple `∞`-pole**
   (`orderAtPoint = −1`, the unramified-over-`∞` case; order-1 ⟹ `deriv h ≠ 0`).

2. `Jacobians/Dolbeault/FormTraceFullFibreRationalityNF.lean` — `TraceRationalityDataNF`, the full-fibre
   trace-rationality reduction target with the sound `∞`-fibre datum and `agree_infty` against
   `inftyFibreTraceNF`. `toGlobalTraceData` reuses the proved finite `hL32_of_agree_fibreRegularData` and
   the sound `infty_eq_of_agreeNF`; `residueSum_eq_zero` closes Gate A via the proved `GlobalTraceData`
   descent. Non-vacuity (empty pole set) re-exported.

3. `Jacobians/Dolbeault/FormTraceCoherenceFromMovingNF.lean` — `traceRationalityDataNF_ofMovingData` and
   `…_ofSheetSections`: assemble a `TraceRationalityDataNF` from a global selection `Φ`
   (`T := valueChartTrace`), per-pole `MovingCoherenceDatum` (the finite coherence + off-centre meromorphy
   reuse the proved moving-fibre engine `hcoh_fin_of_movingDatum`), the genus-`0` remainder vanishing
   (`hentire`/`hrecip_cont` ⟹ `T = L.R` via the proved Liouville
   `coeff_eq_of_entire_diff_of_recipCoeff_continuousAt`), and the **sound** `∞`-coherence `hcoh_inf`. The
   sheet-form constructor builds the per-pole moving data labeling-free
   (`MovingCoherenceDatum.ofSheetSectionsSet`), ready to consume the canonical full-fibre selection's
   (proven) sheet sections.

## Where Gate A now rests (precise remaining obligations)

`residueSum_eq_zero_of_sheetTraceRationalityNF` (and `…_ofMovingData`) reduce Gate A `∑Res = 0` —
*soundly* and axiom-clean — to, for an adapted cover `f`:

1. **Wall 2 (Φ + sheet sections).** A global fibre selection `Φ` enumerating the poles, with smooth
   pole-value sheet sections `secFin`/`hsetFin`. Dischargeable from the canonical full-fibre selection
   (`FormTraceGlobalFibreSelection`, the symmetric lever — *proven*); only the wiring into the NF
   constructor remains (the connector signature matches).

2. **Genus-`0` remainder vanishing `hentire`/`hrecip_cont`** for `valueChartTrace` — the deep §VIII.3
   analytic content (after subtracting the finite principal parts, the remainder is entire and holomorphic
   across `∞`; `H⁰(ℂℙ¹, Ω) = 0`). Has its own sub-residuals in the existing stack (off-exceptional
   analyticity via the moving coherence, branch-value removability, junk-freeness `hcont_int`, the
   sphere-form vanishing `R₀`). **Per the plan's `T := traceFun` strategy**, the cleanest discharge routes
   these from the *proven* bundle branch extension `TraceForm.traceExtendsAt_branchPoint` + the ∞-bridge +
   `coeffAt_eq_zero_of_sphereForm` — not yet wired.

3. **Sound `∞`-coherence `hcoh_inf`** — `recipCoeff (valueChartTrace) =ᶠ[𝓝[≠] 0]
   (inftyFibreTraceNF ω₀ f Dinf).traceCoeff`. A genuine moving-fibre residual at `∞` (the `∞`-analogue of
   the finite `MovingCoherenceDatum`; the existing `∞`-reparametrization bridge
   `recipCoeff_inftyMovingSum_eq_traceCoeff` mirrors over to the NF trace, leaving the geometric
   coherence as the residual).

4. **Wall 1 (genericity).** `∃ f` adapted: a nonconstant `f` (from the proven Riemann inequality
   `exists_nonconstant_meromorphic` / `two_le_lDim_largeEffective`) whose finite α-poles are regular
   non-poles of `f` and whose `∞` α-poles are **simple poles** of `f` (so `FibreRegularData.ofRegular` and
   `InftyFibreDataNF.ofRegular` apply). The genericity-in-linear-system argument (avoid the finitely-many
   codim-≥1 bad conditions; `criticalValues_finite_general`) is not yet formalized.

## Reuse map (proven, untouched)

- `ProperMapDegreeSheets.exists_reciprocal_NF` (the repaired reciprocal — the keystone of the fix);
- `FibreTrace.resAt_traceCoeff'`, `chartIntegrand` / `meromorphicAt_chartIntegrand` /
  `resAt_chartIntegrand_eq_formFnResidue`, `exists_planar_section`, `resAtInfty_eq_resAt_recipCoeff`;
- `GlobalTraceData.residueSum_eq_zero`, `hL32_of_agree_fibreRegularData`;
- `exists_laurentForm_principalPart`, `coeff_eq_of_entire_diff_of_recipCoeff_continuousAt`;
- `MovingCoherenceDatum` + `.coherent` + `.ofSheetSectionsSet`, `hcoh_fin_of_movingDatum` /
  `meromorphicAt_valueChartTrace_of_movingDatum`.

## References

- Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3 (the trace `Tr`, Lemma 3.2; normal
  form (3.1); the residue at infinity).
- Forster, GTM 81, §17.
- `docs/gate_a_cover_genericity_textbook_2026-06-08.md` (the full-fibre route / genericity discussion).
