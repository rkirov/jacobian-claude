# Gate A — the value-correct patched-trace unification + boundedness port: status (2026-06-08)

**Task.**  CLOSE Gate A (`∑ₐ Resₐ(α) = 0`, `α = ω₀·g`) by UNIFYING the proven `FormTrace*` engines into
one instantiation of `globalTrace_of_glue` for an adapted cover, using the **value-correct
branch-patched trace** (avoiding the false `BranchAwareTraceSelection.hbranch` continuity route), plus
the ONE genuinely-new analytic step (the branch-value boundedness port).

**Headline.**  Both deliverables are **done, axiom-clean**:

1. **The unification** — `globalTrace_of_glue` is instantiated via the patched trace, reducing Gate A to
   one structure `PatchedTraceSelection` whose fields are exactly the genuine Miranda §VIII.3 geometry.
2. **The boundedness port** — the branch-value boundedness crux `(z − b₀)·valueChartTrace z → 0` is
   ported to the planar moving-selection trace, discharged from the **proven** per-sheet ratio atom.

Gate A `∑Res = 0` is **NOT yet unconditional**; the single irreducible obligation is sharpened below
(the construction of a real, non-empty `PatchedTraceSelection` — i.e. the global selection `Φ`).

---

## What was built this session (all axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no custom axiom)

One new file, `Jacobians/Dolbeault/FormTraceGlobalTPatched.lean`, verified by authoritative
`lake env lean #print axioms`.

### The value-correct patched trace

* **`valueChartTracePatched ω₀ f Φ br`** — `valueChartTrace ω₀ f Φ` everywhere except at the
  finitely-many branch values `br`, where it is replaced by its **punctured-limit value** (the
  multi-point `Function.update`/removable-singularity form of the single-point
  `valueChartTrace_branchExtension`).  This is the value-correct trace, analytic *across* branch points
  — the partial-sum junk repaired to the analytic-continuation limit.
* **`…_of_not_mem` / `…_eq_branchExtension` / `…_eventuallyEq`** — the patch is inert off `br` (equal),
  coincides with the single-point removable extension at each branch value, and germ-equals
  `valueChartTrace` on `𝓝[≠] z` for *every* `z` (branch values isolated).
* **`recipCoeff_valueChartTracePatched_eventuallyEq`** — the reciprocal coefficient germ-equals that of
  `valueChartTrace` near `0` (for `ζ ≠ 0` small, `ζ⁻¹` escapes the finite `br`), carrying the `∞`-glue
  unchanged.
* **`analyticAt_valueChartTracePatched_off_centres`** — the full `hT_off` for the patched trace: regular
  values via the moving-sheet coherence (patch inert), **branch values via the value-correct removable
  extension** `analyticAt_branchExtension_valueChartTrace` (resting on punctured analyticity + the
  boundedness crux — *never* on continuity of the raw partial-sum trace).

### The boundedness port (THE genuinely-new analytic step)

* **`tendsto_zero_valueChartTrace_of_sections`** — discharges the boundedness crux `hbnd` at a branch
  value from the **proven** planar per-sheet ratio atom
  `FormTraceBranchPlanarExtend.tendsto_zero_section_deriv`.  Given the moving-sum germ-equality of
  `valueChartTrace` with the fibre sum along chart pullbacks `rinv_j = chart_{x_j} ∘ sec_j` of the cover
  sheets through the preimages `x_j` of `b₀`, each per-sheet term `(z − b₀)·coeff_j(rinv_j z)·deriv(rinv_j)
  z → 0` (the ratio atom on the analytic left-inverse `φ_j := f.holoRepr ∘ chart_{x_j}.symm`), and the
  finite sum `→ 0`.  This is the **planar shadow of the proven bundle-side
  `TraceForm.traceLocalCoeff_mul_sub_tendsto_zero_Y`** — the uniform-cardinality/finite-subcover
  machinery is *replaced* by the moving selection's explicit sheet enumeration, and the per-sheet content
  is the *same* proven ratio atom (`φ_j − b₀ = (w − w₀)^e·g`, no Puiseux/symmetric-function machinery).
* **`tendsto_zero_valueChartTrace_of_sheetSections`** — the reduced interface: derives *all* the
  per-sheet right-inverse / differentiability / chain-rule data of `…_of_sections` from a family of
  **smooth cover sheets** `sec : ι → ℂ → X` (sections of `f.holoRepr` through the non-pole preimages),
  via the proven `chartPullback_section_rinv`,
  `MeromorphicFunction.analyticAt_holoRepr_chartPullback_of_orderNonneg`, and the chain rule on
  `φ_j ∘ rinv_j = id`.  The caller supplies only the genuine geometric content: section smoothness,
  non-poleness, `f`-nonconstancy, coeff-continuity, and the moving-sum germ-equality.

### The unified Gate-A reduction

* **`PatchedTraceSelection`** — the Gate-A input feeding the patched trace `Tᵉˣᵗ` to
  `residueSum_eq_zero_of_glue`.  Mirrors `BranchAwareTraceSelection` for the finite/`∞` bookkeeping and
  the pole-value coherence, but the branch-specific field is the genuine §VIII.3 **boundedness crux**
  `hbnd` — *replacing the false `BranchAwareTraceSelection.hbranch` continuity* (the raw trace value at a
  branch value is a partial sheet sum, hence discontinuous).
* **`residueSum_eq_zero_of_patchedTraceSelection`** — **Gate A `∑Res = 0`** from a `PatchedTraceSelection`,
  via the proven `residueSum_eq_zero_of_glue` with `T := valueChartTracePatched ω₀ f Φ br`.  Finite glue
  from the per-pole moving datum (germ-transported to `Tᵉˣᵗ`), off-centre analyticity from the
  regular-value coherence ⊕ the value-correct branch extension, and the `∞`/junk/genus-`0` data.
* **`patchedTraceSelection_empty` / `residueSum_eq_zero_of_patchedTraceSelection_holomorphic`** —
  end-to-end **non-vacuity** (empty-pole case, `br = ∅`, patch inert, `T ≡ 0`): the structure is
  satisfiable, not a disguised `False`.

---

## Why this is the correct close (soundness)

* **No revived `hbranch`.**  The false route demanded the raw `valueChartTrace` be continuous (`hbranch`)
  *or* host the branch value — both false (the regular-fibre selection has *fewer* sheets at a branch
  value, so the value there is a *partial* sum).  The patched trace `Tᵉˣᵗ` instead carries the
  analytic-continuation **limit** at each branch value (value-correct *by construction*), and its
  analyticity there is the proven removable engine resting on the boundedness crux.
* **No false field.**  Every `PatchedTraceSelection` field is genuinely consumed; the non-vacuity witness
  confirms satisfiability.  The pole-sub-fibre glue phrasing is preserved (the honest separation
  genericity is folded into `Φ`, a Gate-D refinement).
* **Authoritative axiom check passes** for every headline declaration: `[propext, Classical.choice,
  Quot.sound]`; `^axiom ` grep empty; zero `sorry`.

---

## The single minimal remaining obligation (precise diagnosis)

Gate A `∑Res = 0` is reduced — axiom-clean — to the existence of a **non-empty `PatchedTraceSelection`**
for a real adapted cover.  Every field is either proved infrastructure or transported from
`valueChartTrace`; the *only* irreducible geometric content is:

> **Construct the global fibre selection `Φ : (b : ℂ) → FibreRegularData g f b`** such that, near every
> base value, `valueChartTrace ω₀ f Φ` is the **moving fibre sum** along a continuously-varying sheet
> frame enumerating the *full* fibre `F⁻¹(coe ·)`.

Concretely this supplies, all from the *same* moving-fibre data:

1. **`Cfin` / `Creg`** (the per-pole-value / per-regular-value moving-sheet coherence data) — discharged
   labeling-free by the **symmetric-invariance lever** (`MovingCoherenceDatum.ofSphereSheetSystemSet` +
   `canon_of_fibre_enumeration`, PROVEN) once `Φ b'` enumerates the fibre *as a set*; the sphere sheet
   system exists at regular values (`exists_sphereSheetSystem`).
2. **`hbnd`** (the branch-value boundedness) — now discharged by
   `tendsto_zero_valueChartTrace_of_sheetSections` once the moving-sum germ-equality `hgerm` is supplied
   at each branch value.  **The genuine residual for `hbnd`** is exactly `hgerm` at a branch value: the
   full fibre `Φ z` near `b₀` must be enumerated by the sheets through `b₀`'s preimages — *including the
   `m` colliding sheets* through the ramified preimage (the `z = wᵐ` local model's roots-of-unity
   sections).  Note `…_of_sections` does **not** require the base points `x_j` injective, so the `m`
   colliding sheets (all with the same base = the ramified point) are admissible; what is needed is the
   branched sheet enumeration matching the full fibre.
3. **`hglue_inf`** (the `∞`-glue) — Lemma 3.2 in the reciprocal chart at the `∞` fibre
   (`FormTraceInftyRecip` bridge proven; needs the `∞`-fibre moving data).
4. **`R₀ 0 = 0`** (genus-`0` `∞`-vanishing) — `H⁰(ℂℙ¹, Ω) = 0`
   (`ProjectiveLine.holomorphicOneForm_eq_zero`, PROVEN subsingleton), via the holomorphic remainder.
5. **`hcont_int`** (junk-freeness) — the meromorphic normal form of `Tᵉˣᵗ − L.R` at each centre (pole
   removed).

The conceptual walls are down (monodromy dissolved by the symmetric lever; the boundedness ported to the
proven ratio atom; the false `hbranch` avoided by the value-correct patch).  The remaining work is the
**global selection `Φ`** — the branched-cover full-fibre sheet enumeration consistent across overlapping
local sheet systems, *including the colliding sheets at branch values* (the `z = wᵐ` Puiseux frame).
That is the one well-defined geometric construction left.

---

## Files

* `Jacobians/Dolbeault/FormTraceGlobalTPatched.lean` (new) — the patched trace, the boundedness port (two
  forms), the `PatchedTraceSelection` reduction, and the non-vacuity witness.

Reuse (unchanged, PROVEN): `FormTraceGlobalTAssemble` (`globalTrace_of_glue` /
`residueSum_eq_zero_of_glue`), `FormTraceBranchValueOff` / `FormTraceBranchPlanarExtend` (the removable
engine + the per-sheet ratio atom), `FormTraceMovingFibre*` (the symmetric-lever coherence engines),
`FormTraceGlobalGeometric` (`valueChartTrace` + the off-exceptional analyticity bridge), `TraceForm`
(`sub_div_deriv_tendsto_zero`, `traceLocalCoeff_mul_sub_tendsto_zero_Y`), `MeromorphicLiouville`
(`analyticAt_holoRepr_chartPullback_of_orderNonneg`).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr` is single-valued by
  *symmetry* and extends across branch points; Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §10, §17.

---

# Update (2026-06-08, later) — the full-fibre frame wiring + the sharpened single obligation

**New file** `Jacobians/Dolbeault/FormTracePatchedFrame.lean` (axiom-clean
`[propext, Classical.choice, Quot.sound]`, verified by authoritative `lake env lean #print axioms`; no
`sorry`, no custom `axiom`).  It performs the final wiring of the global full-fibre sheet frame into a
`PatchedTraceSelection`, discharging the three *substantial* fields from the proven engines:

* **`hbnd_of_sheetFrame`** — the per-branch-value boundedness crux `(z − b₀)·valueChartTrace z → 0` from
  a **branched full-fibre frame** (smooth sheets through *all* preimages of `b₀`, the colliding ramified
  `z = wᵐ` Puiseux branches *admitted* — no injectivity of `sec · b₀` demanded), via the proven
  `tendsto_zero_valueChartTrace_of_sheetSections`.
* **`patchedTraceSelection_ofFrame`** — assembles a full `PatchedTraceSelection` from the global frame
  data:
  - `Cfin i` ← `MovingCoherenceDatum.ofSheetSections` over the **pole sub-fibre** `fibreReg hac (cs i)`
    (the honest pole/regular separation; the symmetric lever supplies the per-`b'` index bijection
    pointwise, no labeling);
  - `Creg z` ← `MovingCoherenceDatum.ofSphereSheetSystemCanon` over the **full fibre** (the symmetric
    lever; the only `Φ`-content is the canonical-fibre condition "`Φ b'` enumerates `F⁻¹(coe b')`");
  - `hbnd b₀` ← `hbnd_of_sheetFrame` (the branched Puiseux frame).
  The `∞`/junk/genus-`0` fields are carried as the genuine rationality residual.
* **`residueSum_eq_zero_ofFrame`** — Gate A `∑Res = 0` from the frame data, via
  `residueSum_eq_zero_of_patchedTraceSelection`.
* **`residueSum_eq_zero_ofFrame_holomorphic`** — re-exported non-vacuity (empty-pole witness), so the
  reduction is honest end-to-end.

**No new reduction structure** was added: `patchedTraceSelection_ofFrame`'s hypotheses are the genuine
residual geometric inputs as ordinary constructor arguments (the standard "reduced interface" idiom of
this repo, cf. `MovingCoherenceDatum.ofSheetSections`), and the unramified + branched analytic content is
*proven* here from the engines — not re-stated as new fields.

## Gate A status: REDUCED (axiom-clean), not yet UNCONDITIONAL

Gate A `∑Res = 0` is now reduced — axiom-clean — to supplying `patchedTraceSelection_ofFrame`'s
arguments for a real adapted cover.  The substantial analytic heart (the symmetric-lever per-value
coherence; the branch-value boundedness, including the colliding ramified sheets) is **closed**.  What
remains is the global geometric *construction* of the frame data, which splits into three genuinely
distinct residuals:

1. **THE single hardest atom — the branched full-fibre frame `hgermBr` at each branch value.**  A finite
   family of smooth cover sheets `secBr b₀ : ιBr b₀ → ℂ → X` through *all* preimages of `b₀` — the
   unramified ones (available off the branch locus) **and the `m` colliding ramified Puiseux branches**
   (the `z = wᵐ` local model's `m`-th-root sections, as continuously-varying functions of the base
   value), together with the **moving-sum germ equality** `hgermBr`: near `b₀`, the full-fibre
   `valueChartTrace` equals the fibre sum along these sheets.  `LocalNormalForm`/`LocalKFoldMultiplicity`
   supply the `z = wᵐ` structure and the *cardinality* count of the `m` roots, but **not** a
   continuously-varying *section family* `secBr j : ℂ → X` realizing the `m` Puiseux branches as smooth
   functions of the base, nor the moving-sum representation.  This is the one well-defined geometric
   construction still open (Forster §5 normal form ⟶ continuous `m`-root frame).

2. **The global selection `Φ` + the canonical-fibre condition** (`hΦinjReg`/`hΦrangeReg` + `hselFin`).
   `Φ` must, near every regular value, enumerate the full fibre `F⁻¹(coe ·)` as a set, and near every
   pole-value re-select the pole sub-fibre.  Off the branch locus the sphere sheet systems exist
   (`exists_sphereSheetSystem`); the residual is the *coherent global choice* of `Φ` agreeing with them
   as sets (the labeling is dissolved by the symmetric lever, so only the set-equality is needed).

3. **The `∞`-adaptedness + rationality bookkeeping** (`Dinf`/`hxs_*`, `hglue_inf`, `hcont_int`,
   `R₀ 0 = 0`).  The cover unramified over `∞` (the `∞`-fibre `InftyFibreData`), the `∞`-glue (Lemma 3.2
   in the reciprocal chart), junk-freeness (the meromorphic normal form at each centre), and the
   genus-`0` `∞`-vanishing (`H⁰(ℂℙ¹, Ω) = 0`).

The off-branch sphere-sheet *existence* and *regularity* (`Sreg`/`hderivReg`/`hsheetInjReg`/
`hsheetMemReg`) are mechanically dischargeable from `exists_sphereSheetSystem` +
`criticalValues_finite_general` once `br` is taken to contain the (finite) branch values; they are kept
as arguments here only to avoid duplicating that off-branch bookkeeping inside the wiring file.

**Bottom line.**  Gate A `∑Res = 0` is axiom-clean-reduced to the global full-fibre frame; the single
minimal *new* obligation is residual (1), the continuously-varying branched `m`-sheet Puiseux frame +
its moving-sum germ equality.  Residuals (2) and (3) are the previously-known global-`Φ` and
`∞`-rationality content.  Gate A is **not** yet unconditional.

## Files (this update)

* `Jacobians/Dolbeault/FormTracePatchedFrame.lean` (new) — `hbnd_of_sheetFrame`,
  `patchedTraceSelection_ofFrame`, `residueSum_eq_zero_ofFrame`, `residueSum_eq_zero_ofFrame_holomorphic`.

Reuse (unchanged, PROVEN): `FormTraceGlobalTPatched` (`PatchedTraceSelection`,
`residueSum_eq_zero_of_patchedTraceSelection`, `tendsto_zero_valueChartTrace_of_sheetSections`, the empty
witness), `FormTraceRegularValueDatum` (`MovingCoherenceDatum.ofSphereSheetSystemCanon`),
`FormTraceMovingFibreSheet` (`MovingCoherenceDatum.ofSheetSections`), `FormTraceSphereSheetTranslate` /
`FormTraceMovingFibreSphereSet` (`exists_sphereSheetSystem`, the canonical-fibre lever).
