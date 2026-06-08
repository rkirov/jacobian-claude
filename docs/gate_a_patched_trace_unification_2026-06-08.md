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
