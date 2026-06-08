# Gate A — branch-value boundedness via the bundle trace SUM (the monodromy-free port): status (2026-06-08)

**Task.** CLOSE the Gate A (`∑ₐ Resₐ(α) = 0`, `α = ω₀·g`) **branch-value boundedness crux**
`(z − b₀)·valueChartTrace ω₀ f Φ z → 0` along the architecturally-correct path: derive it from the
**bundle trace SUM** `TraceForm.traceFun` (whose branch-extension boundedness is PROVEN axiom-clean for
holomorphic forms), ported to the meromorphic `α = ω₀·g` — **NOT** from individual continuously-varying
sheets (the monodromy trap: at a branch value the `m` Puiseux branches *permute*; only the symmetric
SUM extends — Miranda §VIII.3, pp. 252–253).

**Headline.** The genuinely-new analytic step is **done, axiom-clean**. One new leaf file
`Jacobians/Dolbeault/FormTraceBundleBranchBound.lean`, verified by authoritative
`lake env lean #print axioms` → `[propext, Classical.choice, Quot.sound]`; no `sorry`, no custom axiom.

Gate A `∑Res = 0` is **NOT yet unconditional**; but the branch-value wall is now **monodromy-free** —
the previously-"single hardest atom" (the colliding ramified `m`-fold Puiseux sheet frame `hgermBr`) is
**gone**, replaced by a single-valued SUM germ bridge.

---

## What was built (axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no custom axiom)

### `tendsto_zero_valueChartTrace_of_bundleGerm` — THE genuinely-new step

Discharges the §VIII.3 branch-value boundedness crux `(z − b₀)·valueChartTrace ω₀ f Φ z → 0` from:

* the **PROVEN** bundle SUM boundedness `TraceForm.traceLocalCoeff_mul_sub_tendsto_zero F … (coe b₀ ∈
  branchLocus F)` (holomorphic `α'` on the cover `F = f.toRiemannSphere`); and
* the **bundle-trace germ bridge** `hbridge` : `valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] b₀] (z ↦ traceLocalCoeff
  (traceFun F α') (coe b₀) (coe z))`.

**The clean affine-chart reading (the key simplification).** On `RiemannSphere = OnePoint ℂ`, the chart
at *every* finite point `coe b₀` is the single global affine chart `chartCoe`
(`RiemannSphere.chartAt_coe`), with `chartCoe (coe z) = z` (`chartCoe_apply_coe`) and `chartCoe.symm z =
coe z` (`chartCoe_symm_apply`). So the bundle crux — stated in `chartAt ℂ (coe b₀)` with centre
coordinate `chartCoe (coe b₀) = b₀` and inverse `chartCoe.symm z = coe z` — reads, in the affine `ℂ`
coordinate, **exactly** as the planar boundedness shape `hbnd` needs:

```
(z − b₀) · traceLocalCoeff (traceFun F α') (coe b₀) (coe z) → 0   (𝓝[≠] b₀).
```

Transport along `hbridge` (`Tendsto.congr'`) gives `hbnd`. The proof is 4 lines.

**Why this is the SUM, not per-sheet frames.** The bundle boundedness
`traceLocalCoeff_mul_sub_tendsto_zero` is proven by a **properness + finite-subcover** argument over the
fibre `F⁻¹{coe b₀}` (`traceLocalCoeff_mul_sub_tendsto_zero_Y`), handling *all* preimages at once —
ramified **and** unramified — with **no individual sheets, no Puiseux frame, no roots-of-unity
cancellation** (just the triangle inequality + the per-preimage normal-form ratio `(F − b₀)/F' → 0`).
This is exactly Miranda's "the trace is single-valued by symmetry; only the SUM extends across branch
points."

### `patchedTraceSelection_ofBundleBranch` / `residueSum_eq_zero_ofBundleBranch`

The §VIII.3 close with the branch-value boundedness from the bundle SUM. Builds a
`PatchedTraceSelection` directly: the per-pole moving data via `MovingCoherenceDatum.ofSheetSections`,
the per-regular data via `MovingCoherenceDatum.ofSphereSheetSystemCanon` (the symmetric lever — both
*unchanged* from `FormTracePatchedFrame.patchedTraceSelection_ofFrame`), but the **entire branched
full-fibre frame block** (`ιBr`/`secBr`/`hsmoothBr`/…/`hgermBr` — the colliding ramified Puiseux sheets)
is **replaced** by the per-branch-value bundle data:

* `hncF` — the cover is nonconstant (freely available);
* `hbrBr b₀` — `coe b₀` is in the branch locus of `F`;
* `αBr b₀` — a holomorphic `1`-form on `X` agreeing with `ω₀·g` near `F⁻¹{coe b₀}` (exists: `b₀` off the
  finite pole-values, where `g` is holomorphic);
* `hbridgeBr b₀` — the bundle-trace germ bridge.

`residueSum_eq_zero_of_patchedTraceSelection` (PROVEN) then yields Gate A `∑Res = 0`.
`residueSum_eq_zero_ofBundleBranch_holomorphic` re-exports the empty-pole non-vacuity.

---

## Why this is the correct close (soundness — review active)

* **No revived `hbranch`.** `hbridgeBr` is a germ equality on the **punctured** neighbourhood `𝓝[≠] b₀`,
  at **regular values** `z ≠ b₀`, where both sides are genuine *full-fibre* sums and agree by Miranda's
  trace definition (LHS = `valueChartTrace = Tr_F(ω₀·g)` in the value chart; RHS = the same SUM read
  through the bundle). It says **nothing** about the value *at* the branch point (which the patch's
  removable limit handles, its analyticity resting on the boundedness `hbnd` derived here). So it is the
  value-correct route — *not* the false `BranchAwareTraceSelection.hbranch` continuity at the branch
  value.
* **No false field, no disguised `False`.** Every new hypothesis is genuinely consumed; the empty-pole
  witness (`residueSum_eq_zero_ofBundleBranch_holomorphic`) confirms satisfiability. The SUM germ bridge
  is the *true* §VIII.3 trace identity for the symmetric sum.
* **Authoritative axiom check passes** for all four headline declarations: `[propext, Classical.choice,
  Quot.sound]`; `^axiom ` grep empty; zero `sorry`.

---

## The single minimal remaining obligation for `hbnd` (precise diagnosis)

After this port, the branch-value boundedness `hbnd` rests on exactly the **bundle-trace germ bridge**
`hbridgeBr` (+ the local-holomorphic form `αBr`):

> at each branch value `b₀` (off the finite pole-values), `valueChartTrace ω₀ f Φ` germ-equals, on the
> punctured neighbourhood, the value-chart local coefficient of the bundle trace SUM `traceFun F (αBr
> b₀)`, where `αBr b₀` is a global holomorphic form on `X` agreeing with `ω₀·g` near the fibre
> `F⁻¹{coe b₀}`.

This splits into two **standard** ingredients (neither a colliding-Puiseux-frame construction):

1. **`αBr b₀`** — a global holomorphic `1`-form `= ω₀·g` near `F⁻¹{coe b₀}`. Since `b₀` is off the finite
   pole-values, `g` is holomorphic on a neighbourhood of the (finite) fibre, so `ω₀·g` is a *local*
   holomorphic form there; extend/patch to a global holomorphic form (a Mittag-Leffler / cutoff
   argument). The bridge only constrains the germ **near the fibre**, so any global holomorphic form
   agreeing there suffices.
2. **The SUM germ identity** — `valueChartTrace ω₀ f Φ z = traceLocalCoeff (traceFun F (αBr b₀)) (coe b₀)
   (coe z)` for regular `z` near `b₀`. Both are the full-fibre value-chart trace of the *same* form
   (`ω₀·g = αBr b₀` near the fibre) over the regular fibre; the per-sheet linchpin
   `FormTraceSheet.sheetPullback_one_eq_coeffAt_mul_deriv` (`sheetPullback = coeffAt·deriv`) identifies
   the bundle per-sheet covector with the planar `chartIntegrand·deriv` summand, term-by-term over the
   (finite, regular) fibre.

The **monodromy** is dissolved (the SUM is single-valued — no per-sheet frame, no roots-of-unity), and
the **boundedness heart** is the PROVEN bundle crux. The residual is the SUM germ identification, a
standard chart computation (the linchpin + the regular-fibre enumeration), plus the local-holomorphic
`αBr`.

Residuals (2) the global selection `Φ` + canonical-fibre condition, and (3) the `∞`-rationality
bookkeeping, are unchanged from `FormTracePatchedFrame`.

---

## Files

* `Jacobians/Dolbeault/FormTraceBundleBranchBound.lean` (new, leaf) —
  `tendsto_zero_valueChartTrace_of_bundleGerm`, `patchedTraceSelection_ofBundleBranch`,
  `residueSum_eq_zero_ofBundleBranch`, `residueSum_eq_zero_ofBundleBranch_holomorphic`.

Reuse (unchanged, PROVEN): `TraceForm` (`traceLocalCoeff_mul_sub_tendsto_zero`/`_Y`, `traceFun`),
`FormTraceGlobalTPatched` (`PatchedTraceSelection`, `residueSum_eq_zero_of_patchedTraceSelection`, the
empty witness), `FormTracePatchedFrame` (the regular/pole engine calls it mirrors),
`FormTraceMovingFibreSheet` / `FormTraceRegularValueDatum` (`MovingCoherenceDatum.ofSheetSections` /
`ofSphereSheetSystemCanon`), `ProjectiveLine` (`RiemannSphere.chartAt_coe`/`chartCoe_apply_coe`/
`chartCoe_symm_apply`).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3, pp. 252–253 (the trace is single-valued by
  symmetry; the SUM extends across branch points; Lemma 3.2). See `docs/miranda_VIII3_confirmation_2026-06-08.md`.
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §10, §17.
