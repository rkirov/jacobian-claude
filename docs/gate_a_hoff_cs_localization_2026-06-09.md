# Gate A `hoff_cs` elimination — precise localization + scope verdict (2026-06-09)

**Branch:** `gate-a-trace-rationality-assembly` · **Mode:** analysis only (no Lean edits committed; no
sound on-critical-path increment was reachable without the missing analytic atom). · **Baseline:**
`Jacobians.Dolbeault.SerreResidueGateAClosed` builds green (8516 jobs), axiom-clean.

## Verdict

Eliminating `hoff_cs` (α's finite pole-values off `f`'s branch locus) is a **genuine multi-thousand-line
refactor**, gated on an analytic atom Mathlib lacks and the repo deliberately avoided. It is NOT a
one-lemma swap. This file pinpoints the exact 3 consumption sites, the 2 facts they provide, the
structural wall, and the single irreducible remaining sub-lemma. Companion textbook re-reading:
`docs/gate_a_cover_genericity_textbook_2026-06-08.md` (C-route i). Steering: `human_input.md` (2026-06-09).

## Where `hoff_cs` is genuinely consumed (exactly 3 call sites, ONE file)

Everything *above* `residueTheorem_ofCanonicalSimpleInfty_genus0_germ_Cfull` merely **threads** `hoff_cs`
as a hypothesis (`SerreResidueInftyCoherence.lean`, `SerreResidueGateAClosed.lean`,
`SerreResidueDirectGenus0GermDischarge.lean` L240/L327/L480). It is genuinely *used* only in
`Jacobians/Dolbeault/SerreResidueDirectGenus0GermDischarge.lean`, inside
`residueTheorem_ofCanonicalSimpleInfty_genus0_germ_Cfull`:

| Site | Line | Use |
|---|---|---|
| 1 | `:264` | `exists_sphereSheetSystem f … (hoff_cs i)` — sphere-sheet system `S i` at the pole-value centre `cs i` (needs `coe (cs i)` off-branch = distinct unramified sheets). |
| 2 | `:288` | `movingCoherenceDatum_canonical hdiv (hoff_cs i) (S i) …` — builds `Cfull i : MovingCoherenceDatum … (cs i)`. |
| 3 | `:291-292` | `movingCoherenceDatum_canonical_D_inj` / `_D_image (hoff_cs i) …` — the combinatorial fields. |

`Cfull i` feeds `residueTheorem_ofCanonicalSimpleInfty_genus0_germ`
(`SerreResidueDirectGenus0Germ.lean`), where (`globalTraceData_of_genus0_germ`, L330-380) it provides
**exactly two facts at `cs i`**:

- **(A) meromorphy** `MeromorphicAt T (cs i)`  (L332-334: `Cfull.coherent_punctured` +
  `meromorphicAt_traceCoeff_fibreTrace`), feeding the principal-part extraction
  `exists_laurentForm_principalPart`.
- **(B) residue identity** `resAt T (cs i) = ∑_{p∈fibre} formFnResidue ω₀ g p`  (L379:
  `hres_fin_of_fullFibreCoherence`).

Here `T := valueChartTracePatched ω₀ f (canonicalFibreSelection g f hdiv) br`.

## The structural wall (why both (A) and (B) are deep)

Both (A) and (B) are realized through one chain:

```
Cfull.D : FibreRegularData g f (cs i)            -- the FIXED reference fibre over cs i
  → fibreTrace ω₀ f Cfull.D : FibreTrace          -- as DISTINCT unramified sheets
  → FibreTrace.resAt_traceCoeff'                   -- the UNRAMIFIED Lemma 3.2
```

- **`FibreRegularData`** (`FormTraceFibre.lean:158`) has field
  `hg_deriv : deriv (f.holoRepr ∘ chart⁻¹) (chart (xs i)) ≠ 0` at *every* fibre point — i.e. the fibre
  points are REGULAR/unramified. At a ramified `cs i` the fibre points ARE the ramification points
  (`deriv = 0`), so **`FibreRegularData g f (cs i)` cannot exist**, hence `MovingCoherenceDatum … (cs i)`
  cannot exist. The entire `Cfull`/`fibreTrace`/`valueChartTrace`-at-a-centre route is *structurally
  impossible* over a ramified centre.
- **`FibreTrace`** (`MeromorphicTrace.lean:312`) likewise bakes in
  `sheet_deriv_ne : deriv (sheet i) b ≠ 0` — it models a fibre as `m` distinct unramified sheets, never a
  single `z = wᵐ` ramified sheet.
- The residue atom **`residueChangeOfVariables`** (`ResidueChangeOfVariables.lean`) requires
  `deriv s b ≠ 0` (local biholomorphism). It does **not** cover the ramified `w ↦ wᵐ` case.
  "`resAt_traceCoeff'` is unconditional" means only that it no longer takes the atom as a *hypothesis*;
  it still covers only UNRAMIFIED sheets. **It is NOT the ramified-fibre Lemma 3.2.**

Every alternative route in the repo (`FormTraceCoherenceFromMoving.meromorphicAt_valueChartTrace_of_movingDatum`,
`FormTraceBranchAwareSelection`'s `Cfin`/`Creg`, `FormResidueTrace.fibre : ℂ → FibreTrace`) goes through
the same `FibreRegularData`/`FibreTrace` unramified model. Mathlib has **no** "analytic on a punctured
neighbourhood ⟹ meromorphic" constructor (meromorphy needs a concrete Laurent order, i.e. a growth bound),
so (A) is not separable from the ramified growth estimate either.

## The single irreducible remaining sub-lemma (the genuine Miranda (3.1) keystone)

At a ramified pole-value `cs i` (take single preimage `p`, mult `m`; `α = ω₀·g`, `g` meromorphic), prove
both (A) and (B). The irreducible analytic atom is the **ramified residue change-of-variables / contour
substitution** `z = wᵐ`:

> `Res_{z=0}( Tr_m α ) = Res_{w=0}(α)`,  where `Tr_m α (z) dz := Σ_{ζᵐ=1} α(ζ · z^{1/m})` (the m-branch
> sum). Miranda (3.1): `Tr_m α = Σₖ c_{km-1} z^{k-1} dz` (`g = Σ cₙ wⁿ`), so the residue is
> `c_{-1} = Res_w(α)`.

It needs ONE of:
1. **Contour reparametrization under `wᵐ`**: `∮_{|z|=rᵐ} Tr_m α dz = ∮_{|w|=r} α dw` (winding-`m`
   substitution). **Mathlib has NO `circleIntegral` change-of-variables / winding-number invariance**
   (stated at `ResidueChangeOfVariables.lean:29-31`; the repo works *around* it via holomorphic
   primitives, which works only for the UNRAMIFIED `deriv≠0` case). This atom is a ~several-hundred-LoC
   Mathlib-gap analytic build.
2. **Roots-of-unity Laurent summation** to derive (3.1) directly via `Σ_{ζᵐ=1} ζⁿ⁺¹ = m · [m ∣ n+1]`,
   then read off `k=0`. Needs the heavy `RootsOfUnity` machinery the repo deliberately AVOIDED
   (`TraceForm.lean:1769`, `FormTraceBundleBranchBound.lean:33` — branch boundedness was done by growth
   estimates, no roots of unity / Puiseux).

PLUS:
- **g-weighting**: at a pole-value `cs i` the numerator `g` has poles in the fibre, so even the
  ramification-robust bundle SUM `traceFun`/`traceFunExt` (which the proven `hbnd` route uses — but only
  at BRANCH values *off* pole-values, where `g` is BOUNDED) does not directly apply; the residue needs a
  *g-weighted* ramified Lemma 3.2.
- **a `FibreTrace`-level refactor** (or a parallel ramified structure) so (A)/(B) route through the
  ramified atom instead of `resAt_traceCoeff'`, then re-thread `cs i` (drop `hoff_cs`) all the way up to
  `residueTheorem_of_adaptedF` / `AdaptedF.hoff_cs` in `SerreResidueGateAClosed.lean`.

## Soundness checkpoint (no false field — verified by hand)

The residue of a *single* sheet under `wᵐ` is `m · Res_w(g)`, **not** `Res_w(g)`: e.g. `g(z)=z⁻¹`,
`s(w)=w²` gives `g(s(w))·s'(w) = w⁻²·2w = 2w⁻¹`, residue `2 = 2·1`; `s(w)=w³` gives `3w⁻¹`, residue
`3 = 3·1`. The trace residue equals the *upstairs* residue ONLY via the m-branch SUM + the winding-`m`
contour cancellation. Therefore any "single-sheet pushforward residue = upstairs residue" shortcut would
be a **FALSE field** — it was identified and NOT added. The genuine content is the winding/branch-sum
atom above.

## Recommendation

- **Textbook-honest elimination (route a):** build the Mathlib-gap `circleIntegral`-under-`wᵐ`
  substitution atom (sub-lemma route 1), then the g-weighted ramified Lemma 3.2 and a ramified
  `FibreTrace`, then re-thread to drop `hoff_cs`. Large but the principled path.
- **Alternative (route b, keep `hoff_cs`):** discharge `ExistsAdaptedF`
  (`SerreResidueGateAClosed.lean`) by RR-with-prescribed-jets — force `f` unramified over the finite
  pole-values (`f' = (f − a)⁻¹` for `a` off the bad set). Needs `MeromorphicFunction.Inv` + a generic
  -position lemma; see `human_input.md` (2026-06-09, earlier entry).

Both are large; neither is a quick win. The 3 call sites + 2 consumed facts above are the exact retarget
surface.
