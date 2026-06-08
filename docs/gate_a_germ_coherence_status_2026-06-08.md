# Gate A — branched-cover germ-coherence: status (2026-06-08, session 2)

**Status:** the **per-sheet covector linchpin** (Miranda §VIII.3, the predecessor's flagged "deepest
geometric piece") is **PROVEN axiom-clean**, together with the `localRep` frame-transition law and the
single-sheet bridge (both `g≡1` and `g`-weighted) connecting the bundle pushforward summand to the
planar `FormTraceFibre.fibreTrace` summand.  The remaining obligation to make Gate A `∑Res=0`
**unconditional** is reduced to exactly the **section identification** (bundle sheet ↔ planar inverse,
uniqueness of local biholo) + the **coherent global selection `Φ`** construction, with the precise
close-path below.

Files (new, both axiom-clean `[propext, Classical.choice, Quot.sound]`, zero custom axioms, zero `sorry`):

* `Jacobians/Dolbeault/FormTraceSheetCovector.lean` — the linchpin + frame-transition.
* `Jacobians/Dolbeault/FormTraceSheetFibreBridge.lean` — the single-sheet bridges (`g≡1`, `g`-weighted).

---

## What was proven (axiom-clean)

### `FormTraceSheetCovector.lean`

1. **`symmL_self_one`** — `(trivAt a).symmL ℂ a 1 = 1`: the self-frame unit tangent is the model unit
   (the self chart-transition `chart_a ∘ chart_a.symm = id` has derivative `1`).
2. **`localRep_self_eq_toFun_one`** — `localRep ω₀ a a = ω₀.toFun a 1` (corollary).
3. **`toFun_apply_eq_mul_localRep`** — `ω₀.toFun a w = w · localRep ω₀ a a`: the covector pairing in
   the self frame is scalar multiplication by the centred local representative (ℂ-linearity).
4. **`localRep_eq_transition_mul_self`** — the **frame-transition law**:
   `localRep ω₀ a y = deriv(chart_y ∘ chart_a.symm)(chart_a y) · localRep ω₀ y y`.  (Generalizes the
   `∞`-case `ProjectiveLine.inftyCoeff_eq_transition` to arbitrary charts; the `dz`-Jacobian.)
5. **`mfderiv_eq_fderiv_chartPullback`** — `mfderiv s y = fderiv ℂ (chart_{s y} ∘ s ∘ chart_y.symm)
   (chart_y y)` (the `mfderiv = fderiv` reading; cf. `LineIntegral.pathSpeed_comp_eq_mfderiv`).
6. **`sheetPullback_apply_eq_coeffAt_mul_deriv`** (+ `_one` variant) — **THE LINCHPIN**:
   `sheetPullback ω₀ s y v = fderiv ℂ (chart_{s y} ∘ s ∘ chart_y.symm) (chart_y y) v · coeffAt ω₀
   (s y) (chart_{s y}(s y))`.  The bundle per-sheet covector read in charts as the planar
   `coeffAt·deriv(section)` object (the `g≡1` `fibreTrace` summand, read in the *moving* fibre-point
   chart).

### `FormTraceSheetFibreBridge.lean`

7. **`sheetPullback_one_eq_fixedChart_coeffAt_mul_deriv`** — the **single-sheet bridge**
   (source-chart independence of the value-chart `dz`-coefficient): the bundle summand equals the
   planar `coeffAt·deriv` summand read in a *fixed* source chart `xs`.  Reconciles the linchpin's
   moving-chart reading with the fixed-chart `fibreTrace` reading via the frame-transition law + the
   `deriv` chain rule — the `dz`-Jacobian cancellation.
8. **`g_weighted_sheetPullback_eq_chartIntegrand_mul_deriv`** — the `g`-weighted bridge:
   `g(s y) · sheetPullback ω₀ s y 1 = chartIntegrand ω₀ g xs (sh w) · deriv(sh) w` — the **exact**
   `FormTraceFibre.fibreTrace.traceCoeff` summand (`coeff i = chartIntegrand ω₀ g (xs i)`).
9. **`eventuallyEq_of_rightInverse_of_rightInverse`** — **uniqueness of the holomorphic local
   inverse**: two continuous right-inverses of an analytic `φ` (`deriv ≠ 0`) agreeing at the base
   germ-agree (both equal the canonical `localInverse`).
10. **`fibreTrace_sheet_eventuallyEq`** — the **section identification**: the `fibreTrace` planar
   sheet (`Classical.choose` inverse of `f.holoRepr ∘ chart⁻¹`) germ-equals any continuous
   right-inverse of that chart pullback through the fibre point — in particular the
   chart-representation of a bundle sheet (a section of `F`).

These discharge the predecessor's **step 1 (the linchpin, ~200–400 LoC estimate)**, the **step 2
section identification** (both the uniqueness-of-local-inverse half **and** the Jacobian-cancellation
half), and the **step 4 `g`-weighting** — all axiom-clean.

---

## The minimal remaining obligation (precise)

To make `residueSum_eq_zero_of_geometricSelection_coh` discharge Gate A unconditionally, supply its
hypotheses `hglue_fin`/`hglue_inf`/`hreg` (germ-coherence) + junk-freeness + the genus-`0`
`∞`-vanishing.  After the bridges above, what remains is:

### (A) Section identification — **CORE PROVEN** (`fibreTrace_sheet_eventuallyEq`)

The planar section `(fibreTrace ω₀ f D).sheet i` germ-equals any continuous right-inverse of
`f.holoRepr ∘ chart_{xs i}.symm` through the fibre point (`fibreTrace_sheet_eventuallyEq`, axiom-clean,
via the uniqueness lemma).  **What remains for (A):** verify that the chart-representation
`chart_{D.xs i} ∘ bsₖ ∘ chartCoe.symm` of a bundle sheet `bsₖ` (from `TraceForm.LocalSheetSystem`)
**is** such a right-inverse — i.e. `f.holoRepr (bsₖ (coe w)) = w` near `b` — which follows from `bsₖ`
being a section of `F = f.toRiemannSphere` plus `toRiemannSphere_eventuallyEq_coe_holoRepr` (matching
`F` with `coe ∘ holoRepr` near a non-pole).  This is the only mechanical residue of (A) (~40–80 LoC,
no new geometry — just feeding the right-inverse hypothesis of `fibreTrace_sheet_eventuallyEq`).

### (B) Coherent global selection `Φ`

Construct `Φ : (b : ℂ) → FibreRegularData g f b` so that, near each base value, `(fibreTrace ω₀ f
(Φ b')).traceCoeff b'` is the **single holomorphic function** given by the bundle fibre sum (using (A)
termwise), hence germ-equals the fixed local fibre traces `fibreReg hac (cs i)` / `Dinf` / `Dreg`
(the `hglue_fin`/`hglue_inf`/`hreg` inputs).  RESPECT the soundness nuance: glue to the **pole
sub-fibre** (`fibreReg`), folding pole/regular separation into `Φ` (a Gate-D refinement) — do **not**
assert false full-fibre germ-equality.

### (C) Genus-`0` `∞`-vanishing `R₀ 0 = 0`

The holomorphic remainder `T − L.R` is a holomorphic `1`-form on `ℂℙ¹`; package via the bundle
holomorphic part + `ProjectiveLine.holomorphicOneForm_eq_zero` (PROVEN subsingleton).  Independent of
(A)/(B), concrete.

### (D) Junk-freeness `hcont_int`

From the meromorphic normal form of `T − L.R` at each centre (the principal part removed).

---

## Close-path summary

`residueSum_eq_zero_of_geometricSelection_coh` (PROVEN, `FormTraceGlobalGeometric.lean`) turns the key
on exactly {(A) section identification, (B) coherent `Φ`, (C) `∞`-vanishing, (D) junk-freeness}.  The
**deepest geometric content is now PROVEN axiom-clean** (this session): the step-1 linchpin, the
step-2 section identification (uniqueness of local inverse **and** the Jacobian-cancellation single-
sheet bridge), and the step-4 `g`-weighting.  The remainder is:

* **(A) residue** — feed the bundle sheet's right-inverse property to `fibreTrace_sheet_eventuallyEq`
  (~40–80 LoC, mechanical, no new geometry);
* **(B)** the coherent-selection `Φ` bookkeeping (sum the per-sheet bridge over the fibre → a single
  holomorphic germ; phrase against the pole sub-fibre `fibreReg`);
* **(C)** the genus-`0` `∞`-vanishing (`holomorphicOneForm_eq_zero`, concrete);
* **(D)** junk-freeness (meromorphic normal form, concrete).

No unsound shortcut was taken: every new lemma is axiom-clean `[propext, Classical.choice, Quot.sound]`
with zero custom axioms, and the honest pole-sub-fibre soundness nuance is preserved (the bridges are
stated per-sheet and frame-independently — no false full-fibre germ-equality is asserted).
