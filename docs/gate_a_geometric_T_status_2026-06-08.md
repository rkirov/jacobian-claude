# Gate A — geometric global trace `T` from the bundle pushforward: status (2026-06-08)

**Status:** geometric `T` definition + Gate-A reduction + non-vacuity COMPLETE, axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `sorry`, no custom axiom).  The irreducible §VIII.3
content (the branched-cover **germ-coherence** / monodromy) isolated as the minimal remaining
obligation with a precise close-path.

File: `Jacobians/Dolbeault/FormTraceGlobalGeometric.lean` (new, 7 declarations).
Plan: `docs/gate_a_geometric_T_plan_2026-06-08.md`, `docs/miranda_VIII3_confirmation_2026-06-08.md`.

---

## What was built (axiom-clean)

* **`valueChartTrace ω₀ f Φ`** — the geometric global trace `T : ℂ → ℂ` of `α = ω₀·g` along
  `F = f.toRiemannSphere`, read in the affine value chart, from a *global fibre selection*
  `Φ : (b : ℂ) → FibreRegularData g f b`: `T b := (fibreTrace ω₀ f (Φ b)).traceCoeff b`.  This is the
  **same** `fibreTrace.traceCoeff` machinery the glue hypothesis of `globalTrace_of_glue` compares
  against (which uses the pole sub-fibre selection `fibreReg hac`), so the bundle pushforward and the
  glue target speak the same language.

* **`analyticAt_valueChartTrace_of_eventuallyEq`** — `T` is analytic at a base value `b` *given* it
  germ-equals a fixed regular fibre trace `D` over `b` (with `g`'s chart-pullback analytic at each
  fibre point of `D`).  Routes through the proved `analyticAt_of_eventuallyEq_regularFibreTrace`.  The
  off-exceptional analyticity `hT_off`, modulo the off-branch germ-coherence.

* **`residueSum_eq_zero_of_geometricSelection`** — **Gate A `∑ₐ Resₐ(α) = 0`** from `T =
  valueChartTrace ω₀ f Φ` plus the glue/coherence inputs, wired into `residueSum_eq_zero_of_glue`.

* **`residueSum_eq_zero_of_geometricSelection_coh`** — the same, but with `hT_off` *discharged* from
  per-regular-value coherence `hreg` (a regular fibre `Dreg z` over each `z` off the centres, with the
  germ-equality + `g`-analyticity).  This is the maximally-reduced form: the only inputs left are the
  germ-coherence (finite / `∞` / off-exceptional), junk-freeness, and the genus-`0` `∞`-vanishing.

* **`valueChartTrace_emptySelection`** + **`residueSum_eq_zero_of_geometricSelection_holomorphic`** —
  non-vacuity: the empty fibre selection gives `T ≡ 0`, and the empty-pole Gate-A reduction is
  satisfiable — confirming the constructors are honest (not a disguised `False`).

The conclusion `∑ a ∈ poles, formFnResidue ω₀ g a = 0` is **exactly** Gate A's target (cf.
`FormResidueTheorem.residueSum_eq_zero_of_formResidueTrace`).

---

## The minimal remaining obligation (the irreducible §VIII.3 monodromy)

Gate A `∑Res(α) = 0` is now **unconditional modulo the germ-coherence** of the geometric trace
`valueChartTrace ω₀ f Φ` with the local fibre traces, for a suitable global fibre selection `Φ`:

1. **The finite/∞ glue** (`hglue_fin`/`hglue_inf`) — `T` germ-equals the pole sub-fibre trace
   `(fibreTrace ω₀ f (fibreReg hac (cs i))).traceCoeff` off each finite pole-value, and `recipCoeff T`
   germ-equals the `∞`-fibre trace off `0`.
2. **The off-exceptional coherence** (`hreg`) — at each value off the centres, `T` germ-equals a fixed
   *regular* fibre trace (the off-branch sheet-gluing).
3. **Junk-freeness** (`hcont_int`) + the **genus-`0` `∞`-vanishing** (`R₀ 0 = 0`).

### The honest soundness note (pole sub-fibre vs full fibre) — UNCHANGED from the predecessor

`globalTrace_of_glue`'s `hglue_fin` glues `T` to the **pole sub-fibre** trace `fibreReg hac p`, not
the full fibre.  The genuine geometric trace sums over the *full* fibre; the two share the residue
(regular sheets are holomorphic) but germ-agree only when the cover **separates the poles of `α` from
the regular fibre points** over each pole-value.  We keep `T` parametrized by the selection `Φ` and
phrase the glue as the coherence hypothesis directly — **no false full-fibre germ-equality is
asserted**.  The separation genericity is folded into the global selection (a Gate-D refinement).

---

## Close-path for the germ-coherence (the deepest geometric piece — multi-session)

The coherence is realizable from the **PROVEN bundle pushforward** `Jacobians.TraceForm.traceForm`:
`traceForm F ω₀ : HolomorphicOneForms RiemannSphere` is a genuine *globally-coherent* holomorphic form
off the branch locus, and off-branch `(traceForm F ω₀).toFun y = ∑ᵢ sheetPullback ω₀ (S.sheet i) y`
(`exists_localSheetSystem_traceForm_eq_sum`).  The bridge to `valueChartTrace` (the `g≡1` frame) is:

1. **Value-chart coefficient read.**  `coeffAt (traceForm F ω₀) (coe b) b = localRep (traceForm F ω₀)
   (coe 0) (coe b)` in the affine sphere chart, where the affine unit tangent is `1`
   (`ProjectiveLine.trivAt_zero_symmL_one`).  So the value-chart coefficient is `(traceForm F ω₀).toFun
   (coe b) (unit tangent)`.

2. **Per-sheet covector identity (THE LINCHPIN — not yet formalized).**
   `sheetPullback ω₀ s y v = (ω₀.toFun (s y)) (mfderiv 𝓘(ℂ) 𝓘(ℂ) s y v)` (definitional, verified).
   The remaining work: read this in charts — `mfderiv s y` in the affine sphere chart equals the
   planar derivative `deriv (chart_{sy} ∘ s ∘ chartCoe.symm)` of the section in coordinates (the
   `mfderiv = fderiv f_loc` machinery of `LineIntegral.pathSpeed_comp_eq_mfderiv`, incl. the
   `restrictScalars ℝ→ℂ` diamond fix), and `ω₀.toFun (s y) (unit source tangent) = coeffAt ω₀ (s y)
   (chart_{sy} (s y)) = localRep ω₀ (s y) (s y)`.  Combined: the bundle per-sheet coefficient equals
   the **planar** `coeffAt ω₀ (s (coe b)) (...) · deriv(planar section)` — i.e. the `fibreTrace`
   summand for `g≡1`.  Estimated ~200–400 LoC of manifold/chart computation.

3. **Section identification.**  The bundle sheet `S.sheet i : RiemannSphere → X` and the planar sheet
   `(fibreTrace).sheet i : ℂ → ℂ` (from `exists_planar_section`) are both the unique local inverse of
   `F`/its chart-pullback through the same fibre point, hence chart representations of each other
   (uniqueness of the local biholomorphic inverse).  Lets the bundle fibre sum be reindexed onto the
   planar fibre.

4. **The `g`-weighting.**  `α = ω₀·g` is *meromorphic*, so `traceForm` (holomorphic-only) does **not**
   apply to `α` directly; the `g`-weight enters per-sheet inside `coeff i = chartIntegrand ω₀ g (xs i)`.
   The coherence for the `g`-weighted trace follows from the `g≡1` coherence (steps 1–3) by inserting
   the per-sheet scalar `g (chart⁻¹ (sheet i w))` (analytic where `g` is, meromorphic at poles), since
   `traceCoeff` is `∑ coeff i (sheet i w)·deriv(sheet i)` and the `g`-factor rides along each sheet.

5. **Genus-`0` `∞`-vanishing `R₀ 0 = 0`.**  The holomorphic remainder `T − L.R` (principal parts
   removed) is a holomorphic `1`-form on `ℂℙ¹`; package it via `traceForm` of the holomorphic part and
   apply `ProjectiveLine.holomorphicOneForm_eq_zero` (PROVEN: `HolomorphicOneForms RiemannSphere`
   subsingleton) ⟹ its `dζ`-coefficient at `∞` is `0`.

Steps 1–4 are the genuine analytic frontier (the predecessor's "deepest geometric piece, multi-session").
The foundation + reduction + non-vacuity in this file make Gate A turn the key on exactly these inputs.

---

## Files

* `Jacobians/Dolbeault/FormTraceGlobalGeometric.lean` (new) — 7 declarations, axiom-clean.
* `docs/gate_a_geometric_T_plan_2026-06-08.md` (new) — the plan.

Reuse (unchanged, PROVEN): `FormTraceGlobalTAssemble` (`globalTrace_of_glue` / `residueSum_eq_zero_of_glue`),
`FormTraceGlobalT` (`analyticAt_of_eventuallyEq_regularFibreTrace`), `FormTraceFibre`/`FormTraceGlobalFunction`
(`fibreTrace`/`traceCoeff`/`analyticAt_traceCoeff`), `FormTraceGlobalConstruct` (`AdaptedCover`/`fibreReg`),
`TraceForm` (the bundle pushforward `traceForm`, the close-path engine), `ProjectiveLine`
(`holomorphicOneForm_eq_zero`, the affine-frame unit tangent).
