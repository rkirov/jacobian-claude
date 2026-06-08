# Gate A — the moving-fibre sheet selection (§VIII.3): status (2026-06-08, session 4)

**Status.**  Gate A's 1-form residue theorem `∑_{a ∈ poles} Res_a(α) = 0` (`α = ω₀·g`) is reduced —
soundly, **axiom-clean** (`[propext, Classical.choice, Quot.sound]`, zero custom axioms, zero `sorry`),
**non-vacuously** — to the existence of a single **`MovingSheetSelection`**, whose per-value moving data
is itself reduced to the **§VIII.3 re-selection bijection alone** (all germ / `dz`-Jacobian /
differentiability content is discharged).

New file (axiom-clean, verified via `lake env lean` `#print axioms`):

* `Jacobians/Dolbeault/FormTraceMovingFibreSheet.lean` — the index-bijection bookkeeping bridge: from
  continuously-varying smooth sections (branched-cover sheets) to `MovingCoherenceDatum`, and the
  sheet-form Gate-A reduction `MovingSheetSelection ⇒ MovingCoherenceFamily ⇒ ∑Res = 0`, with the
  end-to-end non-vacuity witness.

This builds directly on the proved §VIII.3 monodromy heart of session 3
(`FormTraceMovingFibre.lean` / `FormTraceCoherentFromMoving.lean`,
`docs/gate_a_moving_fibre_monodromy_status_2026-06-08.md`).

---

## What was proven this session (axiom-clean)

### Mechanical discharge of the per-value moving data

1. **`transition_analyticAt_overlap`** / **`transition_differentiableAt_overlap`** — the `C^ω`-atlas
   chart change `chartAt z ∘ (chartAt y).symm` is analytic / differentiable at any overlap point
   (inline `contMDiffOn_chart` argument; no heavy Čech import).
2. **`differentiableAt_chart_pullback_section`** — the own-chart pullback `z ↦ chartAt (s b') (s z)` of a
   `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` section is `DifferentiableAt ℂ` (chart `C^ω` ∘ section `C^ω`, then
   `contMDiffAt_iff_contDiffAt`).
3. **`MovingCoherenceDatum.ofSheetSections`** — *the index-bijection bridge.*  Builds a
   `MovingCoherenceDatum` at `b₀` from manifold sections `sec : D.ι → ℂ → X` of `f.holoRepr` through `D`
   (smooth + section property at `b₀`) plus the **§VIII.3 re-selection bijection** `hsel`: near `b₀`,
   `∃ e : (Φ b').ι ≃ D.ι, (Φ b').xs i' = sec (e i') b'` and `sec i b' ∈ chart_{D.xs i}.source`.  *All*
   `MovingCoherenceDatum.ofBijection` side-conditions are discharged:
   * the **section-derivative match** via `FormTraceSheet.fibreTrace_sheet_eventuallyEq` (the planar
     sheet of `fibreTrace (Φ b')` germ-equals the chart-pullback `chart_{sec (e i') b'} ∘ sec (e i')`,
     both right-inverses of `f.holoRepr`'s chart-pullback through `(Φ b').xs i' = sec (e i') b'`);
   * chart-pullback differentiability via (2);
   * the chart transitions via (1);
   * the eventual smoothness / section facts via `contMDiffAt_iff_contMDiffAt_nhds` (ω ≠ ∞) +
     `eventually_eventually_nhds`.
   The caller supplies **only** the geometric re-selection bijection.
4. **`MovingCoherenceDatum.ofLocalSheetSystem`** — the `LocalSheetSystem`-packaged form of (3) (sections
   `sec i := S.sheet (eD i)` read off the sheet system, smoothness/section from the sheet fields).

### The sheet-form Gate-A reduction

5. **`MovingSheetSelection`** — the whole Gate-A input in sheet form: the global selection `Φ`, the
   per-pole-value sheet sections through the **pole sub-fibre** `fibreReg hac (cs i)` (honest separation)
   + their re-selection bijections `hselFin`, the per-regular-value reference fibre + sheet sections +
   re-selection bijections `hselReg`, the finite/∞ enumeration, the `∞`-glue, junk-freeness, and the
   genus-`0` continuation.
6. **`MovingSheetSelection.toMovingCoherenceFamily`** — derives the per-value `MovingCoherenceDatum`
   (`Cfin`/`Creg`) from the sheet sections via (3); the pole-sub-fibre `hCfin_D` is `rfl`.
7. **`residueSum_eq_zero_of_movingSheetSelection`** — Gate A `∑Res = 0` from a `MovingSheetSelection`
   (via (6) + the proved `residueSum_eq_zero_of_movingCoherenceFamily`).
8. **`movingSheetSelection_empty`** / **`residueSum_eq_zero_of_movingSheetSelection_holomorphic`** —
   end-to-end non-vacuity (empty pole set ⇒ `∑Res = 0`; the empty re-selection equiv, all per-point
   fields vacuous).  Confirms the reduction is honest (not a disguised `False`).

---

## The minimal remaining obligation (precise + diagnosed)

Gate A `∑Res = 0` is reduced — soundly, axiom-clean — to **the existence of a `MovingSheetSelection`**.
Its fields are individually either proved infrastructure or one of four precise residuals:

### (A) The global selection `Φ` + the per-value sheet sections + re-selection bijections

The genuine §VIII.3 monodromy.  Build the global selection `Φ : (b : ℂ) → FibreRegularData g f b` and,
at each pole-value `cs i` (against the pole sub-fibre) and each regular value `z`, the
continuously-varying sections `sec` of `f.holoRepr` with the re-selection bijection
`(Φ b').xs i' = sec (e i') b'` near the base value.

**Diagnosis / close-path.**  *All germ content is discharged* — only the bijection + section existence
remains.  The sections are the branched-cover sheets, which exist via `Jacobians.exists_localSheetSystem`
(PROVEN, Forster §4.22) — **but for the compact sphere map `f.toRiemannSphere : X → RiemannSphere`, NOT
directly for `f.holoRepr : X → ℂ`** (the codomain `ℂ` is non-compact, so `exists_localSheetSystem`'s
`CompactSpace Y` hypothesis fails).  The missing translation is:

> a `LocalSheetSystem f.toRiemannSphere (coe b₀)` over a finite-value region, restricted to finite values
> via `coe : ℂ → RiemannSphere`, yields sections of `f.holoRepr`:
> `f.holoRepr (sheet (coe b')) = b'`.

This is tractable from the proved `MeromorphicFunction.toRiemannSphere_of_nonneg`
(`toRiemannSphere y = coe (holoRepr y)` at non-poles) + `OnePoint.coe` injectivity + non-pole
preservation near a regular value (poles are isolated).  Once the sheets are in `f.holoRepr`-section
form, the **identity re-selection bijection** applies *whenever `Φ b'` is defined as the sheet fibre
data* (`(Φ b').xs i' = sheet i' b'` by construction, `e = Equiv.refl`).  The residual genuine content is
the **global patching** of these local sheet selections into one `Φ` consistent across the whole
punctured sphere (the monodromy permutation of sheets across overlaps) + the pole/regular separation
genericity at the pole-values.

### (B) The `∞`-fibre reciprocal glue `hglue_inf`

The reciprocal-chart analogue of (A) at `∞` (`recipCoeff (valueChartTrace) =ᶠ[𝓝[≠] 0] (inftyFibreTrace
ω₀ f Dinf).traceCoeff`) — structurally identical (the same moving-frame argument in the reciprocal
coordinate `ζ = 1/w`).

### (C) Junk-freeness `hcont_int`

The remainder `valueChartTrace − L.R` is continuous at each centre (the meromorphic normal form, the
principal part removed).  Concrete.

### (D) Genus-`0` `∞`-vanishing `R₀ 0 = 0`

Dischargeable via the proved `coeffAt_eq_zero_of_sphereForm` (`H⁰(ℂℙ¹, Ω) = 0`).  Concrete, independent
of (A)/(B)/(C).

---

## Close-path summary

`residueSum_eq_zero_of_movingSheetSelection` (PROVEN) turns the key on Gate A from a single
`MovingSheetSelection`.  This session pushed the reduction one level deeper than session 3's
`MovingCoherenceFamily`: the per-value moving data is now in **sheet form**, reduced to the §VIII.3
re-selection bijection + continuously-varying sheet sections, with *all* the
germ/`dz`-Jacobian/differentiability bookkeeping discharged (`MovingCoherenceDatum.ofSheetSections`).

The remaining obligation is the **global sheet selection** (A) — build `Φ` from the (proved) branched
cover sheets, translated from the sphere map to `f.holoRepr`-sections, patched globally + pole/regular
separation — plus the `∞`-glue (B), junk-freeness (C, concrete), and the genus-`0` vanishing (D,
`coeffAt_eq_zero_of_sphereForm`, concrete).

No unsound shortcut: every new lemma is axiom-clean with zero custom axioms; the pole-sub-fibre soundness
nuance is preserved (the per-pole sheet sections are stated against `fibreReg hac (cs i)`, the separation
folded into the re-selection bijection — no false full-fibre germ-equality); and the whole reduction is
non-vacuously satisfiable (`movingSheetSelection_empty`, `∑Res = 0`).
