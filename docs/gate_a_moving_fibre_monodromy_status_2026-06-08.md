# Gate A — the moving-fibre self-coherence (§VIII.3 monodromy): status (2026-06-08, session 3)

**Status.**  The genuine §VIII.3 **monodromy heart** of the `CoherentTraceSelection` `Φ`-construction is
**PROVEN axiom-clean** (`[propext, Classical.choice, Quot.sound]`, zero custom axioms, zero `sorry`):
the moving-fibre-vs-fixed-fibre match (the "`Tr_F α` is a single function" content) is built from the
proved fibre-sum bridge + a fully-derived `dz`-Jacobian chart-frame independence + the index-bijection
diagonal identity, and assembled into a reduction of Gate A `∑Res = 0` to a single
`MovingCoherenceFamily` obligation whose remaining fields are the precisely-named residual.

Files (new, both axiom-clean, verified via `lake env lean` `#print axioms`):

* `Jacobians/Dolbeault/FormTraceMovingFibre.lean` — the monodromy heart.
* `Jacobians/Dolbeault/FormTraceCoherentFromMoving.lean` — the assembly `MovingCoherenceFamily ⇒
  CoherentTraceSelection ⇒ ∑Res = 0`, with non-vacuity.

---

## What was proven (axiom-clean)

### `FormTraceMovingFibre.lean` (the monodromy heart)

1. **`chartPullback_section_rinv`** — a manifold section `sec : ℂ → X` of the finite value coordinate
   `f.holoRepr` reads, in the canonical chart at a fibre point, as a continuous **right-inverse** of the
   chart pullback `φ = f.holoRepr ∘ chart.symm` — the `rinv` object the proved bridge consumes.
2. **`fibreTrace_eventuallyEq_movingSum`** — the **fixed-fibre side**: `(fibreTrace ω₀ f D).traceCoeff`
   germ-equals the moving fibre sum read along continuously-varying sheets `sec` through `D`'s fibre
   points (directly from the proved `traceCoeff_eventuallyEq_sum_rightInverse`).
3. **`movingSummand_eq_selfChart`** — the **`dz`-Jacobian cancellation**, derived *purely planar* from
   the proved frame-transition law `localRep_eq_transition_mul_self` + the chain rule (no bundle, no
   compactness on the base `ℂ`): the chart-`xs` moving summand equals the intrinsic self-chart summand
   `g(s b')·localRep(s b')(s b')·deriv(chart_{s b'} ∘ s) b'`.  The cancellation `J·J' = 1` is the
   mutual-inverse chart transitions composing to the identity.
4. **`movingSummand_chartIndep`** — hence the moving summand is **independent of the source chart** (the
   "`Tr_F α` is a well-defined form" content of Miranda §VIII.3).
5. **`traceCoeff_diagonal_eq_fixedSum`** — the **diagonal trace = fixed-chart fibre sum**: the
   re-selected fibre trace `(fibreTrace ω₀ f (Φ b')).traceCoeff b'`, via an index bijection `e :
   (Φ b').ι ≃ D.ι`, the section identification (planar sheet = manifold-section chart-pullback
   derivative), and chart-frame independence, equals the fixed-chart fibre sum.  The genuine
   index-bijection monodromy, per point.
6. **`valueChartTrace_eventuallyEq_fibreTrace_of_sharedSheets`** / **`MovingCoherenceDatum.coherent`** /
   **`.coherent_punctured`** — the assembled **local self-coherence**
   `valueChartTrace ω₀ f Φ =ᶠ (fibreTrace ω₀ f D).traceCoeff` near a base value.
7. **`MovingCoherenceDatum.ofBijection`** / **`diagonal_of_pointwiseBijection`** — build the full datum
   (hence the local self-coherence) from the **continuously-varying index bijection** alone; *all* the
   germ/`dz`-Jacobian content is discharged.
8. **`movingCoherenceDatum_empty`** — non-vacuity (the empty selection's datum, diagonal identity `0=0`).

### `FormTraceCoherentFromMoving.lean` (the assembly)

9. **`glue_fin_of_movingDatum`** / **`hreg_of_movingDatum`** — the finite glue (against the **pole
   sub-fibre** `fibreReg hac (cs i)`, honest separation) and off-exceptional coherence from the per-value
   data.
10. **`MovingCoherenceFamily`** + **`.toCoherentTraceSelection`** + **`residueSum_eq_zero_of_movingCoherenceFamily`**
    — the assembled Gate-A input ⇒ `CoherentTraceSelection` ⇒ Gate A `∑Res = 0` (via the proved
    `residueSum_eq_zero_of_coherentSelection`).
11. **`movingCoherenceFamily_empty`** + **`residueSum_eq_zero_of_movingCoherenceFamily_holomorphic`** —
    end-to-end non-vacuity (the empty-pole case yields `∑Res = 0`).

---

## The minimal remaining obligation (precise)

Gate A `∑Res = 0` is reduced — soundly, axiom-clean — to the **existence of a `MovingCoherenceFamily`**.
Its fields are individually either proved or the precise residual:

### (A) The per-value moving data `Cfin i` / `Creg z` — **reduced to the index bijection**

Via `MovingCoherenceDatum.ofBijection`, each datum needs only the **continuously-varying index
bijection** `hbij`: for `b'` near the base value, `∃ e : (Φ b').ι ≃ D.ι` matching the re-selected fibre
points to the moving sections (`(Φ b').xs i' = sec (e i') b'`) + the section identification + the
chart-pullback/transition differentiability.  *All germ content is discharged* — this is the genuine
monodromy/index-bijection (the branched cover's sheets permute continuously, and at the pole-values the
selection enumerates exactly the **pole sub-fibre** `fibreReg hac (cs i)`, the honest separation).  This
is the remaining geometry: build the global selection `Φ` from a `LocalSheetSystem` of `f.holoRepr` off
the critical set (`exists_holo_localInverse_of_notMem_criticalSet` / `TraceForm.LocalSheetSystem`,
PROVEN), consistent across overlaps, separating poles of `α`.

### (B) The `∞`-fibre reciprocal glue `hglue_inf`

The reciprocal-chart analogue of (A) at `∞` (`recipCoeff (valueChartTrace) =ᶠ[𝓝[≠] 0] (inftyFibreTrace
ω₀ f Dinf).traceCoeff`) — the same monodromy in the reciprocal coordinate `ζ = 1/w`.  Structurally
identical; the same moving-frame argument in the `∞`-fibre (a reciprocal-chart `MovingCoherenceDatum`
analogue is the natural next lemma).

### (C) Junk-freeness `hcont_int`

The remainder `valueChartTrace − L.R` is continuous at each centre — the meromorphic normal form (the
principal part removed).  Concrete.

### (D) Genus-`0` `∞`-vanishing `R₀ 0 = 0`

Dischargeable via the proved engine `coeffAt_eq_zero_of_sphereForm` (`H⁰(ℂℙ¹, Ω) = 0`,
`ProjectiveLine.holomorphicOneForm_eq_zero`) once the reciprocal remainder is packaged as a sphere
`1`-form.  Concrete (independent of (A)/(B)/(C)).

---

## Close-path summary

`residueSum_eq_zero_of_movingCoherenceFamily` (PROVEN) turns the key on Gate A from a single
`MovingCoherenceFamily`.  The **deepest geometric content is now PROVEN axiom-clean** (this session): the
moving-fibre-vs-fixed-fibre match — the fixed-fibre side, the `dz`-Jacobian chart-frame independence (the
"well-defined form" content), and the diagonal index-bijection identity.  The remainder is:

* **(A)** the continuously-varying index bijection `hbij` at each pole/regular value (the global `Φ`
  from a `LocalSheetSystem`, pole/regular separation) — *germ content discharged*, only the bijection
  data remains;
* **(B)** the `∞`-fibre reciprocal glue (structurally identical to (A) at `∞`);
* **(C)** junk-freeness (meromorphic normal form, concrete);
* **(D)** the genus-`0` `∞`-vanishing (`coeffAt_eq_zero_of_sphereForm`, concrete).

No unsound shortcut: every new lemma is axiom-clean with zero custom axioms; the pole-sub-fibre soundness
nuance is preserved (the finite glue is stated against `fibreReg hac (cs i)`, the separation folded into
the index bijection — no false full-fibre germ-equality); and the whole reduction is non-vacuously
satisfiable (the empty-pole witnesses, `∑Res = 0`).
