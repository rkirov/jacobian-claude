# Gate A — §VIII.3 monodromy via the symmetric-invariance lever: status (2026-06-08)

**Status.**  The prior round's flagged obstruction — "no global continuous sheet-labeling" for the
moving-fibre re-selection — is **dissolved**.  Gate A's 1-form residue theorem
`∑_{a ∈ poles} Res_a(α) = 0` (`α = ω₀·g`) is now reduced — **axiom-clean**
(`[propext, Classical.choice, Quot.sound]`, zero custom axioms, zero `sorry`), **non-vacuously** — to
the genuine §VIII.3 geometry **with no sheet-labeling content**, and with branch values handled by
Riemann's removable singularity.

New files (all axiom-clean, verified via authoritative `lake env lean` `#print axioms`):

1. `Jacobians/Dolbeault/FormTraceMovingFibreSymm.lean` — the symmetric lever core.
2. `Jacobians/Dolbeault/FormTraceMovingFibreSetSelection.lean` — the set-form Gate-A reduction.
3. `Jacobians/Dolbeault/FormTraceMovingFibreSphereSet.lean` — set-form re-selection from sphere sheets.
4. `Jacobians/Dolbeault/FormTraceBranchExtension.lean` — holomorphic extension across branch values.
5. `Jacobians/Dolbeault/FormTraceBranchAwareSelection.lean` — the capstone reduction.

---

## The lever (the architectural unlock)

`valueChartTrace ω₀ f Φ b' = (fibreTrace ω₀ f (Φ b')).traceCoeff b'` is a **symmetric sum over the
sheets** of the fibre `Φ b'`, so it depends only on `Φ b'` *as a set*, not on any sheet labeling.

**Key finding.**  The existing `MovingSheetSelection.hsel` (`∀ᶠ b', ∃ e : (Φ b').ι ≃ D.ι, …`) was
*already* quantified **pointwise per `b'`** — there was **never** a global-continuity requirement.  The
prior round's obstruction was illusory.  The only residual was to *produce* the per-`b'` bijection,
which **exists automatically** whenever the moving fibre `Φ b'` and the section values enumerate the
*same finite set* (both injective with equal range) — `Equiv.ofInjective` on each side.

---

## What was proven this session (axiom-clean)

### (1) The symmetric lever core — `FormTraceMovingFibreSymm.lean`
* `equivOfInjective_image_eq` — two injective enumerations `p q` of the same set
  (`Set.range p = Set.range q`) are matched by a bijection `e` with `p i = q (e i)`.  *No continuity.*
* `MovingCoherenceDatum.ofSheetSectionsSet` — `MovingCoherenceDatum.ofSheetSections` with the
  re-selection in **set form** (moving fibre = section values as a set, both injective).  The per-`b'`
  bijection is reconstructed pointwise by the lever; the caller supplies **no labeling**.

### (2) The set-form Gate-A reduction — `FormTraceMovingFibreSetSelection.lean`
* `MovingSheetSelectionSet` — the whole Gate-A input with `hselFin`/`hselReg` replaced by the set-form
  `hsetFin`/`hsetReg`.
* `residueSum_eq_zero_of_movingSheetSelectionSet` — Gate A `∑Res = 0` from it (wired through
  `MovingCoherenceFamily ⇒ ∑Res=0`).
* `movingSheetSelectionSet_empty` + `…_holomorphic` — end-to-end non-vacuity.

### (3) Set-form re-selection from sphere sheets — `FormTraceMovingFibreSphereSet.lean`
* `sheetValues_range_eq_fibre` — the sphere sheet values over `b'` enumerate the full fibre
  `F⁻¹(coe b')` (`LocalSheetSystem.fibre_eq`).
* `MovingCoherenceDatum.ofSphereSheetSystemSet` — the moving datum from a sphere sheet system with the
  *canonical-fibre* re-selection (the moving fibre enumerates the sphere fibre as a set), **no labeling**.
* `canon_of_fibre_enumeration` — the set-equality reduces to "`Φ b'` is the fibre as a set" (the two
  ranges agree because both equal the fibre).

### (4) Branch-value extension (the genuine residual) — `FormTraceBranchExtension.lean`
At a branch value there is **no sheet system**.  The trace extends across it by **Riemann's removable
singularity** (`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`):
* `analyticAt_valueChartTrace_of_punctured_continuous` — analytic on a punctured nhd + continuous at the
  point ⟹ analytic at the point.
* `analyticAt_valueChartTrace_off_centres` — the full `hT_off`: regular values via the moving-sheet
  coherence, branch values `z ∈ br` via the extension (a punctured ball around `z` avoids the finite
  `centres ∪ br`).  **The only branch-specific input is continuity, never a sheet system.**

### (5) The capstone — `FormTraceBranchAwareSelection.lean`
* `BranchAwareTraceSelection` — the Gate-A input bundling: the per-pole/per-regular moving-sheet
  coherence data (no labeling), the regular-value `g`-analyticity, the finite branch values `br` + their
  **continuity** `hbranch`, and the `∞`-glue / junk-freeness / genus-`0` data.
* `residueSum_eq_zero_of_branchAwareSelection` — Gate A `∑Res = 0` via `residueSum_eq_zero_of_glue` (the
  low-level descent whose off-centre requirement is *analyticity*, exactly what the branch extension
  supplies — `CoherentTraceSelection` would instead demand germ-coherence at branch values, false there).
* `branchAwareTraceSelection_empty` + `…_holomorphic` — end-to-end non-vacuity.

Conclusion type confirmed `= ∑ a ∈ poles, formFnResidue ω₀ g a = 0` (Gate A's target).

---

## The minimal remaining obligation (precise + diagnosed)

Gate A `∑Res = 0` is reduced — axiom-clean, no labeling — to **the existence of one
`BranchAwareTraceSelection` for a real adapted cover**.  Its fields are individually either proved
infrastructure or one of these residuals, **none of which is the monodromy-labeling obstruction** (that
is gone):

* **(i) The global canonical `Φ`** — a `Φ : (b : ℂ) → FibreRegularData g f b` enumerating the fibre at
  each value.  Close-path: the fibre-as-a-set is intrinsic; the per-value coherence data `Cfin`/`Creg`
  are built from `MovingCoherenceDatum.ofSphereSheetSystemSet` (axiom-clean) with the canonical-fibre
  re-selection `canon_of_fibre_enumeration`, whose `Φ`-content is purely "`Φ b'` *is* the fibre".
* **(ii) Regular-value regularity** (`hderiv`/`hmero` for the sphere sheet fibres, `hCreg_g`
  `g`-analyticity) — from the local biholomorphism off the critical set (`exists_holo_localInverse`,
  `criticalValues_finite_general`).
* **(iii) Branch-value continuity** `hbranch` — the genuine §VIII.3 analytic content: the symmetric
  trace is bounded/single-valued across the branch point, hence continuous (Riemann extension input).
  This is the **only** branch-specific obligation and is *not* a sheet/labeling fact.
* **(iv) `∞`-glue, junk-freeness, genus-`0` `∞`-vanishing** — the reciprocal-chart analogue (B,
  structurally identical), the meromorphic-normal-form continuity (C, concrete), and
  `coeffAt_eq_zero_of_sphereForm` (D, `H⁰(ℂℙ¹,Ω)=0`, concrete).

**The monodromy-LABELING obstruction is removed.**  The residual is the canonical-fibre construction +
the off-branch regularity + the branch-value continuity (Riemann extension) + the concrete `∞`/junk/
genus-`0` data — all standard §VIII.3 / Riemann-surface content, none requiring a global sheet-labeling.

---

## Soundness

No custom axiom, no `sorry`.  Every new declaration verified `[propext, Classical.choice, Quot.sound]`
via authoritative `lake env lean` `#print axioms` (not LSP).  The pole-sub-fibre nuance is preserved
(`hCfin_D : (Cfin i).D = fibreReg hac (cs i)`).  All five reductions are non-vacuously satisfiable
(empty-pole witnesses yielding `∑Res = 0`).  Full glob build green (3513 jobs).
