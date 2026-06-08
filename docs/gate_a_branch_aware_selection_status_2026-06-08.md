# Gate A — constructing a real `BranchAwareTraceSelection`: status (2026-06-08)

**Task.**  Construct ONE `BranchAwareTraceSelection` for an adapted cover, closing Gate A
(`∑ Res(α) = 0`, `α = ω₀·g`) **unconditionally** (modulo separate `AdaptedCover` existence).  Plan:
Miranda §VIII.3, residual = pieces (i) canonical fibre, (ii) off-branch regularity, (iii) branch-value
continuity, (iv) ∞/junk/genus-0.

**Headline.**  The session **closed pieces (i)+(ii)** into reusable axiom-clean engines and **pinned down
piece (iii) precisely** — and in doing so found that (iii) is *not* "standard analysis with a quick
finish": there is a **genuine structural obstruction** in `BranchAwareTraceSelection` as currently
stated, which means it **cannot be instantiated for any real (ramified) cover** without a change to how
the branch-value trace value is carried.  The good news: the deepest *analytic* content of (iii) — the
§VIII.3 boundedness — is **already proven axiom-clean elsewhere in the repo** (`Jacobians/TraceForm.lean`,
`traceExtendsAt_branchPoint`), so the correct close-path is a *bridge*, not new analysis.

Gate A `∑Res=0` is therefore **NOT yet unconditional**; the minimal remaining obligation is sharpened and
re-pointed (below).

---

## What was built this session (axiom-clean `[propext, Classical.choice, Quot.sound]`)

New files, both verified via authoritative `lake env lean` `#print axioms`, zero custom axioms, zero
`sorry`:

1. `Jacobians/Dolbeault/FormTraceRegularValueDatum.lean` —
   `MovingCoherenceDatum.ofSphereSheetSystemCanon`: the **regular-value coherence engine** (pieces
   (i)+(ii)).  Chains `MovingCoherenceDatum.ofSphereSheetSystemSet` + `canon_of_fibre_enumeration` so the
   per-regular-value `Creg` datum's *only* `Φ`-content is the canonical-fibre condition (`(Φ b').xs`
   injectively enumerates the full fibre `F⁻¹(coe b')` near `b₀`), with the off-branch regularity reduced
   to `hderiv`/`hmero` at the sphere-sheet fibre points.  Set-equality of the moving fibre and the sheet
   values is reconstructed *inside* (both ranges equal the fibre) — no labeling.

2. `Jacobians/Dolbeault/FormTraceBranchContinuity.lean` —
   `continuousAt_valueChartTrace_of_tendsto` (+ `…_self`): reduces the `hbranch` field to its two genuine
   sub-obligations: **(1)** the punctured limit `L` exists (`Tendsto (valueChartTrace …) (𝓝[≠] z) (𝓝 L)`)
   and **(2)** the value-matching `valueChartTrace … z = L`.  Records the structural subtlety driving the
   obstruction below.

---

## The structural obstruction in `BranchAwareTraceSelection` (the honest finding)

`valueChartTrace ω₀ f Φ z := (fibreTrace ω₀ f (Φ z)).traceCoeff z` is, at **every** value `z`,
the **finite fibre-sum** `∑ᵢ (chartIntegrand ω₀ g (Φ z).xs i)(sheetᵢ z)·sheetᵢ'(z)` over the fibre data
`Φ z`, whose sheets are **unramified** holomorphic sections (`FibreRegularData.hg_deriv ≠ 0`).

The field `hbranch : ∀ z ∈ br, z ∉ centres → ContinuousAt (valueChartTrace ω₀ f Φ) z` therefore requires
the value **at** the branch value `z` (computed through `Φ z`) to equal the punctured limit `L =
lim_{w→z} Tr_F α(w)`.  But:

* `br` = the **branch values of the cover** `F = f.toRiemannSphere`; by definition each contains a
  **ramified** fibre point (a critical point of `f`).
* `Φ z` is a `FibreRegularData g f z`, so it may only enumerate **unramified** points
  (`hg_deriv ≠ 0`) with `f.holoRepr (xs i) = z` — i.e. points **of the fibre over `z`**.
* The ramified fibre points contribute a **nonzero, finite** amount to the limit `L` (the
  `wᵉ`-normal-form `z^{-(e-1)/e}` blow-ups of the `e` colliding sheets *cancel* by roots-of-unity
  orthogonality, leaving a finite nonzero residue contribution).  A `Φ z` built from the *unramified*
  preimages gives only a **partial** sum, missing that contribution.

**⟹ For any cover with ramification at a branch-value off the pole-values (essentially every real
cover), no `FibreRegularData g f z` has `traceCoeff z = L`, so `hbranch` is FALSE for the canonical-fibre
`Φ`.**  Adding "virtual" sheets is impossible: `hval` forces fibre membership.  Hence
`BranchAwareTraceSelection` is **not instantiable for a real ramified cover** as currently stated.

This corrects the prior plan's framing of (iii) as "standard §VIII.3 analysis, the deepest residual":
the analysis is real *and* the `valueChartTrace`-via-`Φ` representation structurally cannot host the
branch-value extension value.

---

## The deepest analytic content of (iii) is ALREADY PROVEN (the unlock)

`Jacobians/TraceForm.lean` contains the **genuine §VIII.3 branch extension**, built on the *correct*
object `traceFunExt f α` (the removable-singularity extension of the fibre-sum trace `traceFun f α`),
**proven axiom-clean**:

* `traceLocalCoeff_mul_sub_tendsto_zero` / `…_Y` — the **boundedness crux** (the local coefficient of the
  trace has at worst a removable singularity at a branch point) — PROVEN (uniform fibre-cardinality bound
  `fibre_ncard_bddAbove_near_branch` + per-summand `traceSummand_localCoeff_mul_sub_tendsto` + finite
  subcover).  *This is exactly sub-obligation (1) of `hbranch`, formalised.*
* `traceExtendsAt_branchPoint`, `exists_traceForm`, `traceForm` — the global holomorphic extension across
  the finite branch locus — PROVEN.

These are stated for **holomorphic** forms `α : HolomorphicOneForms Y`.  `α = ω₀·g` is **meromorphic**
(`g` has poles), but the boundedness lemmas are **local and fibre-point-by-fibre-point**, so they apply
verbatim near any branch value that is **not** a pole-value of `ω₀·g` (where `ω₀·g` is holomorphic on a
neighbourhood of the fibre).

---

## The minimal remaining obligation (precise + re-pointed)

Gate A `∑Res=0` is reduced — axiom-clean, no labeling, with (i)+(ii) engined — to **discharging the
branch-value behaviour soundly**.  Two equivalent close-paths, both *bridges over already-proven
analysis*, not new analysis:

* **Close-path A (preferred — decouple `T` from `Φ`).**  `residueSum_eq_zero_of_glue` (and
  `residueSum_eq_zero_of_geometricSelection`) take `T : ℂ → ℂ` as an **arbitrary function** — it need not
  be `valueChartTrace ω₀ f Φ`.  Feed it the **removable-extension trace** `T` (the value-chart local
  coefficient of the extended fibre-sum trace of `α = ω₀·g`), which is **analytic everywhere off the
  pole-values** (so `hT_off` is free, *including* at branch values — no `hbranch` needed), and germ-equals
  the fibre traces off the pole-values (so `hglue_fin`/`hglue_inf` hold).  Obligation: **build the
  extended `T` for the meromorphic `ω₀·g`** by porting the `TraceForm` boundedness/extension
  (`traceLocalCoeff_mul_sub_tendsto_zero_Y` technique) to the `valueChartTrace`/`chartIntegrand`
  apparatus, and prove the off-pole germ-equality `T =ᶠ fibreTrace.traceCoeff`.  This **sidesteps the
  structural obstruction entirely** (no `BranchAwareTraceSelection`).

* **Close-path B (repair the structure).**  Re-state `BranchAwareTraceSelection.hbranch` /
  `valueChartTrace` so the branch-value value is the **extension limit** (e.g. carry `Φ` only off `br` and
  define the trace at branch values as the removable limit), then discharge it via
  `continuousAt_valueChartTrace_of_tendsto` (built this session) + the ported boundedness.

Either way the **only genuinely-new work** is porting the *proven* `TraceForm` branch-boundedness to the
meromorphic `ω₀·g` value-chart trace — the §VIII.3 boundedness, of the same character as
`traceLocalCoeff_mul_sub_tendsto_zero_Y` (already axiom-clean for the holomorphic case).  Estimated a
focused build (the technique and the uniform-cardinality / finite-subcover scaffolding are reusable).

**Pieces (i)+(ii) are done** (`ofSphereSheetSystemCanon`).  Piece (iv) (∞/junk/genus-0) is the concrete
reciprocal-chart + `coeffAt_eq_zero_of_sphereForm` data, unchanged and independent of the obstruction.

---

## Soundness

No custom axiom, no `sorry` on a false statement.  Both new files re-grepped `^axiom ` (empty) and
verified `[propext, Classical.choice, Quot.sound]` via authoritative `lake env lean` `#print axioms`.
The `BranchAwareTraceSelection` empty-pole non-vacuity remains valid (no branch values ⟹ `hbranch`
vacuous).  The obstruction above is reported, **not papered over with a false `hbranch`** — the structure
is left untouched, and the sound close-paths are documented.  Full targeted builds green.
