# Recon: mrdouglasny/jacobian-challenge → integration plan (2026-06-08)

Source repo: `/tmp/mrdouglasny-recon` (mrdouglasny/jacobian-challenge).
Target: `/home/rado/jacobian` (our FULLY-sorry-free, ZERO-custom-axiom project).
Read-only on our repo; this doc is the only file written.

## TL;DR

- **License: Apache 2.0** (file `/tmp/mrdouglasny-recon/LICENSE`). Our repo is also Apache 2.0.
  Copying is permitted **with attribution** (keep their per-file copyright header / add a NOTICE
  line). No blocker.
- Their repo is an **assume-and-derive scaffold with 42 live `AX_` axioms**. Their own
  `AXIOM_AUDIT.md` + kernel-checked `docs/axiom-report.txt` are accurate and were used here to
  trace taint. Almost everything substantive bottoms out in an `AX_` and is therefore **NOT
  usable** for us.
- **The "Kirov" vendored subtree (`Jacobians/Vendor/Kirov/`, and the `Bridge/Kirov*` files that
  reference it) is a STALE port of OUR OWN repo** (rkirov/jacobian-claude). It is not new content
  for us; it proves things about *our* old definitions and several Bridge files there are
  axiom-tainted anyway. Skip.
- **The genuinely clean, Mathlib-only, axiom-free, potentially-useful content is small and lives
  in `Jacobians/GeneralResults/` + `Jacobians/Bridge/ContourDeformation.lean`.** These are
  generic complex-analysis lemmas. Net value is modest because we already have most of the
  surrounding machinery, but a few are real micro-wins.
- **Top pick: `Bridge/ContourDeformation.lean`** — chart-local (planar) homotopy-invariance of
  holomorphic 1-form integrals, built directly on Mathlib's `CurveIntegral/Poincare`. This is the
  *exact planar building block* our `HolomorphicPrimitives.lean` flags as the input to its
  isolated `HasHomotopyInvariantPeriods` atom (the #1b de-Rham wall). Confirmed our Mathlib pin
  already ships the Poincaré lemma it uses.

Verdict on the headline ask: **there are 2-4 small clean wins, no large clean win.** The big
files (Bridge line-integral, Serre, period lattice, Abel-Jacobi) are all axiom-tainted and not
portable.

---

## Toolchain / Mathlib compatibility (checked)

| | ours | theirs |
|---|---|---|
| Lean toolchain | `v4.30.0-rc1` | `v4.30.0` |
| Mathlib rev | `8e3c989…` | `c5ea003…` |

Pins differ but are close. **Every Mathlib primitive used by the clean candidate files was
verified present in OUR Mathlib checkout** (`.lake/packages/mathlib`), including the key one:
`Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean` with
`curveIntegral_add_curveIntegral_eq_of_diffContOnCl` (their file's engine). So the ports should
compile against our pin with at most cosmetic fixes.

**Syntax adaptation needed for all ports:** their files use the new Lean module system
(`module` / `public import` / `public section`). Our repo uses classic `import`. Porting = strip
those three wrappers and convert `public import X` → `import X`. Trivial mechanical edit.

---

## Per-candidate assessment

Format: (a) what it proves; (b) axiom status; (c) API match / adaptation; (d) which obligation;
(e) port effort.

### CLEAN candidates (Mathlib-only, transitively axiom-free)

#### 1. `Jacobians/Bridge/ContourDeformation.lean` (172 L)  ★ top pick
- (a) Chart-local path-independence for holomorphic 1-forms in one complex dimension. Defines
  `holoOneForm f z := mul ℝ ℂ (f z)` (the form `f(z) dz` as an `ℝ`-CLM), proves it is closed
  (`holoOneForm_dOmega_symm`: the Fréchet derivative is symmetric, from `f` holomorphic), and
  derives **`contourDeformation1D_pathHomotopy`**: for holomorphic `f` on open `t`, two
  endpoint-homotopic paths whose interior stays in `t` have equal curve integrals
  `∫ᶜ … holoOneForm f`. Built on Mathlib's Poincaré curve-integral homotopy lemma + side-curve
  vanishing lemmas.
- (b) **CLEAN.** Imports only 4 Mathlib modules (`CurveIntegral.Poincare`, `DivergenceTheorem`,
  `Complex.RealDeriv`, `Normed.Operator.Mul`, `FDeriv.Mul`). No `AX_`, no `sorry`. Ported by the
  author from his own `picard-lefschetz` repo. (Should be `#print axioms`-confirmed after the
  port, but the source-level trace is unambiguous.)
- (c) Self-contained — no dependence on any project definition. The only adaptation is the
  module-syntax strip. It uses `HasDerivAt.complexToReal_fderiv` (present, `RealDeriv.lean:95`),
  `curveIntegral_cast`/`curveIntegral_refl` (present), `Homotopy.evalAt` (present in our Poincaré
  module).
- (d) **Obligation #1** (contour deformation) AND directly feeds **#1b** (`HasHomotopyInvariantPeriods`).
  Our `Jacobians/HolomorphicPrimitives.lean` *already imports the same Poincaré module* and
  explicitly says (lines 107-115) that the planar homotopy-invariance "is **absent from Mathlib**:
  only the planar analogue exists, and even that has not been globalised." This file *is* the
  packaged planar analogue (closedness + endpoint-homotopy ⇒ equal integrals) in exactly the
  `holoOneForm`/`∫ᶜ` shape. It does **not** by itself discharge our manifold-level atom (which
  needs the chart-by-chart globalisation onto a simply connected surface), but it is the cleanest
  starting brick for that proof and saves re-deriving the closedness + side-curve-vanishing
  plumbing.
- (e) **Trivial port** (strip module syntax, fix header). **Medium-to-large follow-on work** to
  actually wire it into our `HasHomotopyInvariantPeriods` (the manifold globalisation is the real
  content and is ours to write). Worth porting as a banked lemma regardless.

#### 2. `Jacobians/GeneralResults/EntireGrowth.lean` (116 L)
- (a) `differentiable_eq_polynomial_of_growth`: an entire `g : ℂ → ℂ` with
  `‖g z‖ ≤ C·(1+‖z‖)^n` is a polynomial of `natDegree ≤ n`. Induction on `n`: base = Liouville
  (`exists_const_forall_eq_of_bounded`), step = divide by `dslope g 0` (`sub_smul_dslope`).
- (b) **CLEAN.** `import Mathlib` only; no `AX_`/`sorry`. (The one "axiom" grep hit is the word in
  its docstring.)
- (c) Self-contained; standard Mathlib names all present in our pin
  (`exists_const_forall_eq_of_bounded`, `differentiableOn_dslope`, `sub_smul_dslope`,
  `IsCompact.exists_bound_of_continuousOn`). No project dependency.
- (d) **Obligation #5** (generic analysis) and indirectly the RR/Liouville side. We do **not**
  have this lemma: our `MeromorphicLiouville.lean` is about meromorphic poles/normal-forms, not
  the entire-polynomial-growth statement. It's a clean reusable addition if/when an RR or
  canonical-divisor argument needs "polynomial growth ⇒ polynomial degree".
- (e) **Trivial** (copy file, fix header). Use only if a downstream proof wants it; otherwise a
  cheap bank.

#### 3. `Jacobians/GeneralResults/InverseFunctionTheorem.lean` (97 L)
- (a) `contDiffOn_symm_toOpenPartialHomeomorph`: the inverse branch from
  `ContDiffAt.toOpenPartialHomeomorph` is `ContDiffOn` on its **whole** target (not just
  pointwise), given a global `ContDiff ℂ ω f` hypothesis (the local-only form is false — their
  audit notes this). Built from `ApproximatesLinearOn` + `ContinuousLinearEquiv.ofBijective`.
- (b) **CLEAN.** Imports 3 named Mathlib analysis modules; no `AX_`/`sorry`.
- (c) Self-contained. All primitives present (`ApproximatesLinearOn`, `toOpenPartialHomeomorph`,
  `subsingleton_or_nnnorm_symm_pos`, `approximates_deriv_on_open_nhds`).
- (d) **Obligation #5**, and adjacent to our `ManifoldIFT.lean` (which has `exists_holo_localInverse`
  but **not** this "smooth on the entire target" form). Possible micro-help for our local-normal-form /
  IFT discharge files (`Discharge/Manifold/LocalNormalForm.lean` etc.), but those are deep in
  Hurwitz/degree work we already largely own; low marginal value.
- (e) **Trivial** to port; **uncertain** whether we have a use-site. Bank only if a concrete
  IFT-on-target gap appears.

#### 4. `Jacobians/GeneralResults/OddPartDslope.lean` (49 L)
- (a) `analyticAt_oddPart`, `analyticAt_dslope_oddPart`, `dslope_oddPart_of_ne`: the odd part
  `w ↦ h w − h(−w)` of an analytic function is analytic and vanishes at 0, and its difference
  quotient `dslope` is analytic at 0.
- (b) **CLEAN.** 3 named Mathlib imports; no `AX_`/`sorry`. Uses `p.fslope` /
  `has_fpower_series_dslope_fslope` (present).
- (c) Self-contained.
- (d) Hyperelliptic-specific (branch-point removability). **Not on our priority list** — we are
  not pursuing the hyperelliptic-witness route; our path is the abstract Čech/Dolbeault +
  residue/Serre track. **No obligation match.**
- (e) Trivial port, but **not needed**.

#### 5. `Jacobians/GeneralResults/ChartTransition.lean` (81 L)
- (a) `transition_fderiv_mul`: derivatives of the two mutually-inverse chart transitions on a
  complex 1-manifold multiply to 1 (plus helpers `chart_mdiff`, `chartsymm_mdiff`).
- (b) **CLEAN.** `import Mathlib` only; no `AX_`/`sorry`.
- (c) Generic over `[ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]`.
- (d) Generic chart calculus. **We almost certainly already have equivalents** — our repo has a
  large chart-transition apparatus (`CotangentCoeff.lean`, `analyticAt_chart_change` in
  `Dolbeault/CechH0.lean`, many `Dolbeault/CechModel*`). Overlapping, low marginal value.
- (e) Trivial port; **probably redundant** with our existing chart-change lemmas. Verify against
  `CotangentCoeff.lean` before bothering.

#### 6. `Jacobians/Bridge/BridgePath.lean` (1437 L)
- (a) "A connected complex 1-manifold is smoothly path-connected": flat-endpoint reparametrisation
  (`flatReparam`/`flatSegment`), chart-ball Lebesgue subdivision, smooth concatenation. Exports a
  big toolbox (`complex_chartedSpace_pathConnectedSpace`, `exists_pathChartBallSubdivision`, …).
- (b) **CLEAN at the file level** (Mathlib-only imports, 0 `AX_`, statements reference no project
  names). BUT it exists to feed the **tainted** `Bridge/KirovLineIntegral.lean` line-integral
  construction.
- (c) Self-contained as a library, but large and bridge-path-specific.
- (d) Adjacent to our `Jacobians/SmoothPath.lean` (smooth path concatenation). **Our `SmoothPath`
  has only 1 sorry**, so this is not a high-value rescue. The reusable nuggets (flat reparam /
  segment, smooth-path-connectedness) are small and mostly already covered by us or Mathlib.
- (e) **Large** to vet/port wholesale for tiny marginal value. **Not recommended** unless our 1
  `SmoothPath` sorry turns out to be exactly the flat-junction glue this file does.

### Vendored-Wallace files (MIT, *different provenance* — tangentstorm, not mrdouglasny)

These live under `Jacobians/Vendor/Wallace/` and are **MIT-licensed work by Michal J Wallace
(tangentstorm)**, merely re-vendored by mrdouglasny. They are Mathlib-only and axiom-free. We do
**not** currently vendor Wallace. Flagged separately because the license/attribution is MIT and the
provenance is a third repo we have a separate memory note on.

- `Vendor/Wallace/Periods/CurveIntegralSubpath.lean` (210 L): `curveIntegral_subpath_of_le`
  (restricting a curve integral to a subpath via affine reparam). CLEAN. Touches **#1/#7**
  (line-integral algebra). Possible micro-help for our cut-surface/period integral algebra.
- `Vendor/Wallace/HolomorphicForms/VanishingOrder.lean` (571 L),
  `…/AnalyticLocalMapping.lean` (268 L), `…/CotangentBundle.lean` (135 L): meromorphic order /
  analytic local mapping / cotangent bundle lemmas. CLEAN. Overlap heavily with our existing
  order/normal-form machinery; **per our existing memory note, nothing from tangentstorm was
  cleanly portable beyond what we already did** — re-confirm before investing.
- **These are an MIT opportunity independent of mrdouglasny; if pursued, go to the upstream
  tangentstorm repo directly and vendor under our `vendor/` with the MIT LICENSE.**

---

## NOT usable (axiom-tainted or sorry-bearing) — with reasons

| File / theorem | Reason |
|---|---|
| `Bridge/KirovLineIntegral.lean` (1063 L) | References `AX_pathIntegral_local_antiderivative` (3×) — which their OWN README/AXIOM_AUDIT says was **deleted as FALSE/unsound** (single-valued ℂ "FTC" forces zero periods on genus≥1). Also imports our stale `RiemannSurface.OneForm` + `BridgePath` + `KirovHolomorphic`. The spec's "16 axiom refs" is stale; current is the *unsound* one. **Hard reject.** |
| `Bridge/KirovHolomorphic.lean` (631 L), `Bridge/KirovHolomorphicEquiv.lean` | Depend on `AX_FiniteDimOneForms` (Montel finite-dimensionality bridge) + our stale `RiemannSurface.OneForm`/`Vendor.Kirov`. The FiniteDim-of-1-forms result is OUR own work anyway (we have `Montel/`). Tainted; redundant. |
| `Bridge/BridgePathArc.lean`, `Bridge/KirovCanonicalEq.lean` | Import `KirovLineIntegral` / project `RiemannSurface.{ArcAlgebra,CanonicalArcIntegral}`. Transitively tainted + about stale defs. |
| `Extensions/AbelJacobi.lean` (#4 Abel) | Bottoms out in `AX_AbelTheorem`, `AX_PeriodLattice`, `AX_RiemannBilinear`, `AX_AnalyticCycleBasis`, `AX_pathIntegral_local_antiderivative` + **5 sorries**. The entire Abel content is assumed. **Hard reject** for obligation #4. |
| `Extensions/Hyperelliptic.lean` (6 sorries), `Extensions/HyperellipticEven.lean` | Sorry-bearing + hyperelliptic-witness route we don't pursue. |
| `Axioms/SerreDuality.lean` (`AX_SerreDuality`), `Axioms/RiemannRoch.lean` (`AX_RiemannRoch`), `Axioms/RiemannBilinear.lean`, `Axioms/PeriodLattice.lean`, `Axioms/AnalyticCycleBasis.lean`, `Axioms/PluckerFormula.lean`, `Axioms/AbelTheorem.lean`, all of `Axioms/*` | **These ARE the axioms.** Obligations #2 (Serre §17), #3 (Abel), #7 (period lattice) are *assumed* here, not proved. The `RiemannSurface/Cohomology/{RiemannRochAPI,SerreDualityAPI}.lean` files are vetted *statements* with 8 deferred sorries on top of these axioms — no proof content. **Nothing portable for #2/#3/#7.** |
| `Vendor/Kirov/*` (Montel, LineIntegral, ZLatticeQuotient, …) | A port of OUR OWN older repo. Axiom-free but it's our past work about our old API; not new content. |
| `RiemannSurface/RiemannRochSpace.lean` etc. | Their `L(D)` over the meromorphic germ quotient + `h0_zero` (h⁰(0)=1) is axiom-free — but **we already have `h0Dim_eq_lDim` proven axiom-clean** and the full Čech 𝒪_D representation; theirs is a different (simpler, less complete) construction with no advantage for us. |

### The χ-side `LocallyRealizable` / local Mittag-Leffler (obligation #6)
- **Not present** in their repo in any usable form. They route everything through `AX_RiemannRoch`
  / `AX_SerreDuality`, so there is no local-Mittag-Leffler / `LocallyRealizable` content to port.

---

## PRIORITIZED integration list (clean + needed + low-effort first)

1. **`Bridge/ContourDeformation.lean` → bank as `Jacobians/<…>/ContourDeformation.lean`.**
   Trivial port (strip module syntax + Apache attribution to M. R. Douglas). Highest relevance:
   the planar holomorphic homotopy-invariance brick that our `HolomorphicPrimitives.lean`
   explicitly wants for the `#1b` `HasHomotopyInvariantPeriods` atom. After porting, the
   substantive (non-trivial, *ours-to-write*) step is the chart-by-chart globalisation onto a
   simply connected surface — but this brick removes the planar plumbing from that task.
   **Action: `#print axioms contourDeformation1D_pathHomotopy` after porting to confirm
   `[propext, Classical.choice, Quot.sound]` before relying on it.**

2. **`GeneralResults/EntireGrowth.lean` (`differentiable_eq_polynomial_of_growth`) → bank.**
   Trivial port, clean, and a lemma we genuinely lack. Pull in when an RR / canonical-divisor /
   degree argument needs "entire + polynomial growth ⇒ polynomial of bounded degree."

3. **`GeneralResults/InverseFunctionTheorem.lean` (`contDiffOn_symm_toOpenPartialHomeomorph`) →
   bank if a use-site appears.** Trivial port; complements our `ManifoldIFT.exists_holo_localInverse`
   with the "smooth on whole target" form. Only adopt if a `Discharge/Manifold/LocalNormalForm`-style
   gap actually needs it.

(2) and (3) are cheap insurance; (1) is the one with a concrete, already-identified consumer.

**Explicitly skip:** `ChartTransition.lean` (redundant with our chart-change lemmas — verify vs
`CotangentCoeff.lean`), `OddPartDslope.lean` (hyperelliptic route we don't take), `BridgePath.lean`
(huge, ~no marginal value vs our `SmoothPath`), and everything in the NOT-usable table.

**Separate MIT track (optional):** the Wallace `CurveIntegralSubpath` / order lemmas are clean MIT;
if a period/cut-surface line-integral algebra gap appears, source them from upstream tangentstorm —
but our existing memory note says prior tangentstorm recon found nothing cleanly portable beyond
what we already did, so confirm a concrete need first.

---

## License verdict

**Apache 2.0** (`/tmp/mrdouglasny-recon/LICENSE`), identical to our repo's license. Copying their
Lean files into our repo is permitted. Requirement: **retain attribution** — keep the file's
`Copyright (c) 2026 Michael R. Douglas … Apache 2.0` header (and per Apache §4, preserve notices).
ContourDeformation additionally notes it was ported from the author's `picard-lefschetz` repo. The
Wallace files are **MIT** (© Michal J Wallace, tangentstorm) — also copy-compatible with attribution
if pursued. No GPL/viral-license blocker anywhere.

## How any port should be axiom-verified (discipline)

For each ported declaration, after it compiles in our tree, run
`#print axioms <fully.qualified.name>` and require the output to be exactly
`[propext, Classical.choice, Quot.sound]`. Do this *before* any of our headline theorems are made
to depend on it. The source-level traces above are unambiguous (Mathlib-only imports, no `AX_`,
no `sorry`), so the risk is low — but the kernel check is the gate that prevents injecting a hidden
axiom into our zero-axiom project.
