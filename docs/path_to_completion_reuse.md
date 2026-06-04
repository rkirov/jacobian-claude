# Path to completion — the maximal-reuse audit

Living research doc (2026-06-04). Question: *given everything already proven in this repo, what is the
minimal net-new work to close each remaining wall, maximally reusing what exists?* Companion to
`deg_div_research.md`, `cech_finiteness_research.md`, `hodge_bridge_research.md`.

Discipline: grounded (`file:line` + exact names), skeptical (no "reusable" claim without reading the
statement). Sections marked **[agent pending]** are being deep-audited by parallel read-only agents and
will be merged.

---

## 0. The thesis (why the walls are not 5 fresh theorems)

The repo is ~48.7k LoC / 137 files. The five remaining walls do **not** each require a major theorem from
scratch — they are *assemblies + a few focused atoms* on a large, **mostly-proven shared substrate**. The
single most important structural fact, found this audit:

> **`Jacobians/Discharge/Manifold/` is 11.6k LoC across 53 files and is essentially SORRY-FREE** (only two
> `:= sorry` hits, both in comments). It is a complete holomorphic degree/fibre/multiplicity apparatus.

That one directory de-risks W2 (deg_div) and feeds W1b (#1b degree). The other walls sit on similarly-built
substrates (residue calculus, flat-Stokes, the Montel FA spine, the period lattice, the Dolbeault
comparison). The work that remains is concentrated in a handful of *bridges* and *assemblies*, not broad
new theory.

---

## 1. The cross-cutting reusable substrate (what is proven and shared)

| Substrate | Location (key names) | Status | Walls it feeds |
|---|---|---|---|
| **Holomorphic degree / fibre / multiplicity** | `Discharge/Manifold/` (53 files, 11.6k LoC): `degreeFiber_eq_card_of_regularWitness`, `criticalValues_finite_general`, `localMultiplicityOne_preimage_card{,_with_radius,_on_closedBall}`, `localMultiplicity_one_locally_injective`, Hurwitz patching, `FibreCardLocallyConstant…`, `RegularValueExistsReg…` | **sorry-free** | **W2** deg_div, **W1b** #1b |
| **Disk argument principle / k-th root** | `Discharge/Manifold/ArgumentPrincipleDiskProof.lean` (`argumentPrinciple_disk_statement_holds`), `AnalyticKthRoot.lean:126` (`analytic_kth_root_branch_exists_statement`) | **both DONE, axiom-clean** | **W2** |
| **Residue calculus** | `Dolbeault/{Residue,FormCoeff,MittagLeffler,SerreDuality}.lean`: `resAt`, `residueSum`, `Res(holo)=0`, §17.9 litmus `subspaces_inf_ne_bot_of_finrank_add_gt`, `serre_surjectivity_dim_core`, §17.6 witness | sorry-free | **W2** (global Res), **W1** (Serre pairing) |
| **Flat Stokes / box-divergence / circleIntegral** | Mathlib `integral_divergence_*`, `integral_boundary_rect_*`, `circleIntegral.*`; repo `CutSurface.lean`, `rectBoundaryIntegral_handleSum` | proven (Mathlib + repo) | **W3** #7, **W2** arg-principle, **W1** Serre residue |
| **Finiteness FA spine (Montel/Schwartz)** | `Montel/Compactness.lean` (1.1k), `Montel/Complete.lean` (0.9k), `Dolbeault/CechFinitenessWiring.lean`, the `BddHol` Banach + compact-operator atoms | spine proven; manifold instantiation in progress (FunctionDiskAcyclic) | **W1** finiteness |
| **Dolbeault comparison + ∂̄ operators** | `Dolbeault/DolbeaultComparison{,Proof,Inverse,Equiv}.lean` (`cechH1 ≅ H^{0,1}`), `RealForms.lean` (`differential`, `dbar` both sorry-free) | comparison ~closed; `RealForms` sorry-free | **W1** Serre, **W1b** de Rham |
| **RR interface** | `RiemannRoch.lean`: `lDim`, `linearSystem`, faithfulness, `lDim_eq_zero_of_deg_neg`, genus-0 endgame; `DegDivResidue.lean` (deg_div PROVEN from `exists_properMapDegree`) | proven mod the 2 named inputs | **W1**, headline |
| **Period lattice / Jacobian torus** | `PeriodLattice.lean` (1.6k), `ZLatticeQuotient.lean` (0.8k) | substantial | **W3** #7, **W4** #3 Abel |
| **Trace / pushforward** | `TracePullback.lean` (2.6k), `TraceForm.lean` (2.5k) | proven (S8 trace fix) | S8 `pushforward_pullback` |

Reading: a large fraction of the 48.7k LoC is *reusable proven substrate*. The walls draw on overlapping
columns of this table — e.g. flat-Stokes serves three walls; the residue calculus serves W2 and W1.

---

## 2. W2 — `deg_div` / `exists_properMapDegree` (the closest, after finiteness)

**Status: the two irreducible atoms are DONE; what remains is one bridge + one assembly, both reuse-heavy.**

`deg_div` is PROVEN from the single node `exists_properMapDegree` (`DegDivResidue.lean:214`). That node sits
on the sorry-free 11.6k-LoC degree apparatus. The chain, with current status:

1. `argumentPrinciple_disk_statement` (`LocalNormalForm:543`) — **DONE** (`ArgumentPrincipleDiskProof:168`, axiom-clean, this run).
2. `analytic_kth_root_branch_exists_statement` (`LocalKFoldMultiplicity:123`) — **DONE** (`AnalyticKthRoot:126`, in the sorry-free dir).
3. `argumentPrinciple_implies_rouche_statement` (`LocalNormalForm:574`) — **OPEN.** The next atom: argument
   principle + k-th-root + open-mapping ⟹ the Rouché preimage count. The simple-zero (`g − w`) passage the
   `deg_div` recon §5.3 described. Both its inputs are now proven, so this is a focused bridge.
4. `localMultiplicity_eq_localOrder_statement` (`LocalNormalForm:386`) — **OPEN**, follows from (3): local
   degree = order.
5. `exists_properMapDegree` (`DegDivResidue:214`) — the final fibre-count assembly: `zerosCount = polesCount
   = d`, reusing `degreeFiber_eq_card_of_regularWitness` + `criticalValues_finite_general` + (4) for the
   ramified fibres over `0`/`∞`.

**Reuse verdict:** very high. The two hardest pieces (argument principle, k-th-root branch) are proven; the
remainder is the open-mapping Rouché bridge (3)→(4) plus a fibre-count assembly (5) over an essentially-
complete degree library. This is the **single best effort-to-impact wall to finish next** after the
finiteness atom — a few hundred LoC of bridge+assembly, almost entirely wiring proven results. (Caveat from
`deg_div_research.md §6.3`: W2 is needed for *general* RR + Serre's class-level `Res`, not the bare genus
headline — but per the "build everything" scope it is in-scope regardless.)

---

## 3. W1 — Serre / RR (the make-or-break)   **[agent pending]**

Deep audit in progress (the PDE-free Čech-residue route: is it a reuse-assembly over the built comparison +
residue + finiteness + χ machinery, or does it hide a Hodge/elliptic wall at `H^{0,1} ≅ Ω` /
`arithmeticGenus_eq_genus`?). To be merged.

Known reusable inputs: the Dolbeault comparison (`cechH1 ≅ H^{0,1}`), the residue calculus + §17.9 litmus,
the finiteness node (FunctionDiskAcyclic atom building now), χ-additivity (`SkyscraperAssembly`). Known open
sorries: `exists_riemannRoch_divisor` (RR), the three `DolbeaultLadder` sorries (finiteness, `h1Dim 0 =
genus`, `h1Dim D = lDim(K−D)`), `CohomologicalRR:334`, `DolbeaultComparison:227`.

---

## 4. W3 #7 cut-surface · W4 #3 Abel · W1b #1b backward (the independent walls)

### W3 — `exists_cutSurface` (`CutSurfaceRelations.lean:161`) — **MOST reuse-collapsible**
- Consumption (all sorry-free): `exists_cutSurface` → `toCanonicalDissection` → `exists_canonicalDissection`
  → `exists_periodLattice_realBasis` (`PeriodLattice.lean:856`) → the lattice full-rank API. Discharging
  it closes #7 outright. Tighter scaffold: `exists_cutSurface_of_topology` (`CutSurfaceRecon.lean:114`)
  reduces it to `Nonempty (CutSurfaceTopology X)`.
- **Reuse (the whole analytic half is built, axiom-clean):** both Riemann bilinear relations
  `cutSurface_R1`/`_R2` (`CutSurfaceRelations.lean:126,135`) PROVEN from the boundary-word fields;
  `periodVec_linearIndependent` (`Dissection.lean:108`, posDef ⟹ 2g vecs ℝ-indep); the Green/box engine
  (`rectBoundaryIntegral*`, `boundaryForm`, `GreenPositivity`) on Mathlib `DivergenceTheorem` +
  `integral_boundary_rect_eq_zero` + `Convex.exists_forall_hasDerivWithinAt`; the handle aggregation
  `rectBoundaryIntegral_handleSum` (`CutSurfaceRecon.lean:170`).
- **Net-new:** construct the 14 `CutSurfaceTopology` fields — i.e. **surface topology only**: Radó
  triangulability + classification ⟹ symplectic loop basis (`H₁≅ℤ^{2g}`); the holomorphic cut-chart to a
  `4g`-gon; the gluing/monodromy "boundary word" (per-edge identifications + primitive's jump-by-period).
- **Verdict: ~70% of the classical proof already proven; residue is pure topology. ~2–4k LoC, front-loaded
  on topology.** Risk: Mathlib has *no* surface-topology API (no triangulation, no `4g`-gon normal form) —
  the largest greenfield chunk, but conceptually bounded. The "gluing ⟹ boundary word" derivation is the
  correctness crux.

### W4 — `abelJacobi_twoPoint_ne_zero` (`Abel.lean:671`) — **reduction reused, core greenfield**
- Consumed only by `ofCurve_inj` (the #3 theorem), proven modulo this leaf. `AbelRecon.lean` proves the
  whole route EXCEPT Abel's theorem, axiom-clean: `abelJacobi_twoPoint_ne_zero_of_abel` (`:153`) derives the
  target from `AbelStatement X` (`:134`) + the genus-0 fact. So **W4 is pinned to exactly `AbelStatement X`**
  (Abel *sufficiency*: `abelJacobi(P−Q)=0 → ∃ f, HasSingleSimplePole Q`).
- **Reuse:** the full reduction (`AbelRecon`) + `abelJacobi_twoPointDivisor` (`Abel.lean:595`). The trace
  layer powers Abel *necessity* — the half NOT needed here.
- **Net-new = `AbelStatement`**, the HARD half that constructs `f`. No RR-free *and* Hodge-free elementary
  proof exists. Route A (Forster §20): weak divisor solution + **`∂̄`-solvability `H¹(X,𝒪)`** (the Dolbeault
  tower). Route B (G–H): third-kind differential `ω_{PQ}` + reciprocity — gated on **RR** + ∑Res=0;
  reciprocity reuses the `CutSurface`/`boundaryForm` toolkit (shared with W3).
- **Verdict: ~3–6k+ LoC, the deepest of the three; reduction done, core absent.** W3 ⊥ W4 (logically
  independent — the lattice says nothing about whether the open-path period is a lattice point; that
  non-membership IS Abel). **Leverage:** Route B's RR input is exactly what the Dolbeault agents target — RR
  unlocks W4 + the genus-comparison + forward #1 simultaneously.

### W1b — `genus_zero_of_nonempty_homeo_sphere` (`DegreeOneSphere.lean:675`) — **a trap + the de Rham wall**
- The `mpr` of `genus_eq_zero_iff_homeo`. Reuse already built: `RiemannSphere.genus_eq_zero` (`ProjectiveLine.lean:614`,
  via Liouville — the entire `Ω(ℂℙ¹)=0` content, DONE & in scope), `homeoSphere`, and Step-1/Step-5 transport
  in `GenusSphereBackward.lean` (`exists_ne_zero_holomorphicOneForm_of_genus_pos`, `simplyConnectedSpace_of_homeo_sphere`).
- **KEY FINDING — the genus-transport shortcut is BLOCKED.** One wants `X ≃ₜ S² ≃ₜ ℂℙ¹ ⟹ genus X = 0` for
  free; it FAILS because `genus := finrank ℂ HolomorphicOneForms` is **complex-analytic** (transports across a
  *biholomorphism*, not a homeomorphism), and the endgame only ever produces a *topological* `X ≃ₜ S²`. So
  `RiemannSphere.genus_eq_zero` is unreachable for this hypothesis. The honest route is the contrapositive
  `genus ≥ 1 ⟹ X ≄ₜ S²` via de Rham, with two greenfield nodes: **(1) `SimplyConnectedSpace S²`** (absent —
  only a Mathlib `proof_wanted`; we build it) and **(2) closed-not-exact ⟹ ∃ loop `∮_γ ω ≠ 0`** (manifold
  loop-integration + homotopy-invariance — no Mathlib scaffolding; the repo even deleted the local version).
- **Verdict: ~1.5–3k LoC across two absent nodes.** `SimplyConnectedSpace S²` is a clean, self-contained,
  **Dolbeault-independent** sub-target (cheapest *isolated* win; also a `proof_wanted` Mathlib would accept) —
  but alone it does NOT close W1b without the de Rham period slice (the same Hodge/∂̄-flavored gap as W4-A).

---

## 5. Reuse-leverage ranking (W1 Serre verdict still **[agent pending §3]**)

Ordered by effort-to-impact / reuse-collapsibility:

1. **W1 finiteness atom** (`FunctionDiskAcyclic`) — building now; pure reuse of `primFn`/`cechTerm` post-clash-fix.
2. **W2 Rouché bridge + fibre assembly** — both hard atoms (arg-principle, k-th-root) DONE; residue is the
   open-mapping bridge `argumentPrinciple_implies_rouche_statement` + `exists_properMapDegree` assembly over
   the 11.6k sorry-free degree dir. Highest effort-to-impact of the *open* items. ~few hundred LoC.
3. **W3 #7 cut-surface** — most reuse-collapsible *classical* wall: ~70% proven (bilinear relations + matrix
   core + box-Green + handle-sum); residue = pure surface topology (Radó/`4g`-gon), ~2–4k LoC.
4. **`SimplyConnectedSpace S²`** (a W1b sub-node) — clean, self-contained, **Dolbeault-independent**; the
   cheapest *isolated* topology win (also a Mathlib `proof_wanted`). Does NOT alone close W1b.
5. **W1 Serre ladder** — the make-or-break; reuse-vs-Hodge-wall verdict **pending §3**.
6. **W1b de Rham period slice** — manifold loop-integration + homotopy-invariance; no Mathlib scaffolding.
7. **W4 #3 Abel** (`AbelStatement`) — deepest: reduction reused (axiom-clean), but the core is a multi-k-LoC
   greenfield `∂̄`/RR theorem.

### Cross-wall structural insights (the highest-value findings)
- **RR is the single highest-leverage missing theorem.** Building it (the Dolbeault tower the agents target)
  discharges W1, **and** W4 Route B (`AbelStatement` via `ω_{PQ}` + reciprocity), **and** the genus-comparison
  /forward-#1 — three walls at once. It does NOT give W3 (deliberately PDE-free Green-on-polygon) or
  `SimplyConnectedSpace S²` (pure homotopy).
- **The genus-invariance trap (W1b):** `genus` is complex-analytic; the only available equivalence is
  topological — so the "transport from `ℂℙ¹`" shortcut is false-as-applied. Forces the de Rham wall.
- **Three sub-targets are Dolbeault-INDEPENDENT** and can proceed in parallel with the Serre tower: W2's
  Rouché bridge+assembly, W3's surface topology, and `SimplyConnectedSpace S²`. These are the "keep the
  other fronts moving" candidates.
- **The shared Hodge/∂̄ gap:** W4-Route-A and W1b's period slice both bottom out at the *same* manifold-∂̄
  analysis as W1's Serre ladder — so W1's verdict (§3) effectively decides whether that whole family is one
  shared build or three separate walls.
