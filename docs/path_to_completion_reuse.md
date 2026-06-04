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

## 4. W3 #7 cut-surface · W4 #3 Abel · W1b #1b backward   **[agent pending]**

Deep audit in progress (reuse of flat-Stokes/`CutSurface`, the period lattice, de Rham/`RealForms`, and the
`S²` topology; and the cheapest in-repo route to `SimplyConnectedSpace S²` since we build everything
ourselves). To be merged.

---

## 5. Preliminary reuse-leverage ranking (to be finalized after the agent audits)

1. **W1 finiteness atom** (FunctionDiskAcyclic) — building now; reuse of `primFn`/`cechTerm` post-clash-fix.
2. **W2 Rouché bridge + fibre assembly** — both hard atoms done; highest effort-to-impact remaining.
3. **W1 Serre ladder** — the make-or-break; reuse-vs-Hodge-wall verdict pending §3.
4. **W3 / W4 / W1b** — the independent classical walls; reuse extent pending §4.
