# Architecture map — dependency DAG to a sorry-free finish

Canonical dependency map for completing the Jacobians challenge (Buzzard v0.4). Current as of
2026-06-02 (DAG) + 2026-06-03 delta (below). Companion to `docs/STATUS.md` (per-theorem `sorryAx`
ground truth), `docs/dolbeault_ladder_derisk.md` (the bimodal RR-wall cost analysis), and
`docs/cech_finiteness_research.md` (the finiteness-node finding that this map incorporates).

## 2026-06-03 delta — three nodes advanced (re-color before reading the DAG below)

- **`🔴 Dolbeault comparison` → ✅ DONE (sorry-free).** The `finrank ℝ DolbeaultH01 = 2·h1Dim 0` node
  (incl. all 5 former sub-kernels + RT2/`toGerm_holoFn`) is axiom-clean. Only the `cechH1_dolbeault_
  comparison` L3 *wiring* leaf (Leray cover-independence) remains, and it has no consumers. **NOTE:**
  this node was over-weighted as the RR critical path — it gives `cechH1 ≅ H^{0,1}`, the *first* iso;
  `arithmeticGenus_eq_genus` still needs the *second* (`H^{0,1}≅Ω(X)` = Serre/§17), so the comparison
  being done does NOT by itself move `arithmeticGenus_eq_genus`.
- **`🔴 arithmeticGenus_eq_genus` (Serre §17) — local calculus now ✅, global assembly still 🔴.** The
  PDE-free §17 route's LOCAL residue calculus is fully sorry-free (`Residue.lean`/`SerreDuality.lean`/
  `FormCoeff.lean`: `resAt` + API, both abstract duality cores incl. the §17.9 litmus, the §17.6
  residue-1 witness). Remaining 🔴 = the *global* `Res : H¹(X,Ω)→ℂ` (needs `∑Res=0`=`deg_div`) + the
  pairing assembly. See `docs/hodge_bridge_research.md`.
- **`🟡 finiteDimensional_cechH1` ⟸ `exists_cechModel` — K-bridge layer now ✅.** The germ↔`BddHol`
  comparison primitives are built sorry-free (`CechModelBridge.lean`/`CechModelManifold.lean`). Next
  blocker = non-convex restriction-compactness (cross-chart overlaps aren't convex); step 1 done, step 2
  in progress. See `docs/cech_finiteness_research.md`.

```
LEGEND:  ✅ done/axiom-clean   🔧 in progress   🟢 templated/reuse (low risk)
         🟡 bounded-new (medium)   🔴 greenfield (high risk)


╔════════════════════════════ CHALLENGE DELIVERABLES ════════════════════════════╗
   genus_eq_zero_iff_homeo        ofCurve_inj      ofCurve/pullback_contMDiff,
        (the headline)                                pushforward_pullback
        │            │              │   │                    │
   ┌────┘            └────┐    ┌────┘   └────┐               │
   ▼ (forward)    (backward)▼  ▼             ▼               ▼
┌──────────┐      ┌────────┐ ┌────┐    ┌─────────┐    ┌─────────────┐
│ RR + Res │      │ #1b    │ │ #3 │    │ #7      │    │ #7 (lattice │
│          │      │ Hodge  │ │Abel│    │cut-chart│    │ → manifold) │
└────┬─────┘      └───┬────┘ └─┬──┘    └────┬────┘    └──────┬──────┘
     │                │        │            │                │
     │   ┌────────────┴────────┴────────────┴────────────────┘
     │   │   all of #1b / #7 / (Abel's deepest input) bottom out in the
     │   │   SAME analytic core as RR  ⇒  one shared investment
     ▼   ▼
╔════════════════ RIEMANN–ROCH  (exists_riemannRoch_divisor) ════════════════╗
║  ⟸ riemannRoch_equality_of_ladder ✅ (PROVEN — composes the 4 leaves)       ║
║                                                                            ║
║   l(D) − l(K−D) = deg D + 1 − g                                            ║
║      │            │              │                                         ║
║      ▼            ▼              ▼                                         ║
║ ┌─────────┐  ┌─────────┐  ┌──────────────┐  ┌──────────────────────────┐  ║
║ │h0Dim_eq_│  │ cohomo- │  │ serre_h1_eq  │  │ arithmeticGenus_eq_genus │  ║
║ │  lDim   │  │ logical_│  │ (general     │  │   (Serre @ D=0: h¹(𝒪)=g) │  ║
║ │(bridge) │  │   RR    │  │  Serre)      │  │                          │  ║
║ │  🔧     │  │ (χ-add) │  │   🔴          │  │           🔴             │  ║
║ └────┬────┘  └────┬────┘  └──────┬───────┘  └────────────┬─────────────┘  ║
╚══════╪════════════╪══════════════╪═══════════════════════╪════════════════╝
       │            │              │                       │
       │            ▼              └──────────┬────────────┘
       │     ┌──────────────┐                 ▼
       │     │finiteDimensio│        ┌──────────────────────────┐
       │     │ nal_cechH1   │◀───────│  SERRE / DOLBEAULT CORE   │  🔴 greenfield
       │     │ (Forster14.9)│        │  H¹(𝒪) ≅ H^{0,1} ≅ Ω(X)*  │  (the irreducible
       │     │     🟡        │        │  + residue-pairing        │   nugget)
       │     └──────┬───────┘        └────────┬─────────────────┘
       │            │                         │
       ▼            ▼                         ▼
┌──────────────────────────────┐   ┌──────────────────────────────┐
│  FINITENESS TREE — DE-RISKED  │   │   SERRE TREE — GREENFIELD     │
│  (mostly REUSE)               │   │                              │
│  ✅ nested triple cover        │   │  🔧 G2 ∂̄-globalize (PoU+G1)  │
│  ✅ disk-Montel (Compactness)  │   │  ✅ intrinsic ∂̄ operator dbar │
│  ✅ supNorm+bcf+Riesz pattern  │   │  🔴 Dolbeault comparison      │
│  ✅ G1 ∂̄-disk (Leray vanish)   │   │     (Čech H¹ ≅ H^{0,1})       │
│  🟡 Schwartz finite-codim lem  │   │  🟡 residue pairing           │
│  🟢 germ↔supNorm comparison    │   │     (CutSurface/Green: ✅ int │
│                               │   │      side; 🔴 perfectness)    │
└───────────────────────────────┘   └──────────────────────────────┘

       ┌───────────────────────────────────────────────────────────┐
       │  Res / deg_div  (∑Res=0, manifold Stokes)   🔴  — its own   │
       │  build, shares the Stokes family with the residue pairing   │
       └───────────────────────────────────────────────────────────┘
```

## The finding this map incorporates (vs. the earlier "one Dolbeault root" map)

1. **The Dolbeault root splits.** It is *not* one root. **G1 (∂̄-disk, ✅ done)** feeds only the
   *finiteness* tree (via the Leray vanishing `H¹(disk,𝒪)=0`); **G2 (∂̄-globalize) + the intrinsic ∂̄
   operator `dbar`** feed only the *Serre* tree. The two were conflated before.

2. **G2 is OFF the finiteness critical path.** Finiteness uses only disk-level G1, not globalized ∂̄.
   So G2 is deferred to the Serre node — it does not block the χ-additivity half of RR.

3. **`finiteDimensional_cechH1` dropped 🔴 → 🟡.** Its sub-tree is mostly ✅ *reuse*: the nested triple
   cover (`Montel/Cover.lean`), disk-Montel (`Montel/Compactness.lean`), and the supNorm+bcf+Riesz
   endgame (`FiniteDimensional.of_isCompact_closedBall₀`) already exist for Ω(X). Only the Schwartz
   finite-codim lemma (🟡 bounded) and the germ↔supNorm comparison (🟢 cheap) are new.

4. **The genuine 🔴 greenfield is isolated to one box:** the **Serre/Dolbeault core**
   (`H¹(𝒪)≅H^{0,1}≅Ω(X)*`), plus `deg_div`. Everything else on the RR ladder is done, in progress, or
   de-risked reuse.

## Critical path to the headline (`genus 0 → S²`)

```
h0Dim_eq_lDim 🔧  +  finiteDimensional_cechH1 🟡  →  cohomological_riemannRoch
        +  arithmeticGenus_eq_genus 🔴 (D=0 Serre)  +  deg_div 🔴
        →  l(P)=2  →  single simple pole ✅  →  deg-1 map  →  ℂℙ¹≃S² ✅
```

The headline needs **`arithmeticGenus_eq_genus` (Serre at `D=0`) but NOT `serre_h1_eq` (general
Serre)** — so the single 🔴 Serre box can be attacked in its smallest form first (the de-risk's
scoping win). `serre_h1_eq` is needed only for the all-`D` RR statement and for #3 (Abel).

## Status of the leaves / nodes

| Node | File | Status |
|---|---|---|
| `riemannRoch_equality_of_ladder` | DolbeaultLadder.lean | ✅ composes the leaves |
| `h0Dim_eq_lDim` (bridge) | CechH0.lean | 🔧 keystone+forward+ker+assembly ✅; gluing/surjectivity in progress |
| `finiteDimensional_cechH1` | DolbeaultLadder.lean | 🟡 templated (see `cech_finiteness_research.md`) |
| `cohomological_riemannRoch` (χ-add) | DolbeaultLadder.lean | 🟡 homological once finiteness lands |
| `arithmeticGenus_eq_genus` (D=0 Serre) | DolbeaultLadder.lean | 🔴 Dolbeault nugget |
| `serre_h1_eq` (general Serre) | DolbeaultLadder.lean | 🔴 residue-pairing perfectness |
| `deg_div` (residue thm) | RiemannRoch.lean | 🔴 manifold Stokes |
| `genus_zero_of_nonempty_homeo_sphere` (#1b) | DegreeOneSphere.lean | 🔴 Hodge (g = ½·b₁) |
| `exists_cutSurface` (#7) | CutSurfaceRelations.lean | 🔴 surface classification / Hodge reuse |
| `abelJacobi_twoPoint_ne_zero` (#3) | Abel.lean | 🔴 Abel (⟸ RR + reciprocity) |

Foundations already done (axiom-clean): G1 ∂̄-disk (`DbarDisk`), intrinsic ∂̄ operator
(`RealForms.dbar`), nested cover + disk-Montel (`Montel/*`), ℂℙ¹ shim + `≃ₜ S²` (`ProjectiveLine`),
single-simple-pole extraction from `l(P)=2` (`RiemannRoch`/`MeromorphicLiouville`), #7 analytic core
(`periodVec_linearIndependent`, R1/R2).

---

## 2026-06-02 autonomous run — the RR wall is now a map of named honest kernels

The Dolbeault→Serre→RR foundation was built top-to-bottom this session; the entire connective tissue
(skeletons, bookkeeping, the homological crank, the comparison spine) is **PROVEN axiom-clean**, and
the irreducible analysis is isolated to a handful of **named, honest, single-statement `sorry`s** (each
a TRUE classical theorem). Repo builds green throughout. New files (all green): `DbarLocal`,
`DbarDiskCohomology` (full-disk ∂̄, no Mittag-Leffler), `DolbeaultH01` (`dbarL`), `DolbeaultComparison`
(`H^{0,1}` constructed), `DolbeaultComparisonProof` (comparison spine + chart bridge proven),
`CohomologicalRR` (χ-additivity crank), `DegDivResidue` (residue skeleton), + the finiteness stack.

**The named kernels (= the entire remaining analytic content of RR):**
| Kernel (`sorry`) | File | What it is | feeds |
|---|---|---|---|
| `exists_cechModel` | CechFinitenessWiring | Forster-14.9 chart-disk Leray model + comparison | finiteness |
| `exists_skyscraperLES` | CohomologicalRR | skyscraper SES connecting map + `skyDim=1` + snake | χ-additivity |
| `exists_properMapDegree` | DegDivResidue | `#zeros=deg=#poles` (Rouché + ramified count + general `X→ℂℙ¹`) | `deg_div` |
| `exists_chartPullback_zeroOne_datum` + 4 | DolbeaultComparisonProof | (0,1)-form chart-pullback datum: smoothness + mfderiv↔planar-`deriv` bookkeeping; + maps well-defined/inverse | Dolbeault comparison (L3) |

**Kernel attack (latest):** the **Wirtinger chain rule** `dbarDisk_comp_holo` — `∂̄(f∘τ) = conj(τ′)·(∂̄f∘τ)`
for holomorphic `τ` (the genuine analytic content of the Dolbeault comparison's local solvability) — is
**PROVEN axiom-clean**. `exists_localPrimitive_apply_one` is reduced to the finer residue
`exists_chartPullback_zeroOne_datum` and reformulated with `+hg` (the `(0,1)` hypothesis the sole caller
already has) so the `conj(τ′)` frame factor **cancels** on both sides. Verified (`#print axioms`: only
`sorryAx` via the one finer kernel). Residue = tangent-bundle/smoothness bookkeeping (~100-200 LoC), not
new analysis.
| `arithmeticGenus_eq_genus`, `serre_h1_eq` | DolbeaultLadder | Serre at `D=0` / general (need comparison + `H^{0,1}≅Ω(X)`) | RR |

**Glue done:** `cohomological_riemannRoch` wired into the ladder (→ `exists_skyscraperLES`); `h0Dim_eq_lDim`
proven (→ `cechRestrictL_surjective`). **2 soundness bugs caught & fixed** (`leray_surjective` /
`cechH1_linearEquiv_supH1` were vacuously-false free `∀`-statements; concentrated into `exists_cechModel`).
**Worst-feared elliptic/Weyl kernel stayed OFF the table** (Čech-residue route). What remains is exactly
these named kernels — research-grade analysis, but each a single isolated honest statement, not open design.
