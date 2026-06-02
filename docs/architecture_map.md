# Architecture map — dependency DAG to a sorry-free finish

Canonical dependency map for completing the Jacobians challenge (Buzzard v0.4). Current as of
2026-06-02. Companion to `docs/STATUS.md` (per-theorem `sorryAx` ground truth),
`docs/dolbeault_ladder_derisk.md` (the bimodal RR-wall cost analysis), and
`docs/cech_finiteness_research.md` (the finiteness-node finding that this map incorporates).

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
