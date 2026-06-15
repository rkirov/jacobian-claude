# Jacobians Lean API Challenge — solved

[![CI](https://github.com/rkirov/jacobian-claude/actions/workflows/lean.yml/badge.svg)](https://github.com/rkirov/jacobian-claude/actions/workflows/lean.yml)

Lean 4 formalization of Kevin Buzzard's
[Jacobians API challenge](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9)
(**v0.4**), pinned to Mathlib commit
[`8e3c989`](https://github.com/leanprover-community/mathlib4/commit/8e3c989104daaa052921bf43de9eef0e1ac9fbf5)
(2026-04-15). Built from scratch, with **zero reliance on future Mathlib**.

**Status: complete.** The repository is **sorry-free** (zero `sorry` sites, zero custom axioms);
every challenge declaration — `genus`, `genus_eq_zero_iff_homeo`, `Jacobian` with its 7 instances,
`ofCurve` (+ `_self`/`_contMDiff`/`_inj`), `pushforward`/`pullback` with functoriality,
`ContMDiff.degree`, `pushforward_pullback` — is machine-verified with
`#print axioms` = `[propext, Classical.choice, Quot.sound]`.

Conformance is machine-checked in two forms:

- [`ChallengeConformance.lean`](ChallengeConformance.lean) — the verbatim **v0.4 spec**
  ([`Jacobian_challenge.lean`](Jacobian_challenge.lean), byte-identical to the gist): every
  signature restated exactly and discharged by this repo's declarations
  (`lake env lean ChallengeConformance.lean`, exit 0).
- [`ChallengeLeaderboard.lean`](ChallengeLeaderboard.lean) — the
  [lean-eval leaderboard form](https://lean-lang.org/eval/problems/jacobian_challenge_diffgeo/)
  of the same statements (`modelWithCornersSelf` spelling, `[Nonempty X]` binders).

The universe-polymorphic `Jacobian : Type u` is met by `ULift`-ing the concrete `Type 0` torus
([`Jacobians/Surface/ULiftManifold.lean`](Jacobians/Surface/ULiftManifold.lean) — infrastructure Mathlib lacks).

## ⚠ Disclaimer — AI-produced, unreviewed by a mathematician

The human author ([rkirov](https://github.com/rkirov)) does not know the mathematics involved
(algebraic geometry, Riemann surfaces, Serre duality, Abel's theorem) and has **not** reviewed the
content. The code, proofs, and documentation were produced by **Claude** (Anthropic's LLM) across many
sessions with light human scoping/steering. The one hard guarantee is **Lean's kernel**: every
declaration here is `#print axioms`-clean (no `sorryAx`, no custom axioms). Everything else — proof
strategy, prose, mathematical judgment — may be imperfect. Statements were cross-checked against the
cited textbooks throughout, and the two conformance files pin the challenge statements verbatim, but a
subject-expert review is still welcome.

## What was proven (the five walls, and the routes that closed them)

All of the required Riemann-surface theory was built in-repo, following the standard textbook
arguments (Forster GTM 81, Miranda):

| Theorem | Route | Where |
|---|---|---|
| **Riemann–Roch** (`exists_riemannRoch_divisor`, every genus) | Miranda Ch. VI Laurent-tail (adelic) route: tail `H¹`, RR-I, Serre duality `h¹(D) = l(K−D)` in the meromorphic pair frame | `Jacobians/LaurentTail/` |
| **Residue theorem** (`∑ Res = 0`, genus-free) | planar Stokes + annulus residue atoms + partition-of-unity ledger (Forster 10.20/10.21); also the degree route for `deg_div` | `Jacobians/ResidueTheorem/ResidueTheoremStokes.lean` |
| **Genus 0 ⟺ sphere** (`genus_eq_zero_iff_homeo`) | forward: RR ⟹ single simple pole ⟹ degree-1 map; backward: the monodromy theorem via discrete analytic continuation (no integration) | `Jacobians/GenusSphereHeadline.lean`, `Jacobians/Monodromy/` |
| **Abel's theorem** (`abelJacobi_twoPoint_ne_zero` ⟹ `ofCurve_inj`) | Forster 19.10/20.7, dissection-free: weak solutions + the ∂̄-solvability criterion (`h¹(0) = g` + the ∂̄-pairing) | `Jacobians/Abel*.lean`, `Jacobians/H1Genus/CechH1Genus.lean` |
| **Period lattice full rank** (the Jacobian torus structure) | Forster 21.4, dissection-free (the planned 4g-gon cut surface was never needed and was retired) | `Jacobians/PeriodLattice*.lean`, `Jacobians/PeriodLattice/JacobiLocalMap.lean` |

Supporting towers built along the way: Čech cohomology with finiteness (Forster §14) and the
skyscraper χ-machinery (§16), the Čech↔Dolbeault comparison (§15.14), disk ∂̄-solvability (§13),
Montel-space theory for `HolomorphicOneForms`, proper-map degree/conservation-of-number, and the
holomorphic-primitive monodromy toolkit.

📊 See **[`docs/DESIGN.md`](docs/DESIGN.md)** for design choices,
**[`docs/REFERENCES.md`](docs/REFERENCES.md)** for the canonical sources, and
**[`formalization.yaml`](formalization.yaml)** for the
[mathlib-initiative](https://github.com/mathlib-initiative/formalization.yaml) self-reporting
metadata. For authoritative per-theorem status, prefer the tree itself
(`lake build` + `#print axioms`).

## Build & verify

```bash
lake exe cache get                          # pull the Mathlib olean cache
lake build                                  # green, no sorry warnings
./verify.sh                                 # THE authoritative check — runs the real
                                            # leanprover/comparator (statements + permitted
                                            # axioms + kernel replay) against lean-eval's
                                            # exact jacobian_challenge_diffgeo. Expect
                                            # "Your solution is okay!"
lake env lean ChallengeConformance.lean     # human-readable conformance (drives the docs table)
```

`./verify.sh` mirrors lean-eval as closely as possible — same toolchain (`v4.30.0`), same
Mathlib (`c5ea003`), and the verbatim `Challenge.lean` / `Solution.lean` / `config.json` from
lean-eval's `generated/jacobian_challenge_diffgeo/` (see [`comparator/`](comparator/)). A local
pass should therefore mean a green leaderboard run. Verify any individual result with
`#print axioms <decl>` — everything reports `[propext, Classical.choice, Quot.sound]`.

## Leaderboard submission

The `submission` branch is a derived artifact (main + one generated commit) containing the
[lean-eval](https://github.com/leanprover/lean-eval) workspace
`submission/jacobian_challenge_diffgeo/` — `Submission.lean` (the `JacobianChallenge`-namespace
shim) plus the full library re-rooted under `Submission/`. Regenerate with
`scripts/update_submission_branch.sh`; check staleness with
`python3 scripts/make_submission.py --check`.

## Layout

- [`Jacobian_challenge.lean`](Jacobian_challenge.lean) — the verbatim v0.4 spec ·
  [`ChallengeConformance.lean`](ChallengeConformance.lean) /
  [`ChallengeLeaderboard.lean`](ChallengeLeaderboard.lean) — the conformance checks.
- [`Jacobians.lean`](Jacobians.lean) + `Jacobians/` — the implementation: ~72.4k lines across
  251 modules organized into **30 documented units** (one directory per unit, each with an
  umbrella docstring file: `Meromorphic/`, `Forms/`, `Cech/`, `Dbar/`, `Finiteness/`,
  `LaurentTail/` + `TailDuality/` (Riemann–Roch + Serre duality), `Monodromy/`,
  `Abel/`, `PeriodLattice/`, `MappingDegree/`, …). The unit dependency DAG is declared in
  [`docs/unit_dag_manifest.json`](docs/unit_dag_manifest.json) and enforced in CI; browse it
  interactively at [`docs/units.html`](docs/units.html) or read
  [`docs/UNITS_PROPOSAL.md`](docs/UNITS_PROPOSAL.md). (At challenge completion the tree was
  ~111k lines / 309 files; a post-completion consolidation pruned a superseded 30k-line proof
  route and minimized imports.)
- `docs/` — [`DESIGN.md`](docs/DESIGN.md), [`REFERENCES.md`](docs/REFERENCES.md), and the dated
  route-decision plans (`rr_close_plan_2026-06-09.md`, `walls_bc_plan_2026-06-10.md`).
- `scripts/` — `dead_modules.py` (import-graph reachability sweep), `make_submission.py` +
  `update_submission_branch.sh` (leaderboard packaging), `axiom_check_final.lean`.

## Approach

Missing classical content was kept as **honest `sorry`-bodies** (never typeclass-gated axioms)
until proven; each was a single named classical theorem with a Forster/Miranda pointer. Every
commit was required to build and pass `#print axioms` before being trusted — labels were never
believed without kernel verification. Route decisions were made by books-first research passes
(committed under `docs/`) before building; several planned constructions were *retired* when a
cheaper faithful route existed (most notably the 4g-gon cut surface, replaced by Forster's
dissection-free §19–21 analysis).

## Development timeline

Per-day Lean LoC deltas from git history (`git log --numstat`, `*.lean` only); model from the
commit `Co-Authored-By` trailers. 22 working days total, 2026-04-19 → 2026-06-13.

| Day | LoC + | LoC − | Model | Notes |
|---|---:|---:|---|---|
| 2026-04-19 | 1,773 | 675 | Opus 4.7 (1M) | project start |
| 2026-04-20 | 3,581 | 1,395 | Opus 4.7 (1M) | |
| 2026-04-21 | 1,720 | 153 | Opus 4.7 (1M) | |
| 2026-04-22 | 3,970 | 768 | Opus 4.7 (1M) | |
| 2026-04-23 | 153 | 428 | Opus 4.7 (1M) | |
| 2026-05-28 | 17,643 | 817 | Opus 4.7 / 4.7 (1M) | smoothPath build |
| 2026-05-29 | 2,650 | 1,295 | Opus 4.8 (1M) | |
| 2026-05-30 | 4,454 | 5,610 | Opus 4.8 / 4.8 (1M) | |
| 2026-05-31 | 9,704 | 545 | Opus 4.8 / 4.8 (1M) | port: Brsanch degree/fibre (MIT) |
| 2026-06-01 | 4,327 | 835 | Opus 4.8 | |
| 2026-06-02 | 5,192 | 691 | Opus 4.8 / 4.8 (1M) | |
| 2026-06-03 | 4,945 | 480 | Opus 4.8 (1M) | |
| 2026-06-04 | 13,218 | 1,255 | Opus 4.8 (1M) | |
| 2026-06-05 | 1,310 | 52 | Opus 4.8 (1M) | |
| 2026-06-06 | 937 | 141 | GPT-5.5 Codex | |
| 2026-06-07 | 681 | 175 | GPT-5.5 Codex | |
| 2026-06-08 | 21,545 | 2,628 | Opus 4.8 (1M) | port: mrdouglasny ContourDeformation (Apache-2.0; later superseded) |
| 2026-06-09 | 26,360 | 4,847 | Opus 4.8 (1M) → Fable 5 | port: tangentstorm Green rectangle (MIT, Stokes seed); RR route plan |
| 2026-06-10 | 9,914 | 190 | Fable 5 | Riemann–Roch closed; headline #1 closed |
| 2026-06-11 | ~7,000\* | ~6,400\* | Fable 5 | Abel + period lattice closed; dead-module sweep |
| 2026-06-12 | 15,231 | 53,431 | Fable 5 | consolidation: pruned superseded Dolbeault route + unreferenced decls; literate site |
| 2026-06-13 | 18 | 62 | Fable 5 | docs/site + perf polish; maxHeartbeats prune |

\* Raw 06-11 numbers (+118,335/−117,687) include the generated submission workspace being
committed to main and moved to its own branch the same day (±111,303 of churn both ways);
shown is the approximate honest library delta. Days with ports include the ported external
code in the "+" column. "Model" reflects commit trailers; sub-agent-driven days inherit the
trailer of whatever wrote the commit. The 06-06/06-07 commits carry no `Co-Authored-By`
trailer; those days were coded with GPT-5.5 Codex.

### Provenance of the final tree

Of the ~111k Lean lines at challenge completion, **~96.9% (~107,700 LoC)** were produced by this
project's Claude sessions; **~3.1% (~3,450 LoC)** is ported external code — B. Sanchez's
degree/fibre/Hurwitz well-definedness machinery (3,296 lines across 22 surviving files, adapted
and repackaged at port time; now under `MappingDegree/`) and the tangentstorm Green's-theorem
seed (~148 lines of `PlanarStokes/PlanarCompactSupportStokes.lean`). In the current consolidated
tree (~72.4k lines) the same ported material is ~4.8%. The mrdouglasny port (`ContourDeformation`) was superseded by
the in-repo monodromy toolkit and does not survive in the final tree.

## References & acknowledgments

- Forster, *Lectures on Riemann Surfaces* (GTM 81) — primary.
- Miranda, *Algebraic Curves and Riemann Surfaces* (Ch. VI is the Riemann–Roch route);
  Griffiths–Harris, *Principles of Algebraic Geometry*.
- Degree/fibre well-definedness infrastructure ported (MIT) from
  [Brsanch/jacobian-lean-challenge](https://github.com/Brsanch/jacobian-lean-challenge); audited
  axiom-clean.
- The rectangle Green's theorem seeding the planar Stokes atom ported (MIT) from
  [tangentstorm/JacobianChallenge](https://github.com/tangentstorm/JacobianChallenge), whose
  design notes also flagged pitfalls we then avoided.
- [mrdouglasny/jacobian-challenge](https://github.com/mrdouglasny/jacobian-challenge)
  (Apache-2.0): a contour-deformation development was integrated at an intermediate stage (later
  superseded by the monodromy toolkit), and their axiom inventory served as a map of the genuine
  analytic obstacles.
- Challenge by Kevin Buzzard; built on [mathlib4](https://github.com/leanprover-community/mathlib4).
