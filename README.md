# Jacobians Lean API Challenge

[![CI](https://github.com/rkirov/jacobian-claude/actions/workflows/lean.yml/badge.svg)](https://github.com/rkirov/jacobian-claude/actions/workflows/lean.yml)

Lean 4 formalization of Kevin Buzzard's
[Jacobians API challenge](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9)
(v0.2), pinned to Mathlib commit
[`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`](https://github.com/leanprover-community/mathlib4/commit/8e3c989104daaa052921bf43de9eef0e1ac9fbf5)
(2026-04-15).

## Disclaimer

The human author (rkirov) does not know the mathematics involved
(algebraic geometry, Riemann surfaces, Abel's theorem, etc.) and has
not reviewed the content of this repository. Code, proofs, and
documentation were produced by Claude (Anthropic's LLM) across
several sessions with light human scoping/steering
(see `human_input.md`). Expect errors in math, proof strategy, and
documentation — anything flagged as a "real proof" here should be
independently checked by someone who actually knows the subject
before being relied on.

## Status

**Not done, but further than the headline suggests.** The challenge
file compiles clean (`lake build`, exit 0) and every main signature
from Buzzard's spec is defined, with **0 custom axioms** (`#print
axioms` shows only the standard `propext, Classical.choice,
Quot.sound`). The remaining gaps are named classical theorems not yet
in Mathlib — the mathematically load-bearing pieces. (The build shows
more than one `sorry` warning per goal where a goal is decomposed into
named sub-lemmas.)

The code to date is ~24k lines. A complete, sorry-free solution is
several times that, most of the remaining bulk being upstream Mathlib
infrastructure (manifold Stokes, manifold-level meromorphic functions,
divisor theory on manifolds, Riemann bilinear / Hodge, uniformization)
that does not currently exist in Mathlib.

### What is done

- Every type/definition in Buzzard's spec: `genus`, `Jacobian`,
  `periodLattice`, `ofCurve`, `pushforward`, `pullback`,
  `ContMDiff.degree` (a real fibre-cardinality degree).
- All main theorems compile with the challenge's intended statements.
- **Smooth-path family / Abel–Jacobi holomorphicity** — fully proven,
  axiom-clean (the chart-ball cover + junction-concat keystone).
- **Pushforward/pullback functoriality + lattice preservation** via
  `ZLatticeQuotient`. The `pushforward ∘ pullback = degree`
  *misformalization* (pullback was the transpose, not the genuine
  pushforward) is now fixed: `pullback` is the genuine trace transpose
  and `pushforward_pullback` is a *true* statement.
- **Manifold inverse function theorem** for complex 1-manifolds
  (`exists_holo_localInverse`) and **local holomorphic sections** at
  non-critical points — reusable infrastructure; the off-branch
  **trace (pushforward) of forms** is built on them.
- `ofCurve_inj` reduces to Abel's theorem via a genuine proof chain.
- Line integrals on manifolds (0 sorries — the single biggest missing
  Mathlib piece), chart-invariance of `meromorphicOrderAt`, Montel's
  theorem, the off-branch covering map, fibre finiteness.

### What is remaining

The open classical theorems, named by what they are:

- **Period lattice is discrete** and **is full-rank (a ℤ-lattice)** —
  ground the Jacobian-as-complex-torus instances (Riemann bilinear /
  Hodge; no Mathlib support).
- **Branched-cover loop lifting** — homotope a loop off the branch
  locus (manifold Stokes) and lift it to the preimage cycle. The
  covering, fibre finiteness, manifold IFT, local sections, and the
  off-branch trace are built; the loop homotopy + cycle assembly remain.
- **Pushforward ∘ pullback = degree** — remaining: the trace map's
  branch-point extension + projection formula, then the degree identity
  off the lattice (via full-rank).
- **Degree counts zeros and poles** — off the critical path.
- **Abel–Jacobi non-vanishing** — Abel + Riemann–Hurwitz; the leaf of
  the main injectivity theorem `ofCurve_inj`.
- **Genus zero ⟺ sphere** — uniformization; the most theory-deficient.

The live status is tracked in the agent memory; `docs/REFERENCES.md`
has per-topic textbook pointers and `docs/S8_TRACE_PLAN.md` records the
trace-map design.

## Layout

- `Jacobians.lean` — the challenge file (main theorems + signatures).
- `Jacobians/` — supporting infrastructure:
  - `Abel.lean` — divisors, Abel–Jacobi map, meromorphic functions, Abel's theorem.
  - `PeriodLattice.lean` — period vector, closed loops, Abel-Jacobi map (ofCurve), line integral machinery.
  - `HolomorphicForms.lean` — pullback/pushforward of forms, ambient Φ/Ψ bridges.
  - `LineIntegral.lean` — line integral, pathSpeed, chain rule, concat/reverse.
  - `Genus.lean` — genus = dim HOF X.
  - `Montel/` — Montel's theorem (compactness of holomorphic 1-forms under supNormK).
  - `ZLatticeQuotient.lean` — quotient of ℂ^g by a ℤ-lattice as a complex manifold.
- `docs/` — design notes and references:
  - `DESIGN.md` — long-term construction choices.
  - `REFERENCES.md` — textbook/paper references per topic.
  - `S8_TRACE_PLAN.md` — the trace-map (pushforward of forms) design.
  - `EXTERNAL_AUDIT.md` — audit of the ported discharge infrastructure.

## Build

```bash
lake exe cache get   # pull Mathlib olean cache
lake build
```

Expect a number of `declaration uses 'sorry'` warnings (the open
classical theorems above, plus their named sub-lemmas) and no errors.

## Approach

An earlier draft used a typeclass-gating strategy (`HasAbelsTheorem`,
`HasResidueTheorem`, etc.) to move the missing classical content to
the instance layer. This was reverted: typeclass-gated axioms are
content-equivalent to `sorry` but ambiguous (a reader may not notice
the claim is unproved). All gated theorems are now honest
`sorry`-bodies so the unproved surface is visible in Lean's warnings.

Real content *was* proven along the way and is preserved. Everything
else is a `sorry` with a named classical theorem attached, pointing
to a Forster/Miranda section.

Selected proven content (not just stated — real Lean proofs):
- Chart-invariance of `meromorphicOrderAt` (Forster §6 / Miranda II.4).
- Montel's theorem via Arzelà on per-chart bounded-analytic families.
- Chain rule `pathSpeed_comp_eq_mfderiv` via `IsScalarTower ℝ ℂ ℂ` diamond bypass.
- `lineIntegral_pullback` (change of variables).
- `periodVec_pushforward_of_smooth` (linear algebra + chart pullback).
- `ambientPhi_preserves_truePeriodLattice` (span induction).
- `isClosed_criticalSet` (bundle trivialization + MVT).
- `abelJacobi_twoPointDivisor` (direct sum computation).
- `ofCurve_inj` — the main challenge theorem, proof chain is real
  (relies on sorry-d Abel + Riemann–Hurwitz axioms at the leaves).
- Various concat/reverse smoothness preservation theorems.

## References

- Forster, *Lectures on Riemann Surfaces* (primary).
- Miranda, *Algebraic Curves and Riemann Surfaces*.
- Farkas–Kra, *Riemann Surfaces*.
