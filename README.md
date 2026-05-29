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
from Buzzard's spec is defined. **8 `sorry`s remain, 0 custom axioms**
(`#print axioms` shows only the standard `propext, Classical.choice,
Quot.sound`). Each sorry is a named classical theorem not yet in
Mathlib — the mathematically load-bearing pieces.

The code to date is ~24k lines. A rough honest estimate for a
complete, sorry-free solution is several times that, most of the
remaining bulk being upstream Mathlib infrastructure (manifold
Stokes, manifold-level meromorphic functions, divisor theory on
manifolds, manifold degree, Riemann bilinear / Hodge, uniformization).
None of those currently exist in Mathlib.

See `docs/STATUS.md` for the live 8-sorry inventory (S1–S8), the
dependency/leverage map, and per-sorry tiers.

### What is done

- Every type/definition in Buzzard's challenge spec: `genus`,
  `Jacobian`, `periodLattice`, `ofCurve`, `pushforward`, `pullback`,
  `ContMDiff.degree` (the last two as `0` placeholders where
  noted).
- All the main theorems compile with the challenge's intended
  statements.
- Real proof chains for the `pushforward` side (functoriality,
  lattice preservation, smoothness via `ZLatticeQuotient`).
- `ofCurve_inj` (the main challenge theorem) reduces to Abel's
  theorem via a real proof chain — the chain itself is genuine
  (basepoint change, `abelJacobi ↔ ofCurve` bridge, two-point
  divisor algebra).
- Substantial real infrastructure: line integrals on manifolds
  (0 sorries, the single biggest missing Mathlib piece),
  chart-invariance of `meromorphicOrderAt`, Montel's theorem via
  per-chart Arzelà, bundle-trivialization proofs like
  `isClosed_criticalSet`, reverse/concat smoothness preservation
  for smooth paths.

### What is remaining (8 sorries)

Tiered by realistic Lean-completion difficulty:

- **Tractable now (~weeks, bounded Lean engineering):**
  `exists_smoothPath_family` (S1) — the local chart-ball machinery is
  already proven and axiom-clean; only the global path-family
  construction remains. Closing it makes `ofCurve_contMDiff` (the
  Abel–Jacobi map is holomorphic) fully real with no further work.
- **Hard (single self-contained theory builds, ~months each):**
  `exists_preimageCycle_of_nonconstant` (S4, branched-cover lifting),
  `ambientPhi_ambientPsi_eq` (S8, degree identity — also needs a real
  `pushforwardForm`).
- **Research-frontier (Mathlib-contribution scale, no Mathlib support):**
  `deg_div` (S6, residue theorem), `abelJacobi_twoPoint_ne_zero` (S7,
  Abel + Riemann–Hurwitz — the leaf of the main theorem `ofCurve_inj`),
  `DiscreteTopology`/`IsZLattice` for `truePeriodLattice` (S2/S3,
  Riemann bilinear / Hodge — ground the Jacobian-is-a-torus instances),
  `genus_eq_zero_iff_homeo` (S5, uniformization — the most
  theory-deficient).

See `docs/STATUS.md` for the full inventory with locations, the
dependency/leverage map, and Forster/Miranda section references.

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
- `docs/` — design notes, plans, references, status:
  - `STATUS.md` — project status and milestones.
  - `DESIGN.md` — long-term construction choices.
  - `ABEL_JACOBI_PLAN.md` — roadmap for the Abel–Jacobi chain.
  - `MONTEL_PATH.md` — Montel theorem proof path.
  - `REFERENCES.md` — textbook/paper references per sorry.
  - `recon.md` — Mathlib availability audit.

## Build

```bash
lake exe cache get   # pull Mathlib olean cache
lake build
```

Expect 8 `declaration uses 'sorry'` warnings (one per remaining
classical sorry) and no errors.

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
