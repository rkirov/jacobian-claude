# Jacobians Lean API Challenge

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

17 `sorry`s remain, openly declared. Each corresponds to a named
classical theorem not yet in Mathlib (residue theorem on manifolds,
Riemann–Roch, Abel's theorem, Uniformization, branched-cover trace,
the rank-2g period-lattice theorem, etc.). See `docs/STATUS.md` for
the full inventory with Forster/Miranda references.

Real content *was* proven along the way (see "Approach" below); the
sorries are isolated to the genuinely-missing classical pieces.

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

Expect 17 `declaration uses 'sorry'` warnings (one per remaining
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

Real mathematical content proven in this project (selected highlights):
- Chart-invariance of `meromorphicOrderAt` (Forster §6 / Miranda II.4).
- Montel's theorem via Arzelà on per-chart bounded-analytic families.
- Chain rule `pathSpeed_comp_eq_mfderiv` via `IsScalarTower ℝ ℂ ℂ` diamond bypass.
- `lineIntegral_pullback` (change of variables).
- `periodVec_pushforward_of_smooth` (linear algebra + chart pullback).
- `ambientPhi_preserves_truePeriodLattice` (span induction).
- `isClosed_criticalSet` (bundle trivialization + MVT).
- `abelJacobi_twoPointDivisor` (direct sum computation).
- `ofCurve_inj` (THE main challenge theorem, via Abel chain).
- Various concat/reverse smoothness preservation theorems.

## References

- Forster, *Lectures on Riemann Surfaces* (primary).
- Miranda, *Algebraic Curves and Riemann Surfaces*.
- Farkas–Kra, *Riemann Surfaces*.
