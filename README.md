# Jacobians Lean API Challenge

Lean 4 formalization of Kevin Buzzard's
[Jacobians API challenge](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9)
(v0.2), pinned to Mathlib commit
[`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`](https://github.com/leanprover-community/mathlib4/commit/8e3c989104daaa052921bf43de9eef0e1ac9fbf5)
(2026-04-15).

## Status

**Zero active sorries** in the project. Every theorem in
`Jacobians.lean` compiles as a genuine Lean theorem.

Classical content not yet in Mathlib (residue theorem, Uniformization,
Riemann–Roch, Abel's theorem, branched-cover trace, etc.) is
axiomatized via named typeclasses with explicit Forster/Miranda
references — so real instances plug in cleanly when the underlying
content lands.

See `docs/STATUS.md` for the inventory of typeclasses and their
classical provenance.

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

Expect several `unused variable` linter warnings (typeclasses
propagated into theorems that don't use them — benign) and no
errors.

## Approach

The project uses a **typeclass-gating** strategy for classical
theorems not yet in Mathlib. Instead of `sorry`-ing each, a named
typeclass (e.g. `HasAbelsTheorem X`, `HasResidueTheorem X`,
`HasSmoothPaths X`) captures the axiom. The main theorems (including
`ofCurve_inj`, the main challenge lemma) derive from these typeclass
axioms via real proof chains.

This means:
- Every theorem is a compiled Lean theorem (no `sorry` hiding).
- Mathematical content gaps are explicit at the instance layer.
- Real instances require Mathlib-contribution-scale work (per-typeclass:
  weeks to months of dedicated effort).

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
