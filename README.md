# Jacobians Lean API Challenge

Lean 4 formalization of Kevin Buzzard's
[Jacobians API challenge](https://gist.github.com/kbuzzard/778bc714030b3e974ab5f4038783d1a9)
(v0.2), pinned to Mathlib commit
[`8e3c989104daaa052921bf43de9eef0e1ac9fbf5`](https://github.com/leanprover-community/mathlib4/commit/8e3c989104daaa052921bf43de9eef0e1ac9fbf5)
(2026-04-15).

## Layout

- `Jacobians.lean` — the challenge file, verbatim from the gist (all definitions and theorems are `sorry`).
- `docs/DESIGN.md` — the committed long-term construction choices.
- `docs/recon.md` — Mathlib availability audit, one section per `sorry`.
- `docs/REFERENCES.md` — curated textbook/paper sources with per-sorry pointers.

## Build

```
lake exe cache get   # pull Mathlib olean cache
lake build
```

Expect many `declaration uses 'sorry'` warnings and no errors.
