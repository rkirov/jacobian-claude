# Path to `FiniteDimensional ℂ (HolomorphicOneForms X)` — Montel approach

## Decision

We pursue the **Montel / compactness** route to prove
`FiniteDimensional ℂ (HolomorphicOneForms X)` for X a compact connected
complex 1-manifold. This is the classical approach used in
Ahlfors–Sario and Rudin.

**Why not Cartan–Serre or Hodge?** Both require elliptic PDE theory on
manifolds, which Mathlib essentially lacks.

**Why not Riemann–Roch?** Would require GAGA (compact Riemann surface ≃
algebraic curve), also not in Mathlib.

**Why Montel?** Mathlib has:
- `MontelSpace` abstraction (bounded closed ⇒ compact).
- `FiniteDimensional.of_isCompact_closedBall₀` (Riesz).
- Maximum modulus on compact complex manifolds.
- `ContMDiffSection` with add/smul structure.

The bulk of the work — *Montel's theorem for holomorphic bundle
sections* — has a concrete proof via Cauchy estimates on charts +
Arzelà–Ascoli; no sheaf cohomology required.

## Outline

1. **Norm on `HolomorphicOneForms X`.** Define
   `‖α‖ := sup_{x ∈ X} ‖α x‖` (well-defined since X compact + α
   continuous as a bundle section).
2. **Banach structure.** `HOF X` with this norm is a normed ℂ-vector
   space; completeness (Banach) follows from uniform limits of
   holomorphic sections being holomorphic.
3. **Cauchy estimates in charts.** For a chart `φ : U → ℂ` and α
   written locally as `f dz` with `f` holomorphic on `φ(U)`, derivatives
   of `f` are bounded by `‖α‖ / dist(z, ∂φ(U))`.
4. **Equicontinuity.** Bounded sets in `HOF X` are equicontinuous (via
   Cauchy estimates + uniform control on a finite atlas).
5. **Arzelà–Ascoli.** Bounded + equicontinuous + compact base ⇒ closed
   unit ball is compact.
6. **Riesz.** Compact closed ball ⇒ finite-dimensional.

## Estimated schedule

Roughly 2–4 months of focused Lean work:

| Step | Weeks | Output |
|------|-------|--------|
| 1–2  | 2–3   | Norm + Banach structure on `ContMDiffSection` |
| 3    | 2–3   | Cauchy estimates on charts; bridge `ContMDiff 𝓘(ℂ) ω` ↔ `AnalyticOn ℂ` |
| 4    | 2–3   | Equicontinuity of bounded holomorphic sections |
| 5–6  | 2–3   | Arzelà–Ascoli for bundle sections + Riesz assembly |

## Why this is also a Mathlib PR

- Norm on `ContMDiffSection` for compact base — general-purpose.
- Montel for holomorphic bundle sections — classical missing lemma.
- Cauchy estimates on complex manifold charts — classical missing
  lemma.
- Riesz-adapted finite-dim conclusion for holomorphic sections —
  foundational.

Each of these pieces is independently useful and should be upstreamed
to Mathlib.

## Reference

Ahlfors, L. and Sario, L. *Riemann Surfaces*, Princeton, 1960 —
Ch. II §5 for Montel. Rudin, *Real and Complex Analysis*, Ch. 14 for
the planar case as a template.
