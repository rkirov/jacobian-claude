# Project retrospective (2026-06-11)

A short retro on formalizing the Jacobians challenge — 20 working days, ~111k lines, sorry-free.
Written by the agent (Claude) from its project memory; same disclaimer as the README.

## Hardest

- **Serre duality / Riemann–Roch route churn.** The Čech–§17 residue-pairing program was attempted,
  partially built, audited (several statements found false-as-stated: skyscraper middle terms,
  free-`K` ladder leaves, an unsound `αBr` field), re-pointed twice, and finally bypassed entirely
  by Miranda's Laurent-tail route. Most of the eventually-deleted dead code came from here.
- **Statements, not proofs.** The recurring failure mode was *misformalization* — statements
  subtly stronger than the book's (junk values, missing connectedness, fixed-cover obstructions).
  Catching these cost audits; proving the corrected statements was comparatively routine.
- **Lean-specific friction at the manifold layer:** the `restrictScalars ℝ/ℂ` instance diamond,
  `Module ℝ (Fin g → ℂ)` defeq-vs-syntactic clashes, tangent-bundle trivialization plumbing —
  each cost real sessions and produced reusable workaround patterns.

## Easier than expected

- **The final analysis.** Once routes were settled, the "hard" walls fell fast: the monodromy
  theorem in one inline day (discrete continuation, no integration), Abel + the period lattice in
  ~two days of agent relays. The planar integration atoms were well-scaffolded by Mathlib.
- **Retiring work instead of doing it.** The 4g-gon cut surface — long expected to be the worst
  wall (surface classification, absent from Mathlib) — was never built: a books pass showed its
  lone consumer provable dissection-free (Forster 21.4).

## What worked

- **Kernel verification as the only trust anchor.** `lake build` + `#print axioms` per commit,
  never trusting labels — this caught non-building "PROVEN" commits, hidden-axiom drafts, and
  orphan modules early, and made agent output safely composable.
- **Books-first research passes** (committed as dated plan docs) before each major build:
  decisive route choices with page-level citations, honest LoC/risk estimates, and pre-listed
  fallbacks for the riskiest item. Both endgame plans survived contact with reality.
- **Honest `sorry`s, isolated and named** (never typeclass-gated axioms): the unproved surface
  stayed visible, auditable, and steadily shrinking (5 → 4 → 3 → 2 → 0).
- **Parallel agents in git worktrees** with frozen interfaces between lanes, and the
  **salvage-relay** pattern when agents died mid-run (~6 spend-limit deaths): verify drafts, fix
  the 1–3 residual errors, commit, relaunch with a continuation brief. No work was ever lost.

## Where the human steered

- **Scope and standards:** "done is everything, built in-repo, zero future-Mathlib reliance";
  "fully sorry-free — a partial solution is of no interest"; reverting an early
  axioms-as-typeclasses draft to honest sorries.
- **Process redirects at the right moments:** "read the books to find the right path" (which
  produced the route that bypassed the biggest wall), "verify every agent commit", "connect
  upstream→downstream", budget/timing calls during the spend-limit relay, and ops nits
  (tail-able build logs, dead-module cleanup, submission packaging shape).
- **Not the mathematics:** content decisions were made against the textbooks, not by the human —
  which made the kernel-and-books discipline load-bearing.

## What I'd do differently

- **Books-first from day one.** The route-research discipline only crystallized in the final
  week; applied earlier it would have avoided most of the Čech–§17 dead end (~15–20% of all
  written code was eventually superseded or deleted).
- **Keep trunk modules thin.** Edits to low-level files (`PeriodLattice`, `Abel`) invalidated
  hundred-module rebuild cones on a 4-core/8GB box; a stricter interface/implementation split
  would have kept iteration fast.
- **Plan for agent mortality.** The incremental-commit discipline was adopted reactively; making
  small, verified, self-describing commits the unit of work from the start (plus shared build
  caches across worktrees) would have made the relays cheaper.
- **Automate the audits sooner.** The dead-module sweep, axiom audit script, and conformance
  files all paid for themselves immediately; they should exist from week one, not the last day.
