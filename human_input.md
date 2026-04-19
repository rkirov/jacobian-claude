# Human steering log

Log of the user's corrections, redirects, and clarifications during this
project. The goal is to notice patterns: what keeps going wrong by default,
and what the user has to remind me of repeatedly.

Format: most-recent last. Each entry names the moment, what I was about to
do (or had just done), what the user steered, and what changed.

---

## 2026-04-19 — Session 1 (setup + recon + first theory)

### Ask for a concrete recommendation, don't hedge

**When:** during plan-mode Q&A.
**My default:** Offered three options (period lattice / Pic⁰ / sheaf
cohomology) and asked the user to pick.
**User steer:** "which path do you recommend, we need to pick it early
and carefully."
**Change:** Committed to **period lattice** as the canonical definition,
with reasoning. Stopped presenting non-committal option lists.

### Think long-term Mathlib, don't pre-constrain by current availability

**When:** while choosing `Jacobian` construction.
**My default:** Argued for period lattice partly on "Mathlib doesn't have
sheaf cohomology for analytic spaces" grounds.
**User steer:** "don't limit yourself on what is in or not in mathlib, but
think what is the most natural long term way to define these in mathlib
(we will build what is needed)."
**Change:** Reframed the recommendation around the most natural Mathlib
definition (still period-lattice in basis-free form), acknowledging we'd
build missing theory.

### But also: balance generality against chance of success

**When:** after the previous steer.
**My default:** Swung toward Albanese-for-compact-Kähler as the "most
general" long-term definition.
**User steer:** "hmm, balance chance of success with generality, maybe
just curves is ok for now."
**Change:** Pulled back to curve-only for `Jacobian` / `periodLattice` /
`ofCurve` / `pushforward`; kept cheap generalizations (holomorphic
1-forms on complex manifolds, topological `genus` on closed oriented
2-manifolds, `degree` on equidim complex manifolds); flagged Albanese
etc. as explicit future work. Recorded the tradeoff in `DESIGN.md` so the
scoping is visible.

### Ground every target in a canonical textbook

**When:** while writing the plan.
**My default:** Referenced textbooks casually from memory.
**User steer:** "plan to have a canonical paper reference source to go
back to if stuck, research to find best sources."
**Change:** Web-researched references, committed to Forster + Miranda
primary pair, produced `docs/REFERENCES.md` with per-sorry
chapter/section pointers. Saved the discipline as a memory so I apply it
going forward.

### Scope non-goals precisely, don't blur sessions and project

**When:** plan doc near end.
**My default:** Wrote "Building substantial new Mathlib theory" as a
non-goal.
**User steer:** "…is listed as a non-goal, but the goal is to prove
substantial mathlib if needed."
**Change:** Split into project-level goals (which include building new
Mathlib theory) vs. Session-1-only non-goals (cataloguing, not building).

### Slow builds are a design smell, not a tolerable cost

**When:** after first `Jacobians/ZLatticeQuotient.lean` build took ~4 min
with `import Mathlib`.
**My default:** Kept the broad import and didn't worry about build time.
**User steer:** "/btw be mindful of slow build times, they are sign of
poor definitions and theorems."
**Change:** Swapped `import Mathlib` for three targeted imports.
Elaboration dropped from ~4 min to 7.4 s. Also dropped a concrete example
whose typeclass search was timing out (its own design smell). Committed
the discipline as a memory.

### The challenge is over ℂ, not ℝ — don't shortcut

**When:** while writing `Jacobians/JacobianValidate.lean`.
**My default:** Hit an instance-search failure on
`FiniteDimensional ℝ (Fin g → ℂ)` and pivoted to validate on
`Fin g → ℝ` "to prove the architecture."
**User steer:** "Are you sure, isn't the goal surfaces over c."
**Change:** Found `FiniteDimensional.complexToReal` in
`Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean`, which does the
bridge automatically. Rewrote the validation against `Fin g → ℂ`, the
real target. All five structural instances now fire on the correct
ambient space.

### Commit cadence & pushing

**When:** mid-session.
**My default:** Was about to push to a remote after being asked to
commit.
**User steer:** "i will push just make sure to commmit" — then later
"It's ok work locally for now make sure to commit at reasonable steps."
**Change:** Work stays local; commit at every reasonable step
(skeleton → proof → refactor → validation). No pushes unless asked.
Saved as a memory.

### Don't overstate what's hard; the classical path exists

**When:** after I claimed the content sorries need "sheaf cohomology".
**My default:** cast the math bar unrealistically high ("Cartan–Serre
sheaf cohomology").
**User steer:** "isn't there a different approach — these results were
known in the early 1900s".
**Change:** corrected the characterization — the classical proofs are
complex-analysis + topology + stokes (not sheaf cohomology). Identified
*line integrals on manifolds* as the single biggest missing Mathlib
piece for the classical path. Built `Jacobians/LineIntegral.lean`
(0 sorries). Used it and placeholder-content closures to take the
challenge file from 12 → 6 sorries in one push.

### Continue on high-risk to uncover issues — don't just go deeper on easy wins

**When:** after committing the architecture de-risk (commit `1b429c8`)
and asking what's next.
**My default:** Was leaning toward safe incremental work (more skeleton
files).
**User steer:** "continue on parts that feel highest risk to uncover
more issues"
**Change:** Attempted the highest-risk non-content wire-up: routing
`Jacobians.pushforward` through `Architecture.pushforward +
Bridge.ambientPhi`. Uncovered a concrete design finding (commit
`4e50ddc`): our non-reducible `Jacobian X` makes proof-time elaboration
awkward when using abstract `Architecture` theorems. Documented the
tradeoff (reducibility vs. build time vs. `abbrev`) and deferred the
call. The attempt surfaced a real architectural decision to track, even
though no sorries closed.

### Don't silently drop universe polymorphism; try briefly, mark TODO

**When:** after the prototype committed with `Type 0` instead of the
challenge's `Type u`, and I asked what to do next.
**My default:** Was about to either abandon the universe issue quietly
or dive into a multi-hour `ULift` + `ChartedSpace`-transfer project.
**User steer:** "Try 1) briefly but otherwise settle for proving without
universe polymorphism (especially if it needs changes in Mathlib) leave
as todo explicitly."
**Change:** Briefly checked — `ChartedSpace`-over-`ULift` doesn't exist
in Mathlib and would be a separate contribution. Dropped to `Type`,
noted the gap as an explicit TODO in both the Jacobian docstring and
this log, and moved on. Closed 3 net sorries in `Jacobians.lean`.

---

## Patterns to watch

- **Hedging with option lists.** When I offer 3 options and ask the user
  to pick, I should usually just recommend one with reasoning.
- **Pre-constraining by Mathlib availability.** Natural math first; what
  Mathlib has is a second-order concern for this project.
- **Over-generalizing when told to think long-term.** "Long-term" does
  not mean "maximally general." Success bias still applies.
- **Tolerating slow builds.** ~4 min for a tiny file is a design smell,
  not a cost of doing business.
- **Shortcutting when an instance fails.** Before falling back to a
  simpler type, hunt for the bridge lemma.
- **Publishing / pushing without being asked.** Default to local commit;
  publish only on explicit request.
- **Silently abandoning scope.** When I can't get something to work the
  way the spec asked, mark it as an explicit TODO in the code and the
  steering log rather than just dropping it.
- **Preferring "low-risk progress" over useful risk-taking.** User has
  repeatedly pushed me to take on the hardest / riskiest next step. My
  default is incremental safe work; their steering says aim at what's
  likely to fail, because that's where issues surface.
- **Overstating the math bar.** I'm prone to calling things out as
  "needs sheaf cohomology" or similarly advanced when the classical
  elementary path exists. Classical results had classical proofs —
  if something was done in the 19th century, name the 19th-century
  method, not the 20th-century reformulation. User catches this.
