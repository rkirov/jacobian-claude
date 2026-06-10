# Human steering log (distilled)

This formalization was largely **autonomous** — Claude did the proving across
dozens of sessions (the bulk of the ~57k lines), mostly unattended. This file
records the **human** contribution: the corrections, redirects, and scope calls
the user supplied. It is deliberately terse — the point is to show *how much, and
how,* a human steered an otherwise-autonomous agent, not to re-narrate every
session. The full blow-by-blow (including autonomous per-session progress
reports) is in git history.

**Span:** 2026-04-19 → 2026-06-09. Pattern of involvement: heavy scoping/guardrail
steering up front, then mostly *direction + soundness oversight* while autonomous
sessions did the work. ~30 distinct human redirects across the period.

## Recurring patterns the human had to enforce

The AI's recurring default failure modes, and the corrections that became
standing policy (each is now also a persistent memory):

- **Recommend, don't hedge.** One reasoned recommendation, not a menu of options.
- **Classical / textbook path.** Ground every target in a canonical textbook
  (Forster, Miranda); name the 19th-century method rather than overstating the
  bar as "needs sheaf cohomology"; use standard Mathlib lemmas, not bespoke
  machinery.
- **Honesty over progress-theater.** A typeclass-gated sorry isn't progress;
  "grind" means actually drilling, not reshuffling; honest sorries beat hidden
  axiom-classes.
- **Soundness is non-negotiable.** Never a sorry on a false/unsatisfiable
  statement; no junk/circular structure fields. (Later sessions caught ~12 such
  "bad fields" this way.)
- **Build everything, in-repo.** Done = the full v0.4 challenge, all five walls,
  sorry-free + axiom-clean; zero reliance on anything landing in Mathlib upstream.
- **Connect upstream→downstream.** Build bottom-up wiring already-proven pieces;
  don't isolate fresh downstream kernels.
- **Aim at the risky step.** Prefer the hardest next step that's likely to fail
  (where issues surface) over safe incremental wins.
- **Delegate volume, keep judgment.** Push mechanical volume to clean-context
  agents; never trust an agent's "PROVEN" label — re-verify build + `#print
  axioms` every commit.
- **Descriptive names, no opaque numbering** (S1–S8 / Phase / Priority confused
  the reader); reformat ported/external code as our own — rename and repackage,
  don't preserve foreign structure.
- **House rules.** Commit locally and frequently, push only when asked; don't
  pre-constrain by current Mathlib availability; slow builds are a design smell;
  the curve is over ℂ, not ℝ; pace the math (the user is learning in parallel).

## Chronological — the human's key redirects

| Date | What the human steered |
|------|------------------------|
| 04-19 | Setup: recommend, don't hedge; think long-term but balance generality vs chance of success; ground every target in a textbook; scope non-goals precisely; slow builds are a smell; curve is over ℂ; commit locally / push only when asked; don't overstate the math bar; aim at high-risk steps; mark TODOs rather than silently dropping scope |
| 04-22/23 | Stick to the classical approach (no higher-order refactor); use the Lean MCP for typeclass issues; a typeclass-gated sorry is not progress; reverse the hidden axiom-classes back to honest sorries |
| 05-28 | Verify external claims before trusting; "carefully port what we can use" (Brsanch repo); "don't preserve structure — rename and repackage"; "do it" (commit to the multi-session smoothPath build); "you stop too soon"; flagged + corrected the smoothPath math error |
| 05-29 | Review + Tier-0 cleanup; fix terminology + process overhead; split the de-risking and "connect the ends" |
| 05-30 | Delegate volume to clean-context agents; keep the judgment yourself |
| 05-31 | "Build a self-contained piece"; full-discharge #8 via the port; "finish the core of #7" and parallelize the Abel / Riemann–Roch research |
| 06-01 | Crash recovery; agent-trust failures (non-building code committed as "PROVEN") → always re-verify agent commits |
| 06-02 | "Finish it" — the intrinsic ∂̄ operator (route B); fix the Čech soundness bug via `Filter.Germ`; begin the RR-ladder climb |
| 06-03 | "Prove arithmeticGenus_eq_genus with no sorries / axioms downstream" |
| 06-04 | **Scope correction (verbatim): "done is everything, can't depend on anything landing in mathlib, we have to build it all."** Plus: connect upstream→downstream, don't isolate downstream kernels |
| 06-08 | Continue the finiteness node; critique the attack plan; (took the offered textbook PDFs) |
| 06-09 | "If full RR is needed, prove it — a partial solution is of no interest"; **read the books to find the right path** → narrowed the goal to *just the residue theorem on curves* (closed, axiom-clean); then **clean up for external view** (prune internal docs, delete unused orphans, compact this log) |
| 06-10 | "Finish RR" → closed unconditionally (Miranda tail route + genus-free residue theorem); agents died on spend limits twice → salvage-and-finish-inline pattern; "focus on finishing A" → monodromy theorem built inline, headline #1 (`genus_eq_zero_iff_homeo`) closed; 4 → 2 sorries |

---
*Autonomous sessions — the large majority — are not listed individually; their
per-session reports live in git history.*
