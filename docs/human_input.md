# Steering log (human input / corrections / redirects)

Append-only. Newest at bottom.

## 2026-06-09 — Gate A close on the SOUND ∞-foundation
User directive: deliberately close Gate A (`∑Res(α)=0`) on the now-sound `∞`-foundation,
discharging the remaining inputs of `traceRationalityDataNF_ofMovingData` /
`residueSum_eq_zero_of_traceRationalityDataNF` (`FormTraceCoherenceFromMovingNF.lean`).

Constraints emphasized:
- Use the SOUND `InftyFibreDataNF` (NOT the buggy `InftyFibreData`) and `T := bundle traceFun`
  (NOT `valueChartTrace` — `valueChartTrace` needs the Puiseux frame, the recurring trap).
- Order: do (1) Wall-2 Φ + per-pole moving sections wiring + (3) `hcoh_inf` via
  `InftyFibreDataNF.ofRegular` + (2) the `T:=traceFun` genus-0 discharge FIRST (reuse proven
  atoms `TraceForm.traceExtendsAt_branchPoint`, the ∞-bridge,
  `coeff_eq_of_entire_diff_of_recipCoeff_continuousAt`). Then (4) genericity.
- HONEST FALLBACK: if (4) is too large this round, close everything else so Gate A rests on
  JUST `∃ f, AdaptedCover`-genericity (one named lemma), with precise diagnosis.
- SOUNDNESS review active: NO custom axiom, NO sorry on a false statement; verify every
  structure field is genuinely satisfiable (campaign repeatedly found latent false fields:
  `hbranch`, `hsep`, `R₀=0`, old `InftyFibreData` reciprocal). Authoritative
  `#print axioms` (NOT LSP), confirm `[propext, Classical.choice, Quot.sound]`; keep non-vacuity.
- Discipline: do NOT touch the 2 untracked orphans or any PROVEN file; new file(s) only;
  commit only files touched with explicit `git add`, never `-a`/`-A`; ≤2 targeted builds, no
  full glob (OOM 8 GB); local only. Reference Miranda §VIII.3.
