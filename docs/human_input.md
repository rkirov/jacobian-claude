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

### Autonomous soundness redirect made this session (flag for review)
While discharging input (2) (`hentire`/`hrecip_cont`) I found a SOUNDNESS ISSUE in the
*caller-hypothesis* `hentire` of the proven `traceRationalityDataNF_ofMovingData`: it is stated
against the RAW trace `valueChartTrace ω₀ f Φ`, which is **discontinuous across branch points** (its
value at a branch is a partial sum, not the removable limit — `FormTraceGlobalTPatched.lean:432-433`
explicitly flags `BranchAwareTraceSelection.hbranch` as FALSE). So for any cover with branch points
(genus ≥ 1), `AnalyticOnNhd (valueChartTrace - L.R) univ` is **unsatisfiable** — `hentire` is a latent
false field of the raw constructor. (The proven constructor itself is sound — it only *consumes*
`hentire`; the falsity is in trying to *supply* it.) This is exactly the `T:=valueChartTrace` "Puiseux
trap" the directive warned about, surfacing at the entire-remainder step.

DECISION (autonomous, run-ahead): rather than supply a false `hentire`, I built a NEW sound constructor
`traceRationalityDataNF_ofPatched` (new file `FormTraceRationalityNFPatched.lean`) with
`T := valueChartTracePatched ω₀ f Φ br` — the value-correct trace (patched to the limit at branches),
the planar shadow of the proven bundle `traceFun` extension (the directive's `T := traceFun`). With
this `T`, `hentire` is **PROVEN internally** (not assumed) via `analyticAt_valueChartTracePatched_off_centres`
(branch values handled by the axiom-clean boundedness crux `traceLocalCoeff_mul_sub_tendsto_zero`, NOT
continuity) + junk-freeness. This builds on the SOUND target `TraceRationalityDataNF` structure +
`residueSum_eq_zero_of_traceRationalityDataNF` (reused, not edited), with the SOUND `InftyFibreDataNF`.
NEEDS-REVIEW: confirm this re-point is acceptable (it changes the geometric trace object from raw to
patched, but the patched trace is the correct §VIII.3 `Tr_F α`; raw was the wrong object across branches).
