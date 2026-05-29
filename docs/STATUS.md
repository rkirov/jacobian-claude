# Project status

_Last updated 2026-05-29._

## Current state

**Sorry count: 7. Custom axioms: 0.** `lake build` is clean (exit 0;
only linter warnings). Every challenge signature is defined and every
main theorem compiles. The 7 sorries are named classical theorems not
yet in Mathlib; each is honest (no typeclass-gating, no `:= 0`
placeholder hiding the gap).

> **S1 closed (2026-05-29).** `exists_smoothPath_family` (smooth-path
> existence + Abel–Jacobi basepoint change) is now fully proven and
> axiom-clean, including the chart-ball cover `exists_hop_cover`/
> `exists_smoothChain`. The smooth-path content of the Abel–Jacobi map is
> done; `ofCurve_contMDiff`'s residual `sorryAx` is now only via the
> Jacobian's S2/S3 lattice instances, not S1.

> Historical note: an earlier version of this file claimed "0 sorries"
> via a typeclass-gating strategy (`HasAbelsTheorem`, `HasResidueTheorem`,
> …). That strategy was **reverted** — gated axioms are content-equivalent
> to `sorry` but hide the unproved surface. All gaps are now honest
> `sorry`s visible in Lean's warnings.

## The 7 sorries

| ID | Location | Name | Classical content | Tier |
|----|----------|------|-------------------|------|
| ~~S1~~ | — | ~~`exists_smoothPath_family`~~ | **CLOSED 2026-05-29** (smooth-path existence + basepoint change, incl. chart-ball cover) | ✅ proven, axiom-clean |
| S2 | `PeriodLattice.lean:899` | `DiscreteTopology (truePeriodLattice X)` | period lattice is discrete (Riemann bilinear) | research-frontier |
| S3 | `PeriodLattice.lean:905` | `IsZLattice ℝ (truePeriodLattice X)` | lattice has full rank 2g (Hodge) | research-frontier |
| S4 | `PeriodLattice.lean:1121` | `exists_preimageCycle_of_nonconstant` | branched-cover lifting (Forster §10.11) | hard |
| S5 | `Genus.lean:81` | `genus_eq_zero_iff_homeo` | uniformization, genus 0 (Forster §16/27) | research-frontier |
| S6 | `Abel.lean:574` | `deg_div` | residue theorem (Forster §4.24) | research-frontier |
| S7 | `Abel.lean:704` | `abelJacobi_twoPoint_ne_zero` | Abel + Riemann–Hurwitz (Forster §21) | research-frontier |
| S8 | `Jacobians.lean` | `ambientPhi_ambientPsi_eq` | degree identity Φ∘Ψ = d·id (Forster §17) | hard (needs real pushforward) |

## Dependency / leverage map

- **S1 — CLOSED.** `exists_smoothPath_family` is fully proven and axiom-clean.
  The proof chain (all axiom-clean): `IsSmoothPath.concat` (keystone junction
  concat) → `periodVec_concat_of_smooth` (period additivity) +
  `exists_smoothPath_family` (cocycle reduction); `zeroVelHop` (zero-velocity
  hop) + `exists_zeroVel_smoothPath_aux` (n-piece glue) + `exists_smoothChain`
  (chart-ball cover). The cover's anchor-varying-chart obstacle was resolved
  by the **common-anchor** trick (`exists_zeroVelPath_of_common_anchor`):
  reach both endpoints of a Lebesgue segment from its common anchor, one via
  `reverse`. `ofCurve_contMDiff` no longer depends on S1 (only on S2/S3 now,
  via the Jacobian's lattice/manifold instances).
- **S7** is the sole remaining math gap for the main theorem `ofCurve_inj`.
  The downstream wiring (`abelJacobi_twoPointDivisor`, basepoint change,
  smooth-path existence) is now proven.
- **S2/S3** ground every `Jacobian X` manifold instance
  (Compact/Charted/IsManifold/LieAddGroup, via `ZLatticeQuotient`).
  S3 depends on S2 (`IsZLattice` takes `[DiscreteTopology]`).
- **S4** is the sole gap for `ambientPsi_preserves_truePeriodLattice`.
- **S5** is the anti-hack constraint (prevents `∀ X, genus X = 0`).
- **S6** currently has no live consumer (`PrincipalDivisors_le_DivisorOfDegZero`
  is unused) — off the critical path.
- **S8** is needed only for `pushforward_pullback`. As of 2026-05-29 it
  is stated honestly (degree pinned to `ContMDiff.degree`); previously
  it was a free-`d` statement that was vacuously false.

## Degree

`ContMDiff.degree` is a **real** fibre-cardinality degree
(`Jacobians.degreeFiber`), not a `:= 0` stub. The regular-value witness
existence is proven unconditionally and `#print axioms`-clean. Open
sub-gaps: degree *positivity* for non-constant maps, and
*well-definedness* (independence of the chosen regular value).

## Real mathematical content proven

(Selected; all kernel-clean modulo the 8 sorries above.)

- **Line integral** (`LineIntegral.lean`, 0 sorries): `pathSpeed`,
  chain rule `pathSpeed_comp_eq_mfderiv`, `lineIntegral_pullback`,
  full concat/reverse regularity algebra.
- **SmoothPath** (`SmoothPath.lean`, `OfCurveAnalyticitySkeleton.lean`):
  smoothstep C¹ calculus, chart-frame cancellation, chart-ball-hop
  smoothness, 2-piece junction smoothness, period-vector reparam
  invariance — all proven and axiom-clean.
- **Period lattice** (`PeriodLattice.lean`): `periodVec` additivity /
  reversal, `mk_periodVec_eq_of_endpoints`,
  `ambientPhi_preserves_truePeriodLattice`, `isClosed_criticalSet`,
  finiteness of the critical set / branch locus.
- **Montel** (`Montel.lean` + `Montel/`): `FiniteDimensional ℂ
  (HolomorphicOneForms X)` via per-chart Arzelà.
- **Abel / divisors** (`Abel.lean`): `orderAtPoint_chart_invariant`,
  `orderAtPoint_isolated_at`, real `divViaOrder`,
  `abelJacobi_twoPointDivisor` (fully proven).
- **Degree tree** (`Discharge/Manifold/`, 42 files): real `degreeFiber`
  + unconditional regular-value-witness existence, all axiom-clean.

## References

See `docs/REFERENCES.md` for per-sorry textbook pointers.
