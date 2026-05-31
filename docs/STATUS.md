# Project status — verified ground truth

Authoritative, **machine-verified** status of the Jacobians challenge. Last
established 2026-05-31 by `#print axioms` (`lean_verify`) on the headline
declarations. Reproduce with `lake env lean AxiomCheck.lean` (clean core) or
`#print axioms <name>` on any declaration below.

A declaration is **clean** iff `#print axioms` reports exactly
`[propext, Classical.choice, Quot.sound]`. It **carries `sorryAx`** iff that
appears in its axiom set — i.e. it (transitively) depends on one of the 8 open
`sorry`s. `sorryAx` is honest: it is Lean's record that *something* in the
dependency tree is unproved. There are **0 custom `axiom`s** in the project;
the only unproved surface is the 8 `sorry`s below.

## The 8 open `sorry`s

Every one is a **named classical theorem not in Mathlib** (not a mechanical
gap). The §3 loop-lifting geometry — the last piece that was "hard Lean, no
missing math" — is now done (`exists_monodromyLiftFamily`, 2026-05-30).

| # | declaration | file:line | what it is | role |
|---|---|---|---|---|
| 1 | `genus_eq_zero_iff_homeo` | Genus.lean:84 | genus 0 ⟺ sphere (uniformization / Riemann–Roch) | **isolated leaf** |
| 2 | `deg_div` | Abel.lean:577 | `deg(div f)=0` (proper-map degree) | **DEAD leaf** — nothing depends on it |
| 3 | `abelJacobi_twoPoint_ne_zero` | Abel.lean:707 | two-point Abel–Jacobi image ≠ 0 | **critical path** of `ofCurve_inj`; *is* Abel's theorem |
| 4 | `traceExtendsAt_branchPoint` | TraceForm.lean:849 | trace of a form extends across branch points | under `traceForm` ⇒ `pushforward_pullback` |
| 5 | `traceForm_comp` | TraceForm.lean:1091 | trace functoriality `(g∘f)₊=g₊∘f₊` | **off-path leaf** |
| 6 | `exists_loop_off_branchLocus` | TracePullback.lean:349 | homotope a loop off the branch locus | **critical path** of `pushforward_pullback`; needs manifold Stokes (deferred) |
| 7 | `DiscreteTopology (truePeriodLattice X)` | PeriodLattice.lean:841 | period lattice is discrete (Hodge / Riemann bilinear) | **universal instance** (see below) |
| 8 | `IsZLattice ℝ (truePeriodLattice X)` | PeriodLattice.lean:847 | period lattice is full rank `2g` (Hodge / Riemann bilinear) | **universal instance** (see below) |

### #7 / #8 are the universal load-bearing sorry

`Jacobian X = (ℂ^g) ⧸ periodLattice` is only a **complex manifold / Lie group**
*given* that `periodLattice` is a discrete, full-rank ℤ-lattice. Those are
exactly instances #7 and #8. Consequently **every statement asserting
holomorphicity of a map into `Jacobian X` carries `sorryAx` through #7/#8**,
even though the underlying construction is itself clean. This includes
`ofCurve_contMDiff`, `pushforward_contMDiff`, `pullback_contMDiff`. The honest
reading: *"the Abel–Jacobi map is holomorphic" is proven conditional on the
period lattice being a lattice* — not unconditionally.

(By contrast, purely **algebraic** facts about `Jacobian X` that do not invoke
its manifold structure — e.g. `ofCurve_self : ofCurve P P = 0`, a group
equation — are clean.)

## Verified axiom status of the headline declarations

| declaration | status | `sorryAx` enters via |
|---|---|---|
| `ofCurve_self` | **CLEAN** | — (group equation) |
| `ofCurve_contMDiff` | sorryAx | #7/#8 (lattice → manifold structure) |
| `pushforward_contMDiff` | sorryAx | #7/#8 |
| `pullback_contMDiff` | sorryAx | #7/#8 (and the trace matrix, #4) |
| `ofCurve_inj` | sorryAx | #3 (Abel) + #7/#8 |
| `pushforward_pullback` | sorryAx | #4 + #6 + #7/#8 |
| `genus_eq_zero_iff_homeo` | sorryAx | #1 |
| `traceForm` | sorryAx | #4 (branch-point extension) |

## The genuinely-clean core (verified `[propext, Classical.choice, Quot.sound]`)

The real, unconditional content proved along the way:

- **Smooth-path family** `exists_smoothPath_family` (PeriodLattice.lean) — the
  chart-ball cover + junction-concat keystone. The substance behind "the
  Abel–Jacobi map is holomorphic" (the *statement* is then gated only by #7/#8).
- **§3 monodromy lift geometry** `exists_monodromyLiftFamily`,
  `exists_orbitLoops_of_monodromyLiftFamily`, `lift_eqOn_Icc_of_eq` and the
  `velCont` toolkit (TracePullback.lean / CotangentCoeff.lean) — the loop-lifting
  machinery. *(`exists_preimageLoopFamily` itself shows `sorryAx`, but only the
  inherited #4 via `traceFormTotal`/leaf D — the geometry is clean.)*
- `periodVec_pushforward`, `ambientPhi_preserves_truePeriodLattice`,
  `ambientPullbackJac_preserves_truePeriodLattice` (period/lattice algebra).
- `localLift_quotient_eq_ofCurve_eventually` (path-algebra identification — now
  proven; older docstrings calling it a "sorry" are stale).
- Line integrals on manifolds, `lineIntegral_pullback`,
  `pathSpeed_comp_eq_mfderiv` (chain rule), the trace **off the branch locus**
  (`traceForm_toFun_of_notMem_branchLocus`, `exists_localSheetSystem`),
  the off-branch covering / fibre finiteness, the manifold IFT
  (`exists_holo_localInverse`), local holomorphic sections, Montel's theorem,
  chart-invariance of `meromorphicOrderAt`.
- The discharge degree layer guarded by `AxiomCheck.lean` (`ContMDiff.degree`,
  `degreeFiber`, regular-value existence, `finite_branchLocus_of_nonconstant`).

## The honest verdict

All 8 remaining `sorry`s are deep classical theorems Mathlib lacks
(uniformization, Abel 1826, Hodge/Riemann-bilinear period relations, manifold
Stokes, branched-cover trace boundedness via Puiseux). **There is no
"prove-it-from-scratch" win left** — the §3 geometry was the last such piece.
Realistic ways forward, in decreasing tractability:

- **Assume-and-derive** the named classical inputs as explicit typeclass
  hypotheses and derive the headlines as honest *conditional* theorems. (The
  project tried this with `HasAbelsTheorem` and reverted to `sorry` to keep the
  unproved surface visible — see README "Approach".)
- **Build one self-contained real piece** (e.g. Rouché-style local multiplicity
  → #2; but #2 is a dead leaf). High effort, varied value.
- **Consolidate / document** — keep the proven/assumed boundary crisp and
  honest. *(This document.)*

## Recently corrected overclaims (2026-05-31 audit)

- "Abel–Jacobi holomorphicity — fully proven, axiom-clean" conflated the (clean)
  smooth-path family with the holomorphicity *statement*, which carries `sorryAx`
  via #7/#8. The smooth-path family is clean; `ofCurve_contMDiff` is not.
- `ofCurve_contMDiff`'s docstring referenced `localLift_quotient_eq_ofCurve_eventually`
  as a "sorry"; it is now proven.
- `AxiomCheck.lean`'s comment referenced `ambientPhi_ambientPsi_eq` "still sorry'd
  in HolomorphicForms.lean"; the trace unification removed that stub.
