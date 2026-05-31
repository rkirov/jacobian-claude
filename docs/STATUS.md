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
| 7 | `exists_periodLattice_realBasis` | PeriodLattice.lean:855 | period lattice has a real basis of ℂ^g (Riemann bilinear) | **universal instance** (see below) |
| 8 | `ambientPhi_ambientPullback_eq` | Jacobians.lean:456 | ambient degree identity `Φ∘Ψ = deg·id` on all of ℂ^gY | **critical path** of `pushforward_pullback` |

> **Count history (transparency).** A prior pass listed "8" sorries but
> scanned only `Jacobians/` and **missed `ambientPhi_ambientPullback_eq` in the
> root `Jacobians.lean`** — there were really **9**. The lattice reduction
> (2026-05-31, below) then merged the two lattice instances
> (`DiscreteTopology` + `IsZLattice`) into the single `exists_periodLattice_realBasis`,
> netting the current **8**. Reproduce: `grep -rnE '(:=\s*sorry$|^\s*sorry$)' Jacobians.lean Jacobians/`.

### #7 is the universal load-bearing sorry; #8 is the degree headline's last gap

`Jacobian X = (ℂ^g) ⧸ periodLattice` is only a **complex manifold / Lie group**
*given* that `periodLattice` is a discrete, full-rank ℤ-lattice. As of 2026-05-31
both of those are **derived mechanically** (Mathlib `ZSpan`) from the single input
#7 `exists_periodLattice_realBasis`. Consequently **every statement asserting
holomorphicity of a map into `Jacobian X` carries `sorryAx` through #7**, even
though the underlying construction is itself clean: `ofCurve_contMDiff`,
`pushforward_contMDiff`, `pullback_contMDiff`. Honest reading: *"the Abel–Jacobi
map is holomorphic" is proven conditional on the period lattice being a lattice* —
not unconditionally.

#8 `ambientPhi_ambientPullback_eq` is the **ambient (matrix-level) degree
identity** `Φ(Ψ y) = deg·y` for all `y`. It is *already proven on period vectors*
by the keystone `ambientPhi_ambientPullback_periodVec_of_cycle` (which consumes the
§3 preimage cycle + the proven `periodVec_pushforward`); the only remaining gap is
**extending it off the lattice to all of `ℂ^gY`** — which is exactly what #7's
full-rank lattice (the periods span `ℝ^{2g}`) provides. So #7 and #8 are linked:
discharging #7 also unlocks the off-lattice extension of #8.

(By contrast, purely **algebraic** facts about `Jacobian X` that do not invoke
its manifold structure — e.g. `ofCurve_self : ofCurve P P = 0`, a group
equation — are clean.)

## Verified axiom status of the headline declarations

| declaration | status | `sorryAx` enters via |
|---|---|---|
| `ofCurve_self` | **CLEAN** | — (group equation) |
| `ofCurve_contMDiff` | sorryAx | #7 (lattice → manifold structure) |
| `pushforward_contMDiff` | sorryAx | #7 |
| `pullback_contMDiff` | sorryAx | #7 (and the trace matrix, #4) |
| `ofCurve_inj` | sorryAx | #3 (Abel) + #7 |
| `pushforward_pullback` | sorryAx | #8 (ambient identity) + #7 (manifold); #8 in turn rests on #4+#6+#7 |
| `genus_eq_zero_iff_homeo` | sorryAx | #1 |
| `traceForm` | sorryAx | #4 (branch-point extension) |

## The genuinely-clean core (verified `[propext, Classical.choice, Quot.sound]`)

The real, unconditional content proved along the way:

- **Smooth-path family** `exists_smoothPath_family` (PeriodLattice.lean) — the
  chart-ball cover + junction-concat keystone. The substance behind "the
  Abel–Jacobi map is holomorphic" (the *statement* is then gated only by #7).
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
Stokes, branched-cover trace boundedness via Puiseux) — or, like #8, mechanical
consequences gated on those. **There is no "prove-it-from-scratch" win left** —
the §3 geometry was the last such piece. The 2026-05-31 lattice reduction did NOT
discharge any classical content; it *isolated* it: the two lattice instances are
now mechanical (Mathlib `ZSpan`) consequences of the single, precisely-stated
input #7, so the irreducible Hodge nugget is named and minimal.
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
  via #7. The smooth-path family is clean; `ofCurve_contMDiff` is not.
- `ofCurve_contMDiff`'s docstring referenced `localLift_quotient_eq_ofCurve_eventually`
  as a "sorry"; it is now proven.
- `AxiomCheck.lean`'s comment referenced `ambientPhi_ambientPsi_eq` "still sorry'd
  in HolomorphicForms.lean"; the trace unification removed that stub.
- **Sorry miscount**: the first audit pass scanned only `Jacobians/` and reported
  "8" sorries, missing `ambientPhi_ambientPullback_eq` in the root `Jacobians.lean`
  — the true count was **9**. Now corrected, and the table above is the verified list.

## Lattice reduction (2026-05-31)

The two opaque period-lattice instance sorries (`DiscreteTopology` + `IsZLattice`,
the "most basic" foundation under the whole into-`Jacobian` API) were replaced by a
single, precisely-stated classical input #7 `exists_periodLattice_realBasis`
(*the period lattice is the ℤ-span of a real basis of `ℂ^g`*), with both instances
**derived mechanically** from it via Mathlib's `ZSpan.instDiscreteTopology` /
`instIsZLatticeRealSpan`. Net: 2 sorries → 1, the assumption is now named, minimal,
and pins the exact Hodge / Riemann-bilinear content. This does **not** make the
holomorphicity headlines axiom-clean (they still carry `sorryAx` via #7); doing that
would require either discharging #7 (needs Hodge / de Rham `H¹ ≅ ℂ^{2g}`, not in
Mathlib) or promoting #7 to an explicit typeclass hypothesis (an architecture choice
the project previously declined — see README "Approach").
