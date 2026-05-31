# Project status — verified ground truth

Authoritative, **machine-verified** status of the Jacobians challenge. Last
established 2026-05-31 by `#print axioms` (`lean_verify`) on the headline
declarations. Reproduce with `lake env lean AxiomCheck.lean` (clean core) or
`#print axioms <name>` on any declaration below.

A declaration is **clean** iff `#print axioms` reports exactly
`[propext, Classical.choice, Quot.sound]`. It **carries `sorryAx`** iff that
appears in its axiom set — i.e. it (transitively) depends on one of the 6 open
`sorry`s. `sorryAx` is honest: it is Lean's record that *something* in the
dependency tree is unproved. There are **0 custom `axiom`s** in the project;
the only unproved surface is the 6 `sorry`s below.

## The 6 open `sorry`s

Every one is a **named classical theorem not in Mathlib** (not a mechanical
gap). The §3 loop-lifting geometry — the last piece that was "hard Lean, no
missing math" — is now done (`exists_monodromyLiftFamily`, 2026-05-30); and
#8′ degree well-definedness — the last *port-able* piece — is now discharged
(2026-05-31, see below).

| # | declaration | file:line | what it is | role |
|---|---|---|---|---|
| 1 | `genus_eq_zero_iff_homeo` | Genus.lean:84 | genus 0 ⟺ sphere (uniformization / Riemann–Roch) | **isolated leaf** |
| 3 | `abelJacobi_twoPoint_ne_zero` | Abel.lean:669 | two-point Abel–Jacobi image ≠ 0 | **critical path** of `ofCurve_inj`; *is* Abel's theorem |
| 4 | `traceExtendsAt_branchPoint` | TraceForm.lean:849 | trace of a form extends across branch points | under `traceForm` ⇒ `pushforward_pullback` |
| 5 | `traceForm_comp` | TraceForm.lean:1091 | trace functoriality `(g∘f)₊=g₊∘f₊` | **off-path leaf** |
| 6 | `exists_loop_off_branchLocus` | TracePullback.lean:349 | homotope a loop off the branch locus | **critical path** of `pushforward_pullback`; needs manifold Stokes (deferred) |
| 7 | `exists_periodLattice_realBasis` | PeriodLattice.lean:855 | period lattice has a real basis of ℂ^g (Riemann bilinear) | **universal instance** (see below) |

> **Count history (transparency).** Earlier passes miscounted; a verified
> `grep -rnE '(:=\s*sorry$|^\s*sorry$)' Jacobians.lean Jacobians/` is the
> ground truth. Recent moves: the dead `deg_div`/`PrincipalDivisors` chain was
> **deleted** (2026-05-31, was #2 — nothing depended on it); the old #8
> `ambientPhi_ambientPullback_eq` (ambient degree identity `Φ∘Ψ = deg·id`) is
> now **proven**; and **#8′ `exists_preimageCycle_sheets_eq_degree` is now
> discharged** (2026-05-31) by porting Bryan Sanchez's axiom-clean degree
> well-definedness (see below). Net: **7 → 6**.

### #7 is the universal load-bearing sorry; #8′ is now DISCHARGED

#### Old #8 `ambientPhi_ambientPullback_eq` — now PROVEN (2026-05-31)

The ambient (matrix-level) degree identity `Φ(Ψ y) = deg·y` **for all `y`** is no
longer a sorry. The keystone `ambientPhi_ambientPullback_periodVec_of_cycle` gives
it on each `periodVec δ` (consuming the §3 preimage cycle + the proven
`periodVec_pushforward`); `Submodule.span_induction` extends it to the whole period
lattice; and the **§7 real period basis** extends it off the lattice
(`ambientPhi_ambientPullback_eq`, Jacobians.lean) — `ambientPhi∘ambientPullbackJac`
is ℂ-linear and agrees with `deg·id` on the ℝ-basis, so `y = ∑ (b.repr y i)·b i`
pushes through. (A defeq-but-not-syntactic `Module ℝ (Fin g → ℂ)` instance clash
broke `restrictScalars`/`Basis.ext`; the working proof converts each real scalar to
its complex coercion componentwise and closes per-term with a defeq-aware `exact`.)
Its sole remaining input is #8′.

#### #8′ `exists_preimageCycle_sheets_eq_degree` — DISCHARGED (2026-05-31)

For a closed loop `δ`, the keystone needs the preimage cycle's `sheets` to equal
`ContMDiff.degree f`. The cycle from `exists_preimageCycle_of_nonconstant` has
`sheets = M.n = #(f⁻¹{δ 0})`, a **regular** fibre (`δ 0 ∉ branchLocus`); its
cardinality is `degreeFiber f` precisely by **degree well-definedness** (all regular
fibres have equal cardinality). This was **proven, axiom-clean, in Bryan Sanchez's
`jacobian-lean-challenge`** as `degreeFiber_eq_card_of_regular_witness`
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`), and is now **ported
into this repo** (22 modules, ~3.3k LOC, `Jacobians/Discharge/Manifold/`; the local
base already had the *conditional* core and shares brsanch's ZZ-tagged origin, so the
port was mechanical). The cycle side exposes `sheets = #fibre` via
`MonodromyLiftFamily.n_eq_fibre_ncard` (the lift bijection) threaded through
`exists_preimageCycle_sheets_eq_fibreCard_of_nonconstant`; the regular value `y₀ =
δ 0` (off the branch locus, `branchLocus = criticalValuesGeneral` defeq) is packaged
as a `RegularValueWitnessReg` (`exists_regularValueWitnessReg_value_eq`), and
`degreeFiber_eq_card_of_regularWitness` closes it: `sheets = #(f⁻¹{y₀}) = w.card =
degreeFiber f = ContMDiff.degree f`. The degree-well-definedness content is verified
axiom-clean (AxiomCheck.lean); `exists_preimageCycle_sheets_eq_degree` itself carries
`sorryAx` only via the *inherited* #4 (trace branch-point) and #6 (Stokes homotopy),
which the cycle already depended on. So `pushforward_pullback` now rests on
**#4 + #6 + #7** (no separate degree gap).

### #7 the universal load-bearing sorry

`Jacobian X = (ℂ^g) ⧸ periodLattice` is only a **complex manifold / Lie group**
*given* that `periodLattice` is a discrete, full-rank ℤ-lattice. As of 2026-05-31
both of those are **derived mechanically** (Mathlib `ZSpan`) from the single input
#7 `exists_periodLattice_realBasis`. Consequently **every statement asserting
holomorphicity of a map into `Jacobian X` carries `sorryAx` through #7**, even
though the underlying construction is itself clean: `ofCurve_contMDiff`,
`pushforward_contMDiff`, `pullback_contMDiff`. Honest reading: *"the Abel–Jacobi
map is holomorphic" is proven conditional on the period lattice being a lattice* —
not unconditionally. The old #8 off-lattice extension *also* consumed #7's real
basis and is now proven (above), so `pushforward_pullback` rests on #7 + #8′
(+ #4/#6 via the trace).

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
| `pushforward_pullback` | sorryAx | #4 (trace branch-point) + #6 (Stokes homotopy) + #7 (manifold). #8′ degree well-definedness is now **discharged** (axiom-clean port), so it no longer contributes a separate gap |
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
  `degreeFiber`, regular-value existence, `finite_branchLocus_of_nonconstant`),
  **including degree well-definedness** `degreeFiber_eq_card_of_regular_witness`
  (every regular fibre has the same cardinality `= degreeFiber f`) — the ported
  brsanch chain that discharges #8′.

## The honest verdict

All 6 remaining `sorry`s are deep classical theorems Mathlib lacks
(uniformization, Abel 1826, Hodge/Riemann-bilinear period relations, manifold
Stokes, branched-cover trace boundedness via Puiseux). **There is no
"prove-it-from-scratch" win left**, and the last *port-able* win (#8′ degree
well-definedness) is now taken —
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
