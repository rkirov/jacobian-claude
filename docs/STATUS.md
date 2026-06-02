# Project status — verified ground truth (2026-06-01, latest)

Authoritative, machine-verified status of the Jacobians challenge (Buzzard v0.4).
Reproduce: `lake build` (full, expects green) and `#print axioms <name>` on any
declaration; conformance via `lake env lean ChallengeConformance.lean`.

**Dependency map:** `docs/architecture_map.md` — the full DAG to a sorry-free finish
(incorporates the 2026-06-02 finiteness-node finding: the RR wall's finiteness sub-tree is
de-risked reuse, the greenfield is isolated to the Serre/Dolbeault core).

A declaration is **clean** iff `#print axioms` is exactly `[propext, Classical.choice,
Quot.sound]`; it **carries `sorryAx`** iff it transitively depends on one of the open
`sorry`s. There are **0 custom `axiom`s**; the entire unproved surface is the 5 `sorry`s
below.

## Snapshot

- **`lake build`: GREEN, 8393 jobs.** `lakefile` globs all submodules, so this compiles
  every module (no orphan blind-spots).
- **5 `sorry`s** (down from 6 this session), **0 custom axioms.**
- **Conformance: `ChallengeConformance.lean` typechecks** — the *entire* v0.4 API (genus,
  `genus_eq_zero_iff_homeo`, `Jacobian` + its 7 instances, `ofCurve(_self/_contMDiff/_inj)`,
  `pushforward`/`pullback` + functoriality, `ContMDiff.degree`, `pushforward_pullback`) is
  stated with the exact spec signatures and discharged. The only open question is *which*
  deliverables carry `sorryAx`.
- **This session:** the forward genus-0 endgame went from an opaque `sorry` to a **proven
  reduction wired to the headline** (`exists_singleSimplePole_of_genus_zero :=
  exists_singleSimplePole_of_genus_zero_of_rr`); and `deg_div` was **agent-verified to be
  wall-class** (residue theorem), not the separable quick win first estimated.

## The 5 open `sorry`s — the entire unproved surface

Every one is a **named classical theorem absent from Mathlib** (not a mechanical gap).

| # | declaration | file:line | what it is | missing theorem |
|---|---|---|---|---|
| #3 | `abelJacobi_twoPoint_ne_zero` | Abel.lean:666 | two-point Abel–Jacobi image ≠ 0 | **Abel's theorem (1826)** / Jacobi inversion |
| #7 | `exists_cutSurface` | CutSurfaceRelations.lean:158 | a holomorphic cut chart + boundary-word data exists (surface topology `H₁≅ℤ^{2g}`, `4g`-gon Green, gluing) | **surface classification** (Radó + `4g`-gon) — or reuse Hodge |
| RR | `exists_riemannRoch_divisor` | RiemannRoch.lean:271 | ∃ canonical `K` with `l(D)−l(K−D)=deg D+1−g` | **Riemann–Roch** (Dolbeault ∂̄ → Serre duality) |
| Res | `MeromorphicFunction.deg_div` | RiemannRoch.lean:278 | principal divisor has degree 0 (`∑ orders = 0`) | **manifold residue theorem** `∑ Res = 0` (Stokes) |
| #1b | `genus_zero_of_nonempty_homeo_sphere` | DegreeOneSphere.lean:671 | a surface `≃ₜ S²` has genus 0 | **Hodge** (genus is a topological invariant) |

## Challenge-API conformance (machine-verified `#print axioms`, this session)

**Clean (proven outright, no `sorryAx`):**
- `ofCurve_self` (`ofCurve P P = 0` — a group equation)
- `pushforward_comp_apply`, `pullback_comp_apply` (functoriality of the trace maps)
- the 7 `Jacobian X` instances + `genus` (the period-torus construction is itself clean)

**Carries `sorryAx` (and via which wall):**
| deliverable | via |
|---|---|
| `genus_eq_zero_iff_homeo` | RR + Res (forward: genus 0 → single pole → degree-1 map → `≃ₜ S²`) **and** #1b/Hodge (backward) |
| `ofCurve_inj` | #3 (Abel) + #7 |
| `ofCurve_contMDiff`, `pullback_contMDiff` | #7 (period lattice → `Jacobian` manifold structure) |
| `pushforward_pullback` | #7 (the trace-matrix #4, the Stokes-homotopy #6, and degree well-definedness #8′ are all **discharged**; only the lattice→manifold gap remains) |

Honest reading: *"the Abel–Jacobi map is holomorphic" is proven **conditional on the period
lattice being a lattice** (#7)* — the construction is clean, the holomorphicity statement is
gated. Purely algebraic facts about `Jacobian X` (e.g. `ofCurve_self`) are unconditional.

## The walls are shared — strategic picture

The 5 sorries collapse to **one analytic investment with three faces**, all "compact-Riemann-
surface analysis Mathlib lacks":

1. **Dolbeault ∂̄-solvability → Serre duality → Riemann–Roch** (the `RR` sorry). Highest
   leverage: RR + the proven reduction discharges #1-forward. The disk atom (G1) is done.
2. **Manifold Stokes** → **residue theorem `∑ Res = 0`** (the `Res`/`deg_div` sorry) → also
   feeds RR derivations. Same Stokes family as (1).
3. **Period relations / surface topology** (#7, and #1-backward via Hodge). #7's analytic
   core (`periodVec_linearIndependent`, the Riemann-bilinear-relations ⟹ ℝ-independence) is
   **already proven**; what remains is the cut-chart existence (classification, or a Hodge
   reuse). #3 (Abel) is logically **independent** — no meet-in-the-middle with #7.

What unlocks what:
- **RR + Res** ⟹ `genus_eq_zero_iff_homeo` *forward*.
- **Hodge (#1b)** ⟹ `genus_eq_zero_iff_homeo` *backward*. Together ⟹ the full #1 iff.
- **#7** ⟹ every into/out-of-`Jacobian` holomorphicity statement (`ofCurve_contMDiff`,
  `pullback_contMDiff`, `pushforward_pullback`) becomes unconditional.
- **#3 (Abel)** ⟹ `ofCurve_inj` (with #7).

## The Dolbeault→RR ladder (the concrete plan for the RR wall)

- **G1 — ∂̄-disk atom** (Cauchy–Pompeiu, `DbarDisk.lean`): **DONE, axiom-clean.** Rides
  Mathlib convolution + 2D divergence theorem + repo `GreenBox`.
- **G2 — globalize** ∂̄-solvability on compact `X`: tool in hand
  (`SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source`).
- **G3 — `H¹(X,𝒪)` finite-dimensional** (Forster 14.9): the Montel/Schwartz compactness
  engine is **already proven in-repo** (`Montel.lean`, 0-sorry); remaining = adapt to Čech-H¹
  cochains. Not greenfield.
- **G4 — `𝒪_D`-on-a-manifold + Serre duality** (residue pairing): the concentrated
  greenfield risk (no structure sheaf on a manifold). See `docs/riemann_roch_proof_plan.md §4`.
- **`deg_div`/Res** rides the same manifold-Stokes build (G4-adjacent): `∑ Res_x(df/f) = 0`,
  `Res_x(df/f) = orderAtPoint f x`. The map-degree alternative is blocked (the repo's
  `degreeFiber_eq_card_of_regularWitness` counts only *regular* fibres; zeros/poles are
  ramified, and the order↔multiplicity bridge is itself open).

## Ways forward (decreasing tractability)

1. **Climb the Dolbeault ladder G2→G4** to land RR — highest leverage, the only zero-axiom
   route to #1-forward. `deg_div` falls out of the same Stokes build.
2. **Assume-and-derive**: promote the named classical inputs to explicit typeclass
   hypotheses and ship honest *conditional* headlines. (Tried once with `HasAbelsTheorem`,
   reverted to `sorry` to keep the unproved surface visible — see README "Approach".)
3. **#7 via Hodge reuse** (not Radó — the highest-variance, no-Lean-prior-art tar-pit):
   once the Dolbeault/Hodge build exists for RR, reuse it for the period relations.

## The genuinely-clean core (verified `[propext, Classical.choice, Quot.sound]`)

The real, unconditional content proved along the way: the period-torus construction +
its 7 `Jacobian` instances; the **single-simple-pole extraction from `l(P)=2`** (this
session); the trace pushforward of holomorphic 1-forms incl. the branch-point extension
(#4, discharged); degree well-definedness (`degreeFiber_eq_card_of_regularWitness`, #8′,
ported); the §3 monodromy-lift geometry; `exists_loop_off_branchLocus` (#6, discharged);
ℂℙ¹ as a certified genus-0 surface (`genus_eq_zero`, the `dz = -w⁻²dw` law); Montel's
theorem (`closedBall_isCompact`); the ∂̄-disk atom (G1); `exists_smoothPath_family`; line
integrals on manifolds + the chain rule; chart-invariance of `meromorphicOrderAt`.

## History

Earlier session deltas (the 7→6→5→4 sorry reductions, #4/#5/#6/#8′ discharges, the lattice
reduction, the ℂℙ¹ dz-law, soundness fixes for `toSphere`/`lDim`-junk and the trace map)
are in the git log and the memory notes (`project_jacobian_state_2026-05`,
`project_rr_interface`, `project_sorry_free_roadmap`, `reference_dolbeault_disk_atom`).
This file is the current authoritative snapshot.
