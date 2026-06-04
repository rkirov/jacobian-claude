# Project status — verified ground truth (2026-06-03, latest)

Authoritative, machine-verified status of the Jacobians challenge (Buzzard v0.4).
Reproduce: `lake build` (full, expects green) and `#print axioms <name>` on any
declaration; conformance via `lake env lean ChallengeConformance.lean`.

## 🟢 2026-06-03 SESSION — big-picture delta (RR/Serre/finiteness sub-tree advanced)

The **5 challenge-critical sorries are UNCHANGED** (none discharged this session — see the table
below). What changed is the **supporting infrastructure beneath the RR wall**: a large sorry-free
foundation was built and one named kernel was eliminated. Headline deltas:

- **The Dolbeault comparison is now FULLY SORRY-FREE** (a named kernel removed). RT2's last leaf
  `toGerm_holoFn` is closed; `comparison_linearEquiv` and `cechH1_dolbeault_comparison_proof` are
  axiom-clean (`finrank ℝ DolbeaultH01 = 2·h1Dim 0`). Built by two coordinated subagents, each
  independently verified (`lake env lean #print axioms`). Only the L3 *wiring* leaf
  `cechH1_dolbeault_comparison` (DolbeaultComparison.lean:227, Leray cover-independence) remains — and
  it has **no consumers**. See [[project_cech_to_dolbeault_progress]].
- **The PDE-free Serre §17 LOCAL residue calculus is fully built & sorry-free** (`Residue.lean`,
  `SerreDuality.lean`, `FormCoeff.lean`): the `resAt` atom + full API; both abstract finite-dim duality
  cores (injectivity→`g ≤ h1Dim 0`, the §17.9 surjectivity count — the litmus PASSED); `coeffAt`,
  `formFnResidue`, and the **Forster §17.6 residue-1 witness**. This de-risks the residue-pairing
  route to `arithmeticGenus_eq_genus`. The remaining Serre content needs the *global* `Res : H¹(X,Ω)→ℂ`
  (well-defined via `∑Res=0`=`deg_div`) + finiteness — both gated on existing sorries, so not yet
  assembled. See [[reference_hodge_bridge_path]], `docs/hodge_bridge_research.md`.
- **The finiteness wall's K-bridge primitive layer is built & axiom-clean** (`CechModelBridge.lean`,
  `CechModelManifold.lean`): `BddHol.ofAnalyticOn`/`ofAnalyticOnOfRelCompact` (germ→`BddHol` codomain),
  `analyticOn_pullback_of_holo` (chart-pullback analyticity), `holoSectionToBddHol` (single-section
  bridge), and `exists_finite_closedBall_cover` (step 1 of non-convex restriction-compactness — the
  next blocker, since cross-chart overlaps aren't convex; step 2 in progress). See
  `docs/cech_finiteness_research.md`, [[project_finiteness_node]].

**Net:** the RR/Serre/finiteness sub-tree is materially de-risked (the worst-feared Dolbeault kernel is
eliminated; the Serre route's local calculus and the finiteness K-bridge are sorry-free), but the
*gating* analytic kernels (`deg_div`, `exists_cechModel`→finiteness, `arithmeticGenus_eq_genus`→Serre)
remain. 22 commits; all individually `lake build`-green + `#print axioms`-clean.

**Dependency map:** `docs/architecture_map.md` — the full DAG to a sorry-free finish
(incorporates the 2026-06-02 finiteness-node finding: the RR wall's finiteness sub-tree is
de-risked reuse, the greenfield is isolated to the Serre/Dolbeault core).

A declaration is **clean** iff `#print axioms` is exactly `[propext, Classical.choice,
Quot.sound]`; it **carries `sorryAx`** iff it transitively depends on one of the open
`sorry`s. There are **0 custom `axiom`s**; the entire unproved surface is the 5 `sorry`s
below.

## Snapshot

- **`lake build`: GREEN** (all 2026-06-03 commits individually verified green + `#print axioms`-clean;
  full-build job count grows as the Serre/finiteness modules land). `lakefile` globs all submodules, so
  this compiles every module (no orphan blind-spots).
- **0 custom axioms.** **~12 `sorry`s total**, in two layers:
  - **5 challenge-critical** (the entire surface the v0.4 API transitively depends on): the table below.
  - **~7 RR/Serre/finiteness sub-tree scaffolding** sorries — a *parallel* Dolbeault-ladder/finiteness
    attempt to eventually *replace* the `exists_riemannRoch_divisor` kernel with a from-first-principles
    proof. NOT yet wired to the challenge headline (the headline still routes through the standalone
    `exists_riemannRoch_divisor`+`deg_div`), so they don't add to the *critical* surface. They are:
    `finiteDimensional_cechH1` ⟸ `exists_cechModel` (finiteness, Forster 14.9); `arithmeticGenus_eq_genus`
    + `serre_h1_eq` (Serre §17); `exists_skyscraperLES`/`chi_jump` (χ-additivity); `exists_properMapDegree`
    (= the `deg_div` engine); `cechH1_dolbeault_comparison` (L3 Leray-wiring, no consumers). The
    2026-06-03 session built the sorry-free scaffolding *beneath* these (Serre §17 local calculus,
    Dolbeault comparison, K-bridge) — see the session delta above.
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
  greenfield risk (no structure sheaf on a manifold). See `docs/archive/riemann_roch_proof_plan.md §4`.
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
