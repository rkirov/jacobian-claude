# Čech finiteness (`exists_cechModel`) — Forster-grounded attack plan

*Supersedes the earlier "local overlap disk-acyclicity atom" plan. Grounded in a direct read of
Forster, **Lectures on Riemann Surfaces** (GTM 81, repo root PDF), §12–14.*

## 0. The goal and where it sits

`CechFinitenessWiring.exists_cechModel 𝔘 D` (`CechFinitenessWiring.lean:379`, the one finiteness
`sorry`) → `DolbeaultLadder.finiteDimensional_cechH1` (Forster Thm 14.9 / Cor 14.10): `H¹(𝔘, 𝒪_D)`
finite-dimensional. This is the foundation under χ-additivity, all of Serre, and Riemann–Roch.

It must produce, for an **arbitrary** finite cover `𝔘` and divisor `D`: a sup-norm Montel model
(`DiskOverlapData` + `Coboundaries` *including* its `leray` field) and a comparison
`𝔘.cechH1 D ≃ₗ[ℂ] c.supH1`.

## 1. What is already proven (axiom-clean inventory)

**Functional-analysis / Montel spine** (= Forster Lemma 14.6 + 14.7, abstracted):
- `CechFiniteness.finiteDimensional_h1_of_leray_compact` — Schwartz/Riesz–Schauder reduction:
  `δ⊕ρ` surjective + `ρ` compact ⟹ `Z¹/range δ` finite.
- `BddHol.*` (Banach space of bounded-holomorphic), `isCompactOperator_restrictCLM_of_compact`
  (disk-Montel, any compact `K ⊆ U`), `isCompactOperator_pi`.
- `CechFinitenessWiring.{finiteDimensional_supH1, leray_surjective, finiteDimensional_cechH1_wired}`
  — the model → finiteness assembly. **Only `exists_cechModel` itself is open.**

**Dolbeault comparison** (= Forster §13/§14 Dolbeault iso) — **the crown jewel**:
- `GoodCover.comparison_linearEquiv' 𝔇 : DolbeaultH01 X ≃ₗ[ℝ] 𝔇.toFiniteCover.cechH1 0` for **any**
  `ChartDiskCover X`, sorry-free, `IsLeray`-free. ⇒ `cechH1 0` is cover-independent across chart-disk
  covers at `D = 0` *for free*. `cech_coboundary_of_cechToDolbeaultForm_exact` packages injectivity.

**Refinement / Leray machinery** (= Forster §12):
- `CechRefinement{,Homotopy,Leray}`: `refineC0/1/2`, δ-commutation, `refineH1`, functoriality,
  STEP A homotopy-independence (`refineH1_eq`), the **sorry-free mutual-refinement iso**
  `refineH1_equiv`, and the **reduction** `refineH1_equiv_of_leray` from the two honest predicates
  `RefinementLift` / `RefinementDescend`.
- `CechDiskAcyclic`: target `IsDiskAcyclic`, the function-level interface `FunctionDiskAcyclic`, the
  reduction `isDiskAcyclic_of_funcLevel`, and `cechH1_subsingleton_of_isDiskAcyclic` (atom ⟹ H¹=0).
- `ChartDiskComparisonPoU`: reusable Bott–Tu PoU machinery (`chartDiskCechToDolbeaultForm`, the
  coboundary-killing `…_coboundary_le`). Sound and reusable.

**∂̄ engine** (= Forster §13):
- `DbarDisk.dbar_solvable_of_compactSupport` — **Forster 13.1** (Cauchy transform, compact support). ✓
- `DbarDiskCohomology.dbar_solvable_ball (hg : ContDiff ℝ ⊤ g) … : ∀ z ∈ ball c r, ∂̄u z = g z`
  — solves on a ball **but requires a GLOBALLY smooth datum `g`**. ✓
- `dbar_holo_splitting_ball` — 2-set holomorphic re-splitting on a ball (inputs globally smooth). ✓
- `differentiableAt_of_dbar_eq_zero{,_local}` — Wirtinger `∂̄=0 ⇒ holo`. ✓

**Partition of unity on the open union** (the topologically-correct base):
- `CechFinitenessBallSolve.coverOpenUnionPoU 𝔇 : SmoothPartitionOfUnity … ↥(⋃Uᵢ) univ` summing to
  `1` on **all** of `↥(⋃Uᵢ)` (`sum_coverOpenUnionPoU_eq_one`, `sum_openUnionRhoHat_eq_one`),
  plus `openUnionRhoC/Hat`, `openUnionCoverPrim`, `contMDiffAt_openUnionCoverPrim`. ✓

## 2. The classical proof (Forster §12–14) mapped to repo objects

| Forster | statement | repo status |
|---|---|---|
| 13.1 | `∂̄f=g` solvable, `g` compact support | ✓ `dbar_solvable_of_compactSupport` |
| **13.2** | `∂̄f=g` solvable on an **open disk** for `g ∈ ℰ(open disk)` (datum smooth on the disk only; **exhaustion**) | **✗ MISSING** — repo only has the *globally-smooth-datum* `dbar_solvable_ball` |
| 13.4 | `H¹(disk, 𝒪)=0` (cover of a single coordinate disk) | needs 13.2 |
| 12.6 | `H¹(𝔘, ℰ)=0` (smooth split via PoU) | PoU on open union ✓; split to build |
| 12.8 | Leray: acyclic cover ⟹ `refineH1` iso | `refineH1_equiv_of_leray` ✓ (needs atom 13.4) |
| 14.6 | cover→shrinking lift `ζ=ξ+δη` (bump + ∂̄-solve) | = the `leray` field; uses **only** `dbar_solvable_ball` |
| 14.7 | finite-dim image (Schwartz iteration) | ✓ `finiteDimensional_h1_of_leray_compact` |
| 14.9 | finiteness via 14.7 + Leray | the assembly |

**Decisive observation.** Two different ∂̄-needs:
- The **`leray` field (14.6)** is a *cover-vs-shrinking* lift. Its cutoff bump `ψ` (=1 on the
  shrinking `𝔚`, support compact in `𝔘`, exists by `𝔚 ⋐ 𝔘`) makes `ψω` **globally** smooth, so the
  **already-available** `dbar_solvable_ball` suffices. No 13.2 needed.
- **Genuine acyclicity (13.4), required by Leray 12.8**, must solve `∂̄g=h` on the *whole* open disk
  with `h` smooth on the open disk only (the glued `∂̄gᵢ`). Its chart image fills the ball, leaving no
  room for a cutoff. **This needs 13.2.**

## 3. Why the previous routes stalled (do not resume these)

- **`GluedDbarDatum` / `SharedChartCover`** tried to prove `H¹(one cover)=0` directly from a Bott–Tu
  PoU datum. A PoU subordinate to a *non-covering* family sums to `1` only on a **closed core**, so the
  datum agrees with `∂̄(chartPrimᵢ)` only on `interior core`
  (`dbarDatum_agrees_on_interiorCore`), and the corrector is holomorphic only there. This is **not**
  Forster's argument and cannot be patched on `X` (a single chart can't cover compact `X`). The fix is
  the open-union PoU (already started, §1) **plus** the right ∂̄ engine (13.2).
- **`ChartDiskAcyclicFromDolbeault.OverlapChartDiskDolbeaultExact`** is vacuous: it requires an overlap
  family (covering only `Uᵢ∩Uⱼ`) to *equal* a `ChartDiskCover X` (which must cover `X`). Also
  `ChartDiskDolbeaultExact 𝔇 ⟺ cechH1(𝔇,0)=0 ⟺ genus 0` (because `comparison_linearEquiv'` makes the
  Bott–Tu map an iso). Salvage the PoU machinery in `ChartDiskComparisonPoU`; drop the `Overlap*`
  consumers.

## 4. Plan (bottom-up; each step is needed regardless of the §6 fork)

1. **Forster 13.2 — `dbar_solvable_open_disk`** *(first deliverable; the single missing engine).*
   `∀ R>0, ∀ g : ℂ→ℂ smooth on ball c R, ∃ u smooth on ball c R, ∂̄u = g on ball c R`.
   Proof (Forster p.106): exhaust `Rₙ ↑ R`; cutoffs `ψₙ` (=1 on `ball Rₙ`, supp in `ball Rₙ₊₁`); solve
   `∂̄fₙ = ψₙg` via 13.1; inductively Runge-correct by Taylor polynomials so
   `‖f̃ₙ₊₁ − f̃ₙ‖_{ball Rₙ₋₁} ≤ 2⁻ⁿ` (`fₙ₊₁−f̃ₙ` is holo on `ball Rₙ`, approximate by a Taylor partial
   sum); locally-uniform limit `f` is smooth, the holomorphic corrections preserve `∂̄f=g`.
   Mathlib pieces: `ContDiffBump`, power-series partial-sum uniform convergence on subdisks,
   locally-uniform-limit-of-holomorphic.

2. **13.4 atom — honest `FunctionDiskAcyclic` for a chart-disk region cover.** Smooth-split the cocycle
   on `↥(⋃Uᵢ)` (open-union PoU); glue `∂̄gᵢ` to a form `h` on the chart-image ball; solve `∂̄g=h` via
   **13.2**; `fᵢ := gᵢ − g` is holomorphic and splits. Discharges the disk-acyclicity atom
   (`IsDiskAcyclic` / `cechH1_subsingleton`) — the sound replacement for `HasGluedDbarDatum`.

3. **Leray 12.8 (cover-independence).** Feed the atom to overlap/refinement families →
   `RefinementLift` / `RefinementDescend` → `refineH1_equiv` for strictly-finer Leray refinements.

4. **`leray` field (14.6).** For the chart-disk Montel model: smooth-split + cutoff bump +
   `dbar_solvable_ball` (no 13.2). Then `finiteDimensional_supH1`.

5. **Comparison + assembly.** `cechH1(chartcover, 0) ≅ supH1` (germ↔`BddHol`; partly in
   `CechModelCochain`/`CechModelDatum`) + cover-independence ⟹ `exists_cechModel`.

## 5. First concrete target

`Jacobians/Dolbeault/DbarOpenDisk.lean` (new): **Forster 13.2**, `dbar_solvable_open_disk`. Self-
contained analysis on top of `DbarDisk.dbar_solvable_of_compactSupport`; unblocks steps 2–5.

## 6. Architecture fork (decide after the atom lands)

Consumers (`CohomologicalRR`, `DolbeaultLadder`, `SkyscraperSnake`) take an **arbitrary** Leray cover.
- **(A)** Full cover-independence via Leray 12.8 (step 3) — the "right" math, needs the atom.
- **(B)** Restate the ladder leaves over a `ChartDiskCover` (RR only needs *some* cover) — lighter, but
  edits soundness-sensitive leaves.
Both are gated on the same atom (steps 1–2), so the fork is deferrable.
