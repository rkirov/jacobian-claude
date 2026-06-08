# Chart-disk Čech H¹ finiteness — plan (`Jacobians/Dolbeault/ChartDiskFiniteness.lean`)

## Goal
`finiteDimensional_cechH1_chartDisk (𝔇 : ChartDiskCover X) :
    FiniteDimensional ℂ (𝔇.toFiniteCover.cechH1 (0 : Divisor X))`
and (if reachable) `FiniteDimensional ℝ (DolbeaultH01 X)` via the proven
`GoodCover.comparison_linearEquiv' 𝔇 : DolbeaultH01 X ≃ₗ[ℝ] 𝔇.toFiniteCover.cechH1 0`.

## Why a ChartDiskCover (not the Montel chartCover)
The Montel model (`CechModelHolomorphic*`) has its `leray` field as an honest `sorry`
(`CechModelHolomorphicLeray.lean`): its cover sets `Uov` are chart-images of `chartOpen∩chartOpen`,
i.e. arbitrary planar opens, NOT balls. The per-chart cutoff ∂̄-solve then only gives the cover
cocycle `x` holomorphic on the shrinking `Wov`, not the full overlap `Uov` (two-scale dilemma), and
the no-cutoff route needs ∂̄-solvability on arbitrary planar opens (Behnke–Stein, absent).

A `ChartDiskCover` has `U i` = chart-preimage of a Euclidean *ball* (`isDisk`). On a ball cover set
the Forster 14.6 lift takes the cocycle at the COVER level: smooth-split, ∂̄-solve `h_i` on the FULL
ball `U_i` (no cutoff — `dbar_solvable_ball` applies to the whole ball), and the cocycle
`ζ_{ij} = h_j∘τ − h_i` is holomorphic on the full overlap automatically (matching ∂̄ via the
Wirtinger chain rule `dbarDisk_comp_holo`). NO cutoff dilemma.

## Reuse inventory (all proven, axiom-clean)
- `HolomorphicDiskOverlapData` / `HolomorphicCoboundaries` (CechModelHolomorphic.lean): the GENERIC
  (not Montel-specific) FA bundle. `ρ_compact`, `finiteDimensional_supH1` (given `leray`),
  `leray_surjective` already proven. I instantiate these with ChartDiskCover geometry.
- `CechFiniteness.{finiteDimensional_h1_of_leray_compact, isCompactOperator_pi,
  isCompactOperator_of_subtypeL_comp}`.
- `BddHol.{restrictOpenCLM, precompHolCLM, isCompactOperator_restrictOpenCLM_of_compact,
  completeSpace, ofAnalyticOn, ...}`.
- `DbarDiskCohomology.{dbar_solvable_ball, differentiableAt_of_dbar_eq_zero}`.
- `dbarDisk_comp_holo` (DolbeaultComparisonProof), `dbarFun_{add,sub,const_smul}` (CechDiskAcyclic),
  `dbarFun_mul`/`dbarFun_finset_sum` (GluedDbarDatum).
- `transition_analyticAt_of_mem`, `analyticAt_chart_change_to` (CechModelManifold).
- `comparison_linearEquiv'` (GoodCover): `DolbeaultH01 X ≃ₗ[ℝ] cechH1 𝔇 0`.

## Construction steps
1. Geometry: chart images `ballImg i = φ_i '' U_i` (a ball), overlap images `Uov (i,j) = φ_i '' (U_i∩U_j)`,
   shrinking `Wov` (half-radius), transitions, relative-compactness. [hardest plumbing]
2. δ-complex (δ⁰, δ¹, δ¹cov, hδδ, hcomm) for the instantiated model.
3. `leray` (14.6 lift) via PoU smooth-split + per-ball `dbar_solvable_ball` + `dbarDisk_comp_holo`.
4. `finiteDimensional_supH1`; germ↔BddHol comparison → `FiniteDimensional ℂ (cechH1 𝔇 0)`.

## Honest-sorry policy
Steps 1–2 are large geometric plumbing duplicating the Montel δ-complex; step 4's germ↔BddHol bridge
may be left as the honest `sorry` per the task. The ANALYTIC HEART (step 3 ball-lift) is the priority.
