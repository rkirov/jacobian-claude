# Closing Walls B (#7 cut surface) and C (#3 Abel converse): route decision and plan (2026-06-10)

Books-first research pass: full read of Forster GTM 81 §§19–21 (pp. 153–173), Miranda Ch. VIII
(pp. 245–264), Griffiths–Harris pp. 228–235 (all from the repo PDFs), recon of
/tmp/jacobian-mrdouglasny and the pinned Mathlib, and a name-by-name audit of repo assets.
**No code changed in this pass.**

## Where the walls stand (verified in-repo today)

The repo is at exactly **2 sorries**:

* **Wall B** — `exists_cutSurface` (`Jacobians/CutSurfaceRelations.lean:161`).
* **Wall C** — `abelJacobi_twoPoint_ne_zero` (`Jacobians/Meromorphic/Abel.lean:671`).

### Wall B: what `CutSurface` actually demands

`structure CutSurface X` (CutSurfaceRelations.lean) has **no cut-chart field** — the chart lives
only in comments. Its fields are exactly:

| field | content |
|---|---|
| `loop : Fin (2 * genus X) → (ℝ → X)` | 2g symplectic homology-basis loops |
| `loop_closed` | each `IsClosedSmoothLoop` |
| `generates` | `closedLoopPeriods X ⊆ Submodule.span ℤ (range (periodVec ∘ loop))` |
| `U : Set ℂ`, `hbox` | convex open ⊇ the unit box `wCLM '' (Icc 0 1 ×ˢ Icc 0 1)` |
| `h, F : Fin (genus X) → ℂ → ℂ`, `hh`, `hF` | pullback coefficients `h_j = cut^*ω_j`, holomorphic on `U`, with primitives `F_i` |
| `boundaryWord_R1` | `(AᵀB − BᵀA) i j = rectBoundaryIntegral (F_i·h_j)` |
| `boundaryWord_R2` | `(AᵀB̄ − BᵀĀ) i j = − boundaryForm (h j) (F i)` |
| `nondeg` | nonzero `v` ⟹ `∑ v_j·h_j` nonzero somewhere in the open box |

The boundary words are Miranda's Lemma 4.1 (p. 257) specialized to `(σ,τ) = (ω_i, ω_j)` and
`(ω_i, ω̄_j)` — i.e. the **4g-gon dissection content**. Downstream, `CutSurface` feeds (only)
`toCanonicalDissection` → `realBasis_of_canonicalDissection` (Dissection.lean, proven) →

```
theorem exists_periodLattice_realBasis :
    ∃ b : Module.Basis (Fin (2 * genus X)) ℝ (Fin (genus X) → ℂ),
      truePeriodLattice X = Submodule.span ℤ (Set.range ⇑b)
```

(PeriodLattice.lean:855). **That theorem is the entire consumer surface**: it alone yields the
`DiscreteTopology (truePeriodLattice X)` and `IsZLattice ℝ (truePeriodLattice X)` instances
(PeriodLattice.lean:865, 872) and the off-lattice extension in `ambientPhi_ambientPullback_eq`
(Jacobians.lean, the `pushforward_pullback` headline). R1/R2 (`cutSurface_R1/R2`, proven) are
**internal scaffolding** of one particular proof of `exists_periodLattice_realBasis`; nothing in
the challenge API needs the bilinear relations themselves.

### Wall C: the exact remaining obligation

`abelJacobi (twoPointDivisor P Q) = 0` unfolds (via `abelJacobi_twoPointDivisor`, proven) to

```
periodVec (smoothPath P₀ P) − periodVec (smoothPath P₀ Q) ∈ truePeriodLattice X
                                  = Submodule.span ℤ (closedLoopPeriods X)
```

where `periodVec γ i = lineIntegral (periodBasisForm X i) γ`. The contradiction half is **fully
proven**: `div f = twoPointDivisor P Q` gives `f.HasSingleSimplePole Q` (orders read directly off
`MeromorphicFunction.div = orderAtPoint`), then `nonempty_homeo_sphere_of_singleSimplePole`
(DegreeOneSphere.lean:630, proven) + `genus_zero_of_nonempty_homeo_sphere` (proven today)
contradict `0 < genus X`. So Wall C is exactly **Abel's converse (sufficiency) for two-point
divisors**: from the span-membership above, produce `f : MeromorphicFunction X` with
`f.div = twoPointDivisor X P Q`.

## What the books actually say

### Forster §20 (pp. 159–165): Abel's sufficiency is DISSECTION-FREE

Forster's preface: "We have also avoided using, without proof, any theorems on the topology of
surfaces." His proof of Abel 20.7, sufficiency direction (p. 164, part (a)):

1. **Weak solutions** (20.1, p. 159): a smooth `f ∈ 𝓔(X_D)` that locally looks like `ψ·z^k`,
   `ψ` smooth nonvanishing, `k = D(a)`. Products/quotients give weak solutions of sums of divisors.
2. **20.2** (pp. 159–160): `d″f/f` of a weak solution is a **smooth (0,1)-form on all of X**
   (`d″f/f = d″ψ/ψ` near the divisor points).
3. **Lemma 20.5** (pp. 162–163): for a curve `c` inside a chart disk, an explicit weak solution of
   `∂c` (`f₀ = exp(ψ·log((z−b)/(z−a)))`, bump `ψ`), equal to `1` off the disk, with
   `∫_c ω = (1/2πi)∬_X (df/f)∧ω` for closed `ω`; general curves by subdivision and products.
   The identity rests on **Lemma 20.3** (p. 160): `(1/2πi)∬ (df/f)∧dg = ∑ k_j·g(a_j)` — a
   planar-Stokes + shrinking-circle residue computation. For holomorphic `ω` the needed primitive
   `g` is a bump × (local holomorphic primitive); no smooth Poincaré lemma needed.
4. **20.7(a)** (p. 164): the Abel hypothesis gives a 1-chain `c` with `∂c = D`, `∫_c ω_i = 0` ∀i.
   Since `(1,0)∧(1,0) = 0` on a surface, `∬ (df/f)∧ω = ∬ (d″f/f)∧ω = 0` ∀ω ∈ Ω. By **19.10**
   there is `g ∈ 𝓔(X)` with `d″g = d″f/f`; then `F := e^{−g}·f` has `d″F = 0`, is a weak solution
   of `D`, hence a **meromorphic** solution: `div F = D`. ∎
5. **19.10** (p. 156): `d″g = σ` is solvable iff `∬ σ∧ω = 0` for all `ω ∈ Ω(X)`. Forster derives
   it from 19.9 (`𝓔^{0,1} = d″𝓔 ⊕ Ω̄`, p. 156), which needs exactly: (i) `∬_X` of 2-forms +
   compact-support Stokes (his 10.20), (ii) the Dolbeault comparison `H¹(X,𝒪) ≅ 𝓔^{0,1}/d″𝓔`
   (15.14), (iii) `dim Ω̄ = g`, (iv) orthogonality computations (19.6). No harmonic PDE theory,
   no dissection, no triangulation anywhere in the chain.

### Forster §21.4 (pp. 168–170): the period LATTICE without a dissection

`Per(ω₁,…,ω_g) ⊂ ℂ^g` is a lattice, proven WITHOUT any homology basis:

* **(a) Local Jacobi map** (pp. 168–169): pick `g` points `a_j` such that no nonzero holomorphic
  form vanishes at all of them (Lemma 21.3, p. 168 — pure linear algebra on the g-dimensional
  `Ω(X)`), disjoint simply connected chart disks `U_j`, and
  `F(x)_i = ∑_j ∫_{a_j}^{x_j} ω_i` (chart-local primitives). Its Jacobian at `a` is the rank-g
  evaluation matrix `A = (φ_ij(a_j))`, so `W := F(U₁×…×U_g)` is a neighborhood of 0 (IFT).
* **(b) Discreteness** (p. 169): if `0 ≠ t ∈ Γ ∩ W`, then `t = F(x)`, and the chain
  (chart paths `a_j → x_j`) minus (the loop combination realizing `t`) has all `Ω`-periods 0, so by
  **Abel's sufficiency** there is meromorphic `f` with simple poles at the `a_j` (principal parts
  `c_j ≠ 0`) and zeros at `x_j`. The **residue theorem** applied to `f·ω_i` gives
  `∑_j c_j·φ_ij(a_j) = 0` for all `i` — contradicting rank g. Hence `Γ ∩ W = 0`.
* **(c) Non-degeneracy** (pp. 169–170): a nonzero real-linear functional vanishing on `Γ` gives
  `c ∈ ℂ^g∖0` with `Re ∫_α ∑c_jω_j = 0` for every loop α; by **19.8** (p. 156) `∑c_jω_j = 0`,
  contradiction. (19.8 = "all-periods-vanishing closed form is exact" + "harmonic ⟹ 0"; for the
  holomorphic-form case this is provable by an elementary max-principle/open-mapping argument —
  see B-3 below — no harmonic theory needed.)

Then 21.1 (lattice = discrete + not in a proper real subspace, pp. 166–167) finishes. **Note the
dependency reversal: Forster's lattice theorem (Wall B) CONSUMES Abel's sufficiency (Wall C's
engine), not vice versa.** (21.5 Remark, p. 170: the symplectic basis is a *consequence*, not an
input.)

### Miranda Ch. VIII (pp. 247–264) and Griffiths–Harris (pp. 228–235): the polygon route

Both prove Abel's sufficiency through the **standard identified 4g-gon** (Miranda p. 247; G–H
p. 228 "represent the surface … as a polygon with 4g sides"):

* Miranda Lemma 4.1 (pp. 257–258): `∫_{∂P} f_σ·τ = ∑_i A_i(σ)B_i(τ) − A_i(τ)B_i(σ)` — exactly the
  repo's `boundaryWord_R1/R2` fields, but ALSO needed with `τ` **meromorphic** (a third kind form).
* Lemma 4.6 (pp. 260–261, the crux): given `A₀(D) = 0`, a third-kind `ω` with residues `D(p)` and
  all a/b-periods in `2πiℤ`. Consumes: existence of third-kind forms (residue-sum-zero criterion,
  his VII.1.15 — repo-feasible via RR), Lemma 4.1 with meromorphic `τ`, the **planar residue
  theorem inside the polygon** (`ρ_k = ∑Res(f_{ω_k}·τ) = A₀(D)_k` — the reciprocity), R1
  (Lemma 4.5) for the `(A;B)/(Bᵀ,−Aᵀ)` exactness, and nonsingularity of `A,B` (Lemma 4.4 ← 4.2/4.3).
* `f(p) = exp(∫_{p₀}^p ω)` (p. 262); single-valuedness additionally needs `H₁(X∖supp D)` generated
  by the `a_i,b_i` and small circles (left to Problems VIII.4.A/B — more polygon topology).
* G–H pp. 228–235 is the same plan (reciprocity for differentials of the third kind via the
  polygon Δ, normalized basis, "η′ has all integral periods … by the first bilinear relation").

So the polygon route needs MORE than the current `CutSurface` (a third boundary word with
meromorphic `τ`, plus punctured-surface H₁ generation), on top of the unbuilt polygon existence.
Springer pp. 139–141 (cited in old docstrings) is not in the repo; it is the same classical
dissection construction (Radó triangulation + classification) — not consulted, not needed.

### Verdict on key question (a)

Abel's converse does **not** need the 4g-gon. Forster's route replaces all surface topology by one
global-analysis input — the ∂̄-solvability criterion 19.10 — whose ingredients the repo has mostly
already built (below). The reciprocity/normalization step of Miranda 4.6 / G–H is precisely what
19.10 makes unnecessary.

### Verdict on key question (b)

`CutSurface` should be **retired, not constructed**. Its sole consumer is
`exists_periodLattice_realBasis`; Forster 21.4 proves that statement (same signature, via
Mathlib's ZLattice API) with no dissection, no R1/R2, no boundary words. The proven
CutSurface→R1/R2 files stay as banked archival theorems (hypothesis-conditional, zero cost).

## Recon results

* **mrdouglasny** (/tmp/jacobian-mrdouglasny, fresh look at `Jacobians/Axioms.lean`): both walls
  are axioms there — `AX_IntersectionForm`, `AX_AnalyticCycleBasis` (H₁ basis),
  `AX_PeriodLattice`, `AX_RiemannBilinear`, `AX_AbelTheorem`. **Nothing portable** (confirms the
  2026-06-08 recon).
* **Wallace**: already mined — the repo's `Jacobians/PlanarStokes/PlanarCompactSupportStokes.lean`
  credits Michal J Wallace (`stokes_local_euclidean` port). Nothing further to take for either wall.
* **Pinned Mathlib**: `Topology/CWComplex/` has bare definitions only (Abstract/Classical Basic,
  Finite, Subcomplex) — **no triangulations, no surface classification, no branched coverings**.
  So Route B-I's topology is fully greenfield; the branched-cover-pullback idea still requires the
  classification normal form, which no Lean precedent covers. Conversely the **ZLattice API is a
  perfect fit** for B-II: `IsZLattice` (= `span ℝ = ⊤`), `ZLattice.module_free`/`ZLattice.rank`,
  `Basis.ofZLatticeBasis` with `ofZLatticeBasis_span : span ℤ (range (b.ofZLatticeBasis K)) = L`
  (ZLattice/Basic.lean:638), `discreteTopology_iff_isOpen_singleton_one` for the subgroup
  discreteness from `Γ ∩ W = 0`. Mathlib also has the planar open-mapping theorem
  (`AnalyticAt.eventually_constant_or_nhds_le_map_nhds`, Analysis/Complex/OpenMapping.lean:119)
  and the strict-derivative IFT (`HasStrictFDerivAt.toPartialHomeomorph`/`map_nhds_eq`) needed by
  B-2/B-3.

## Repo assets the Forster route consumes (verified by grep this pass)

| asset | status |
|---|---|
| `DbarOpenDisk.dbar_solvable_open_disk` (Forster 13.2, smooth data on open disk) | proven |
| `comparison_linearEquiv : DolbeaultH01 X ≃ₗ[ℝ] 𝔇.toFiniteCover.cechH1 0` (DolbeaultComparisonEquiv.lean:648, needs `ChartDiskCover` + `IsLeray`) | **proven** — Forster 15.14 is already in-repo |
| `chartDiskCover` is Leray + locally realizable (`exists_realizableLerayCover`, SkyscraperProductWitness.lean:246) | proven |
| `DolbeaultH01`, `OneFormsZeroOne`, `dbarL`, `SmoothCOneForms` (the 𝓔^{0,1}/d″𝓔 package) | proven |
| `residueSum_pairForm_mul_eq_zero_unconditional` (ResidueTheoremStokes.lean:780, `∑Res(f·h·dg₀)=0`, genus-free) | proven |
| `meroFormDiv` (CanonicalFormIso.lean — α/ω₀ as a meromorphic function; converts `f·ω_i` to pair frame) | proven |
| `pairDualMap_injective` + `pairDualMap_surjective` (tail Serre duality `L(K−D) ≅ H¹(D)^*`) | proven |
| tail RR `exists_riemannRoch_divisor_unconditional`, `h1TailDim_zero_eq_genus_unconditional`, `lDim_eq_zero_of_deg_neg` | proven |
| `riemannRoch_inequality` (`deg A − lDim A ≤ h¹_Čech(0) − 1`, SerreOmega0) | proven |
| Primitive/monodromy toolkit: `pathPrimValue`, `pathPrimValue_eq_of_homotopy`, `exists_primitiveChain`, `IsLocalPrimitiveOn` | proven |
| `localLift` + `localLift_eq_const_add_periodVec_ChartBallPath` + `localLift_contMDiffAt` (chart-disk holomorphic primitive of the basis forms — exactly 21.4(a)'s `F_i`) | proven |
| `ManifoldIFT.exists_holo_localInverse`; planar Stokes (`PlanarCompactSupportStokes`), PoU cover (`ResidueStokesCoverPoU`), annulus residue atoms, `PlanarHolomorphicChangeOfVariables` | proven |
| smooth bumps / `SmoothPartitionOfUnity` over chart disks (used by DolbeaultComparisonInverse) | proven (Mathlib + repo wiring) |

Missing bridges (the honest new work): `pathPrimValue = lineIntegral` on smooth paths; a global
`∬_X σ∧ω` pairing (PoU over `chartDiskCover`); `finrank ℂ (cechH1 0) = genus X`; the weak-solution
calculus; conjugate forms `ω̄` as `(0,1)`-sections.

## Route options

### Wall C

**C-I (Miranda/G–H polygon).** Needs `exists_cutSurface` *plus* a third boundary-word field with
meromorphic `τ`, the polygon-interior residue theorem, and `H₁(X∖{P,Q})` generation. Strictly
dominated by C-II unless the polygon is built anyway. Cost: that of B-I + ~1.5k. **Rejected.**

**C-II (Forster §20 weak solutions — RECOMMENDED).** The shared **Abel engine**:

> **ENGINE.** Given curves `γ_m : ℝ → X` (continuous, chart-subdividable) and `n_m : ℤ` forming a
> chain `c` with `∂c = D` and `pathPrimValue`-periods `∫_c ω_i = 0` for the basis forms, there is
> `f : MeromorphicFunction X` with `f.div = D`.

* **E0 — plumbing** (~400–700 LoC, LOW-MED): chain formalism (finite families of curves +
  ℤ-coefficients, boundary divisor); the FTC bridge `pathPrimValue = lineIntegral` for
  `IsSmoothPath`/`IsClosedSmoothLoop` (build on `localLift_eq_const_add_periodVec_ChartBallPath`);
  unfold `abelJacobi = 0` into a chain with zero periods (span-membership ⟹ finite ℤ-combination).
* **E1 — weak solutions** (~300 LoC, LOW): `WeakSolution D f` predicate (Forster 20.1), products,
  integer powers, the smooth global `(0,1)`-datum `σ_f = d″f/f` (20.2 — smooth ACROSS the divisor
  since `d″f/f = d″ψ/ψ` locally; this is the soundness-critical smoothness claim, prove it as a
  named lemma).
* **E2 — per-curve solution + identity** (Forster 20.5 + 20.3) (~1.0–1.5k LoC, MED): subdivision
  into chart disks (`exists_monotone_Icc_subset_open_cover_Icc` pattern already used by
  `PrimitiveChain`); the explicit `exp(ψ·log((z−b)/(z−a)))` solution; the identity
  `∫_{c_j} ω = (1/2πi)∬ (df_j/f_j)∧ω` for holomorphic `ω` — a PLANAR computation (each `df_j/f_j`
  is supported in one chart disk): planar Stokes + shrinking-circle residue (reuse
  `PlanarCompactSupportStokes` + annulus atoms + `ResidueStokesPoleBump` patterns).
* **E3 — the ∂̄-kill (Forster 19.10, repo-native form)** (~2.0–3.5k LoC, MED-HIGH — the crux):
  * **E3b — the integration atom**: the pairing `Λ(σ)_i := ∑_k ∬_{chart k} ρ_k·(σ∧ω_i coeffs)`
    over the fixed `chartDiskCover` PoU; ℝ/ℂ-linearity; **Stokes-vanishing** `Λ(dbarL u) = 0`
    (per-chart planar Stokes + PoU telescoping — same pattern as `ResidueTheoremStokes`); value on
    the chart-supported E2 pieces: `Λ(σ_f)_i = ∫_c ω_i` (planar change of variables,
    `PlanarHolomorphicChangeOfVariables`). This is the "ONE integration atom" the 2026-06-09 books
    verdict predicted; it is bounded and PoU-planar, never a manifold-Stokes theory.
  * **E3c — positivity**: conjugate forms `ω̄` as smooth `(0,1)`-sections (~150–300); the matrix
    `(Λ(ω̄_j)_i)` invertible via `∬ i·ω∧ω̄ > 0` (pointwise `2|w|² dx∧dy ≥ 0` per chart, one chart
    `> 0`; `MeasureTheory` positivity lemmas).
  * **E3a — `finrank ℂ (cechH1 0) = genus X`**: lower bound `≥ g` is FREE from
    `riemannRoch_inequality` + tail-RR (`lDim A = deg A + 1 − g` for `deg A > 2g−2` ⟹
    `h¹_Čech(0) ≥ g`). Upper bound `≤ g`: port Miranda's maximizer vanishing (VI.2.5–2.7, already
    ported at the TAIL level) to the Čech side, i.e. ONE new statement "tail-solvability at `A₀`
    ⟹ `cechH1`-vanishing at `A₀`" via the proven skyscraper/localRealization machinery — or the
    direct tail↔Čech surjection (Miranda Ch. IX §3 is the book anchor). **Riskiest single item**;
    two independent fallbacks listed below.
  * **E3d — assembly**: `dim_ℝ DolbeaultH01 = 2·h¹_Čech(0) = 2g` (`comparison_linearEquiv`) +
    `Λ` hits 2g ℝ-independent values on `{[ω̄_j], [i·ω̄_j]}` (E3b/E3c) ⟹ `Λ` injective on
    `DolbeaultH01` ⟹ `[σ_f] = 0` ⟹ `σ_f = dbarL u`.
* **E4 — exp/correction + meromorphicity** (~400–700 LoC, MED): `F := e^{−u}·f`; `d″F = 0` off
  `supp D` ⟹ holomorphic (C¹ + ℂ-linear derivative ⟹ `DifferentiableAt ℂ` — elementary);
  meromorphic at `supp D` with `orderAtPoint = D` via the local `ψ·z^k` form + removable-singularity
  repair (`MeromorphicNFRepair`/`FormRemovableSingularity`); package as `MeromorphicFunction` and
  conclude `f.div = D` (Finsupp equality).
* **C headline** (~100 LoC): engine at `D = twoPointDivisor P Q` with the chain
  `smoothPath P₀ P − smoothPath P₀ Q − ∑ n_k λ_k`; then the proven contradiction half closes
  `abelJacobi_twoPoint_ne_zero`.

### Wall B

**B-I (build `exists_cutSurface`).** Radó-style triangulation (pullback along the repo's branched
cover is available, but the hard parts remain), classification of surfaces to the 4g-gon normal
form, a holomorphic cut chart, the two boundary-word integral identities, `generates`. No Mathlib
support, no Lean precedent for the classification; the branched-cover leverage shaves the
triangulation only. Estimate ≥ 10k LoC, VERY HIGH risk, months. **Rejected.**

**B-II (Forster 21.4 — RECOMMENDED).** Re-prove `exists_periodLattice_realBasis` verbatim
(signature unchanged ⟹ zero churn in PeriodLattice.lean/Jacobians.lean), retiring
`exists_cutSurface`:

* **B-1 — Lemma 21.3 + evaluation rank** (~150–300 LoC, LOW): `g` points where no nonzero form
  vanishes simultaneously (induction on `finrank`, evaluation functionals); rank-g of
  `A = (φ_ij(a_j))`.
* **B-2 — local Jacobi map + IFT** (~500–800 LoC, MED): `G : ∏_j disk_j → ℂ^g`,
  `G(z)_i = ∑_j P_ij(z_j)` with `P_ij` = chart primitives (reuse `localLift`); `G` is a SUM of
  one-variable holomorphic maps, so its strict Fréchet derivative is assembled by hand
  (`ContDiffAt.hasStrictFDerivAt`), `DG(a) = Matrix.toLin A` invertible ⟹
  `HasStrictFDerivAt.map_nhds_eq` gives `W ∈ 𝓝 0`.
* **B-3 — non-degeneracy (21.4c)** (~400–700 LoC, MED): if a real functional kills
  `truePeriodLattice`, get `0 ≠ ω = ∑c_jω_j` with `Re(lineIntegral ω γ) = 0` for every closed
  smooth loop. Define `u(x) := Re (lineIntegral ω (smoothPath x₀ x))` — EXACTLY well-defined (two
  smooth paths differ by a smooth-loop period, whose Re vanishes; `periodVec_concat_of_smooth` +
  zero-velocity concat machinery). Locally `u = Re G` with `G` the `localLift` primitive. At a max
  of `u` (compactness), Mathlib's open-mapping dichotomy forces `G` locally constant; `{u = max}`
  is open and closed ⟹ `ω ≡ 0` — contradiction. No harmonic theory, no `∬`.
* **B-4 — discreteness (21.4b)** (~400–700 LoC, MED, NEEDS THE ENGINE): `t ∈ Γ ∩ W`, `t ≠ 0` ⟹
  `t = G(z)`, chain (straight chart segments `a_j → x_j`, smooth) minus the lattice combination has
  zero periods ⟹ ENGINE gives `f` with `div f = ∑(x_j − a_j) ≠ 0` (disjoint disks make the points
  distinct), simple poles at `a_j` with leading coefficients `c_j ≠ 0`
  (`laurentCoeff_order_ne_zero`); residue theorem on `f·ω_i` (convert by `meroFormDiv` to the pair
  frame `residueSum_pairForm_mul_eq_zero_unconditional`) gives `A·c = 0` — contradiction. Then
  `Γ ∩ W = 0` + subgroup ⟹ `DiscreteTopology`.
* **B-5 — ZLattice assembly + retirement** (~200–400 LoC, LOW): discrete + `span ℝ = ⊤`
  (`IsZLattice`) ⟹ `ZLattice.module_free` + `ZLattice.rank` = 2g + `Basis.ofZLatticeBasis` +
  `ofZLatticeBasis_span` ⟹ the verbatim `exists_periodLattice_realBasis`. Handle `g = 0`
  separately (trivial module, empty basis, ~30 LoC). Delete the `sorry` and the
  `exists_cutSurface`/`exists_canonicalDissection` plumbing (keep `CutSurface`+R1/R2 files as
  archival hypothesis-conditional theorems, or drop them from the import root).

## Decision

**Adopt the Forster analytic route for BOTH walls. Build Wall C's engine FIRST; Wall B consumes
it.** This reverses the assumed order — C does not wait on B; B-4 waits on the engine. B-1/B-2/B-3
are engine-independent and can run in parallel (two agents: one on E-phases, one on B-1..3).
No new topology is built anywhere; every step is anchored to Forster §§19–21 with repo assets
verified above.

### Phase table (with the ≤2-concurrent-builds constraint)

| phase | content | LoC est. | risk | depends on |
|---|---|---|---|---|
| C-0 | chains + `pathPrimValue=lineIntegral` bridge + hypothesis unfolding | 400–700 | LOW-MED | — |
| C-1 | weak solutions (E1) | ~300 | LOW | C-0 |
| C-2 | per-curve solution + planar 20.3/20.5 identity (E2) | 1000–1500 | MED | C-1 |
| C-3 | pairing atom + positivity + conjugate forms (E3b, E3c) | 1200–2000 | MED-HIGH | — (parallel) |
| C-4 | `h¹_Čech(0) = g` (E3a) | 800–2000 | **MED-HIGH (crux)** | — (parallel) |
| C-5 | 19.10 assembly + exp + meromorphicity + headline (E3d, E4) | 600–1000 | MED | C-2,3,4 |
| B-1 | 21.3 points + rank | 150–300 | LOW | — |
| B-2 | local Jacobi + IFT | 500–800 | MED | B-1 |
| B-3 | non-degeneracy (max principle) | 400–700 | MED | — |
| B-4 | discreteness via engine + residue theorem | 400–700 | MED | C-5, B-2 |
| B-5 | ZLattice assembly, retire CutSurface | 200–400 | LOW | B-3, B-4 |

Total ≈ 6–9.5k LoC. Suggested agent split: agent 1 = C-0→C-1→C-2→C-5; agent 2 = C-3, C-4, then
B-1→B-2→B-3 while agent 1 assembles; B-4/B-5 last.

### Fallbacks for the crux C-4 (`h¹_Čech(0) = g`)

1. (Primary) Čech-side maximizer vanishing: tail-realizability at Miranda's `A₀` ⟹
   `cechH1 A₀ = 0` via the proven skyscraper/`exists_localRealizationData` machinery; then the
   constant `h1Dim D − h1TailDim D` (Čech-RR minus tail-RR, `h0Dim_eq_lDim`) pins `h¹_Čech(0) = g`.
2. Full tail↔Čech comparison `cechH1 D ≅ tail-H¹(D)` (Miranda Ch. IX §3 as book anchor) — more
   work, more reusable.
3. (Last resort, changes route shape) prove 19.10's injectivity via the tail-side Serre pairing
   plus a cocycle→tail bridge atom, skipping the dimension count.

If all three stall, the polygon route (B-I/C-I) remains the only alternative — reassess only then.

## Soundness guards

* **Statement freeze**: `exists_periodLattice_realBasis` and `abelJacobi_twoPoint_ne_zero` keep
  their exact current statements; no consumer churn. Verify with
  `lake env lean ChallengeConformance.lean` after B-5.
* **Non-vacuity**: every new structure (chains, `WeakSolution`, pairing) gets a witness lemma
  (e.g. the explicit 20.5 disk solution; `Λ(ω̄_j)` computed nonzero at g = 1 is NOT required —
  positivity E3c is the witness).
* **The 20.2 smoothness claim** (`d″f/f` smooth across the divisor) is the easiest place to
  misformalize — state it chart-locally with the `ψ ≠ 0` hypothesis explicit and prove before
  building on it.
* **ℝ vs ℂ bookkeeping** in E3d: `comparison_linearEquiv` is ℝ-linear; `DolbeaultH01` carries the
  known module-instance diamond — keep `set_option backward.isDefEq.respectTransparency false`
  discipline (as in `RealForms`/`DolbeaultComparisonInverse`) and work with `finrank ℝ`
  throughout; the `2·` factor is `finrank_real_of_complex` (`cechH1_dolbeault_comparison_proof`,
  DolbeaultComparisonEquiv.lean:660 shows the exact pattern).
* **Engine generality**: state the engine for arbitrary degree-0 `∂c = D` (B-4 needs up to g
  points), not just two-point divisors.
* **Per-commit verification**: targeted `lake build Jacobians.X` + `#print axioms` on each new
  leaf; the full-glob orphan sweep before declaring either wall closed (standing discipline).
* Sign conventions (`2πi` factors, orientation of `∬`) cancel in the only consumed facts
  (`Λ` injectivity, `Γ∩W = 0`); still, validate E2's identity numerically-by-eye against Forster
  20.3's statement before generalizing.

## What this changes about the standing architecture

* `CutSurface`/`CanonicalDissection`/boundary words: retired from the critical path (archival).
  The Riemann bilinear relations are NOT proven by the new route and are NOT needed by the
  challenge; if ever wanted, they become provable later from the lattice + Hodge-style arguments.
* The "#7 realBasis path = cut-surface + Green" memory item is superseded by this plan.
* The Abel engine (C-5) is the single most reusable new asset: it also unlocks `Pic⁰ ≅ Jac`
  (Forster 21.6–21.7) and Jacobi inversion (21.9, via the proven RR) if ever desired — neither is
  needed for the challenge.
