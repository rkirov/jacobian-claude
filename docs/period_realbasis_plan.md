# Plan — #7 `exists_periodLattice_realBasis` (period lattice is a full-rank ℝ-lattice)

**Target** (`PeriodLattice.lean`): `∃ b : Basis (Fin 2g) ℝ (ℂ^g), truePeriodLattice X = span ℤ (range b)`,
where `truePeriodLattice X = span ℤ (closedLoopPeriods X)` and `periodVec γ = (∮_γ ω₁,…,∮_γ ω_g)`.

## Status: scaffold DONE (commit `f382960`), now filling bottom-up (riskiest/deepest first)

`Jacobians/Dissection.lean` splits the goal into **two pillars** + a proven **assembly**:

| node | kind | status |
|---|---|---|
| `realBasis_of_canonicalDissection` | assembly: `2g` ℝ-indep vectors in `ℂ^g≅ℝ^{2g}` ⟹ basis; generation ⟹ ℤ-span | **PROVEN** |
| `exists_periodLattice_realBasis` | = assembly ∘ the two pillars | **PROVEN** (modulo pillars) |
| `exists_canonicalDissection` | **Pillar T (topology)** — isolated | **SORRY** (isolate; surface classification, Mathlib has no path) |
| `periodVec_linearIndependent` | **Pillar A (analysis)** — Riemann bilinear relations | **SORRY** → the build below |

Pillar T is *isolated* (building `H₁(surface)≅ℤ^{2g}` = the surface classification theorem, out of
scope). Pillar A is *built* via Riemann's cut-surface + Green's theorem (no Hodge/de Rham — see
`docs/period_lattice_realbasis_research.md`).

## Pillar A dependency tree (the build) — committed cut-surface model

**Model the cut surface as a BOX image** (not a literal `4g`-gon — avoids polygon subdivision; lets
us use Mathlib's *box* divergence theorem directly via pullback). The dissection carries (fields to
be ADDED to `CanonicalDissection` when filling — "definitions may shift"):

* `cut : (Set.Icc (0:ℝ) 1 ×ˢ Set.Icc 0 1) → X` (or `ℝ² → X` restricted) — smooth, a diffeo on the
  interior onto `X` minus the cut graph, i.e. the cut surface `S₀` realized as a box image;
* the boundary parametrization data: the four edges of `∂([0,1]²)` traverse the `4g`-gon boundary
  word `a₁b₁a₁⁻¹b₁⁻¹⋯`, so `∮_{∂box} (cut^*α)` decomposes into the `2g` loop line-integrals with the
  `f`-jumps (a holomorphic primitive's increments across the cuts = the conjugate periods).

Then the tree, **deepest leaf first** (= fill order):

1. **`greenOnBox`** *(DEEPEST LEAF — fill first; self-contained, pure Mathlib, planar)*.
   `∮_{∂[0,1]²} α = ∬_{[0,1]²} dα` for a `C¹` 1-form `α = P dx + Q dy` on the box, i.e.
   `∮_{∂box}(P,Q) = ∬_box (∂Q/∂x − ∂P/∂y)`. **Wrap Mathlib's
   `MeasureTheory.integral2_divergence_prod_of_hasFDerivAt_off_countable`** (literally 2-D Green in
   divergence form) into the `∮ = ∬ d` language. Validates the whole approach. [~150–400 LoC]

2. **`exists_primitive_on_box`** / **`exists_primitive_simplyConnected`**. A holomorphic `ω`'s
   primitive `f` (`f' = ω`-coeff) on the simply-connected cut box: termwise antiderivative on a
   disc, globalized over the contractible box. [~300–700]

3. **`surfaceIntegral`** `∬_X β := ∬_{[0,1]²} (cut^* β)` for a 2-form `β`, + **pullback Green**
   `∬_X dα = ∮_{∂box}(cut^*α)` (from 1 + `extDeriv` commuting with pullback,
   `Mathlib.Analysis.Calculus.DifferentialForm`). [~300–600]

4. **`riemann_relation_I`** `∑_k (A_{lk}B_{jk} − B_{lk}A_{jk}) = 0`: `f_j ω_l` is a *closed* 1-form
   on `S₀` (`d(f_jω_l)=ω_j∧ω_l=0`, wedge of holomorphic `(1,0)`-forms in complex-dim 1), so
   `∮_{∂box} cut^*(f_jω_l) = ∬ d = 0`; boundary bookkeeping gives the relation. [~400–800]

5. **`riemann_relation_positivity`** `−i∑_k(A_{jk}\overline{B_{jk}} − B_{jk}\overline{A_{jk}}) > 0`:
   `−i∮_{∂box} cut^*(f̄_jω_j) = ∬_X (−i)ω̄_j∧ω_j = ∬ 2|f_j'|² dA > 0` (Green + pointwise
   `−i\overline{dz}∧dz = 2dx dy` + `setIntegral_pos`, `f_j'=ω_j≠0` on an open dense set). [~400–800]

6. **`periodVec_linearIndependent`** *(the pillar-A goal)*: the positivity Hermitian form
   `−iΠᵀJΠ̄ ≻ 0` forces the `2g` rows of the period matrix `Π` (the `periodVec (loop k)`) to be
   ℝ-independent. (Linear algebra: a real relation `∑c_k·period_k=0` yields a nonzero `ω=∑c_jω_j`
   with all periods real-dependent, contradicting positivity.) [~300–600]

**Module layout:** `Jacobians/GreenBox.lean` (1,2 — pure Mathlib), `Jacobians/Dissection.lean`
(extend the structure + 3–6, or split `BilinearRelations.lean`). Keep `GreenBox` upstream
(SmoothPathCore-free; pure `Mathlib`); the rest imports `SmoothPathCore` and stays upstream of
`PeriodLattice`.

**Mathlib keystones:** `integral2_divergence_prod_of_hasFDerivAt_off_countable` (box Green),
`extDeriv`/`extDeriv_pullback` (`Analysis.Calculus.DifferentialForm`), `Complex.…` (primitive on a
disc), `setIntegral_pos`. **Gap to build:** simply-connected primitive / contour homotopy-invariance
(Mathlib has neither as named lemmas).

## Pillar T (isolated)
`exists_canonicalDissection` bundles the symplectic homology basis + the cut-box chart + generation,
all as the single topological input. Building it = surface classification + cylinder-Stokes; out of
scope, isolated (cf. how the repo isolates `PreimageCycle`/`MonodromyLiftFamily` data).

Refs: Chai §1.4; Griffiths–Harris pp.231–232; Forster §§20–21; Miranda Ch. V.
