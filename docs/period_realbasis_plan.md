# Plan — #7 `exists_periodLattice_realBasis` (period lattice is a full-rank ℝ-lattice)

**Target** (`PeriodLattice.lean`): `∃ b : Basis (Fin 2g) ℝ (ℂ^g), truePeriodLattice X = span ℤ (range b)`,
where `truePeriodLattice X = span ℤ (closedLoopPeriods X)` and `periodVec γ = (∮_γ ω₁,…,∮_γ ω_g)`.

## Status: Pillar A DISCHARGED (2026-05-31). Only the isolated input `exists_canonicalDissection` remains.

`Jacobians/Dissection.lean` splits the goal into **two pillars** + a proven **assembly**:

| node | kind | status |
|---|---|---|
| `realBasis_of_canonicalDissection` | assembly: `2g` ℝ-indep vectors in `ℂ^g≅ℝ^{2g}` ⟹ basis; generation ⟹ ℤ-span | **PROVEN** |
| `exists_periodLattice_realBasis` | = assembly ∘ the two pillars | **PROVEN** (modulo the one isolated input) |
| `periodVec_linearIndependent` | **Pillar A (analysis)** — Riemann bilinear relations ⟹ ℝ-independence | ✅ **PROVEN** (axiom-clean) |
| `exists_canonicalDissection` | **isolated input**: topology *+* the two relations (bundled) | **SORRY** (isolated) |

**Pillar A is DONE.** `periodVec_linearIndependent` is proven via the self-contained matrix-algebra
core `linearIndependent_periodRows_of_posDef` (`Jacobians/PeriodMatrixIndep.lean`, axiom-clean): the
two Riemann bilinear relations (R1 `AᵀB=BᵀA`, R2 `H=i(AᵀB̄−BᵀĀ)` positive-definite; sign validated at
`g=1` ↦ `2·Im τ>0`) force the doubled
period matrix `[Π|Π̄]` nonsingular (`det(NᵀJN)=(det N)²·det J`, antidiagonal blocks `±(det H)²≠0` from
`PosDef.det_pos`), hence the `2g` real period vectors are independent. The relations enter as fields
`periodRel_vanishing`/`periodRel_posDef` of `CanonicalDissection`.

**Architecture decision (2026-05-31, flag for review).** The two relations are *bundled into* the
isolated `exists_canonicalDissection` (alongside the topology `H₁≅ℤ^{2g}` + cut chart). This keeps
`exists_periodLattice_realBasis` hypothesis-free. The box-level analytic core for R2 is **proven**
(`boundaryForm_pos`, below); what stays isolated is the cut-chart pullback `cut^*ω=h dz`, the
boundary-word `∮_{∂box}↦∑ₖ(AₖB̄ₖ−BₖĀₖ)`, and (for `g≥2`) Stokes on the `4g`-gon — i.e. exactly the
surface-topology + polygon-Green content Mathlib lacks. The analytic leaves below remain *built and
available* toward eventually discharging R1/R2 from an exposed cut chart (a future refactor).

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

1. **`greenOnUnitBox`** ✅ **DONE** (`Jacobians/GreenBox.lean`, axiom-clean, commit `e3f616d`).
   `∮_{∂[0,1]²}(P dx + Q dy) = ∬_{[0,1]²}(∂Q/∂x − ∂P/∂y)` for ℂ-valued `C¹` `P,Q`, wrapping Mathlib's
   `integral2_divergence_prod_of_hasFDerivAt` (`f=Q, g=−P`). Boundary orientation: counterclockwise
   `∫P(·,0)+∫Q(1,·)−∫P(·,1)−∫Q(0,·)` (callers must match this sign). ~45 LoC.

2. **`exists_primitive_of_convex`** ✅ **DONE** (`Jacobians/Primitive.lean`, axiom-clean, ~16 LoC).
   Mathlib already had it: `Convex.exists_forall_hasDerivWithinAt`
   (`MeasureTheory.Integral.CurveIntegral.Poincare`) + `HasDerivWithinAt.hasDerivAt` on the open box.

   **⚡ Major Mathlib finding (revise the build accordingly).** `Mathlib.MeasureTheory.Integral.CurveIntegral`
   has a full **contour-integral** theory `∫ᶜ x in γ, ω x` (`curveIntegral`) with `_trans`/`_symm`/`_refl`/
   `_add` (path concat + additivity), AND — contrary to the research note — **homotopy invariance of
   closed-form curve integrals**: `curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt` (Poincaré,
   proven via the unit-square pullback + the divergence theorem). It is for paths in a **normed space**
   `E` — i.e. *exactly the box setting* after pulling `ω` back via the cut chart. So steps 3–5 below
   should be rebuilt on `curveIntegral` + this Poincaré lemma (the boundary bookkeeping = `curveIntegral`
   additivity over `∂box` segments; relation I = Poincaré/closed-form). `Mathlib.Analysis.Complex.HasPrimitives`
   (`IsConservativeOn`/`IsExactOn`, Morera) is also available.

3. **`surfaceIntegral`** `∬_X β := ∬_{[0,1]²} (cut^* β)` for a 2-form `β`, + **pullback Green**
   `∬_X dα = ∮_{∂box}(cut^*α)` (from 1 + `extDeriv` commuting with pullback,
   `Mathlib.Analysis.Calculus.DifferentialForm`). [~300–600]

4. **`riemann_relation_I`** `∑_k (A_{lk}B_{jk} − B_{lk}A_{jk}) = 0`: `f_j ω_l` is a *closed* 1-form
   on `S₀` (`d(f_jω_l)=ω_j∧ω_l=0`, wedge of holomorphic `(1,0)`-forms in complex-dim 1), so
   `∮_{∂box} cut^*(f_jω_l) = ∬ d = 0`; boundary bookkeeping gives the relation. [~400–800]

5. **`riemann_relation_positivity`** `i∑_k(A_{jk}\overline{B_{jk}} − B_{jk}\overline{A_{jk}}) > 0`
   (sign per the `g=1` validation; `−i` would be the negative-definite form).
   - ✅ **Green positivity bridge DONE** (`Jacobians/GreenPositivity.lean`, `integral_normSq_eq_boundary`,
     axiom-clean): for holomorphic `h` on `U⊇[0,1]²` with primitive `F`,
     `∬_box ‖h‖² = −(i/2)·∮_{∂box} F̄ h dz`. (pointwise `d(F̄ h dz)=2i‖h‖²` + `greenOnUnitBox`.)
   - **next:** `∬_box ‖h‖² > 0` for `h` holomorphic `≢ 0` (`setIntegral_pos` + isolated zeros ⟹
     zero set measure-zero); then `cut^*ω = h dz` (cut chart) makes `∮_{∂box} F̄ h dz` the period
     bilinear sum (step 3/the boundary word). [remaining ~400]

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
