# `finiteDimensional_cechH1` (G3b, Forster 14.9) — research + build plan

Research for the **next ladder node** after the `h0Dim_eq_lDim` bridge: proving
`FiniteDimensional ℂ (𝔘.cechH1 D)` (Forster *Lectures on Riemann Surfaces* Thm 14.9). Done while
the gluing/surjectivity agent finishes the bridge leaf. Companion to `docs/dolbeault_ladder_derisk.md`
(which flagged this node as the biggest unmeasured risk: the germ-class vs sup-norm representation clash).

## Headline verdict — TEMPLATED, not greenfield

The de-risk feared finiteness was a ~800–1500 LoC greenfield analytic build. **It is largely a
*reuse* of the repo's existing Ω(X) Montel finiteness** (`Jacobians/Montel*`, ~95% done), which proves
the *same shape* of theorem (`FiniteDimensional ℂ (HolomorphicOneForms X)`) by the *same method*
(Montel ⟹ compact ⟹ Riesz). The "germ-vs-sup-norm clash" is resolved the way the repo already
resolved it for Ω(X): put a sup-norm on the analytic object, embed into bounded-continuous-functions
on an inner shrinking, Arzelà–Ascoli compactness, Riesz finite-dimensionality.

## What the repo ALREADY has (big reuse)

- **The nested triple cover** = Forster's `𝔘 ⋐ 𝔙` shrinking, *already built* (`Montel/Cover.lean`):
  `coverOpen x ⊇ chartOpen x ⊇ innerChartOpen x` with closures nested
  `innerShrunkChart ⊆ chartOpen ⊆ shrunkChart ⊆ coverOpen`. This is the "wiggle room" that makes the
  restriction map compact (bounded on the outer disk ⟹ relatively compact on the strictly-inner one).
- **Disk-level Montel** (`Montel/Compactness.lean`, ~1000 LoC, all proven):
  `uniformEquicontinuousOn_of_bounded_analyticOn`, `equicontinuous_localRep_inner_family`,
  `isCompact_univ_pi_closure_image_inner_bcf` (Arzelà–Ascoli on the bcf embedding),
  `analyticOn_of_pullback_tendsto_locally_uniformly` (locally-uniform limit of holomorphic is
  holomorphic), `exists_cauchy_deriv_bound` (Cauchy estimates). These are about holomorphic functions
  on chart disks — **directly the objects a `𝒪_D`-cochain restriction is built from.**
- **The sup-norm + bcf + Riesz pattern** (`Montel.lean`, `HolomorphicForms.lean`):
  `supNormK`/`supNormKAsAddGroupNorm` → `NormedAddCommGroup`, `embedInnerBcf : HOF →L bcf`,
  `closedBall_isCompact`, and the finish `FiniteDimensional.of_isCompact_closedBall₀ ℂ zero_lt_one`.
  This is exactly the Riesz "compact unit ball ⟹ finite-dim" endgame.
- **∂̄ on a disk** (`DbarDisk.lean`, G1, axiom-clean) — needed for the Leray vanishing
  `H¹(disk, 𝒪) = 0` (a chart-disk cover is then Leray, so `H¹(𝔘) = H¹(X)`).

## Mathlib inventory (verified at pin `8e3c989`, this session)

| Capability | Status | Name / note |
|---|---|---|
| `IsCompactOperator` + full API (comp, closed ideal, limits, closed-ball char) | **PRESENT** | `Analysis/Normed/Operator/Compact.lean` |
| Riesz lemma | **PRESENT** | `riesz_lemma`, `riesz_lemma_of_norm_lt` (`…/RieszLemma.lean`) |
| Fredholm alternative (spectral form) | **PRESENT** | `hasEigenvalue_or_mem_resolventSet`, `antilipschitz_of_not_hasEigenvalue` (`…/FredholmAlternative.lean`) |
| Arzelà–Ascoli | **PRESENT** | `Topology/UniformSpace/Ascoli.lean` |
| Riesz finite-dim from compact unit ball | **PRESENT** | `FiniteDimensional.of_isCompact_closedBall₀` (repo already uses it) |
| **"surjective + compact perturbation ⟹ finite codim" (Schwartz/Forster 14.8)** | **ABSENT** | the one genuinely-missing functional-analysis lemma |
| Banach space of holomorphic functions (sup-norm) | **ABSENT in Mathlib / PRESENT in repo** | repo's `supNormK`/bcf pattern fills it |
| coherent-sheaf / Cartan–Serre finiteness | **ABSENT** | (expected) |

## The two genuinely-new pieces (the residual risk)

1. **Schwartz's finiteness lemma** (Forster 14.8): for Fréchet/Banach `E, F`, `u : E → F` surjective
   continuous and `v : E → F` compact, `(u − v)(E)` has finite codimension in `F`. Mathlib has the
   ingredients (Riesz, compact-operator API, antilipschitz-from-Fredholm) but **not** the packaged
   statement. ~100–300 LoC. **Why it (rather than the cleaner Riesz route) is needed:** the naive Riesz
   route ("unit ball of `H¹` compact ⟹ finite-dim") presumes `H¹` is *Hausdorff*, i.e. `B¹ = im δ⁰` is
   *closed* — but closedness of `B¹` is itself a consequence of finiteness (circular). Forster's
   Schwartz lemma gives finite codim of the *image* directly, sidestepping a-priori closedness. So the
   robust route is the Schwartz lemma, not bare Riesz.
2. **The Leray / two-cover setup**: restriction `Z¹(𝔙) → Z¹(𝔘)` (𝔘 a shrinking of 𝔙) is **compact**
   (disk-Montel, reuse) and induces a surjection on `H¹` (chart-disks are Leray via the G1 ∂̄-disk
   vanishing). Feed `(restriction, δ⁰)` into the Schwartz lemma ⟹ `H¹(𝔘)` finite-dim. The Leray
   refinement bookkeeping (Čech, `H¹(disk)=0`) is real work but G1 is done.

## Representation fork (the clash, resolved)

- The **germ-class rep** (current `cechH1`, `Filter.Germ` over codiscrete) is the *right* rep for
  `h⁰` (junk-free, a plain finrank), the `h0Dim_eq_lDim` bridge, and the χ-additivity bookkeeping.
- The **sup-norm honest-function rep** (holomorphic functions on shrunk disk-intersections, `supNormK`)
  is the *right* rep for the finiteness/Montel argument.
- **Recommendation:** do NOT re-found on one rep. Run finiteness in the sup-norm rep, then prove a
  **comparison** `𝔘.cechH1 D (germ) ≃ₗ cechH1 D (sup-norm/honest)` (equal finrank suffices). The
  comparison is bounded: germ-classes and honest sections differ only by codiscrete junk, which does
  not change `H¹` (the same codiscrete↔𝓝[≠] bridge already proven in `CechH0`). This comparison is the
  price of the dual rep; it is *much* cheaper than re-deriving `h⁰`/χ in a topological rep.

## Recommended build sub-order

0. (G2 ∂̄-globalization is **not** needed here — finiteness uses only G1 ∂̄-*disk*. Defer G2 to the
   Serre node.)
1. `𝒪_D`-cochain sup-norm rep on the nested cover (reuse `supNormK`/bcf pattern). Sections of `𝒪_D`
   on a disk are meromorphic with `D`-bounded poles; clear the pole by the local factor, or reduce to
   `D = 0` first (the skyscraper twist handles general `D` downstream). **Start with `D = 0`.**
2. Compact restriction `C^q(𝔙) → C^q(𝔘)` (reuse disk-Montel `isCompact_…_inner_bcf`). *Likely easier
   than the repo's open Ω(X) sorry `exists_convergent_subseq_of_bounded` — cochains are plain functions
   on overlaps, with no cotangent-bundle reconstruction.*
3. Schwartz finiteness lemma (new, from Mathlib Riesz/compact API).
4. Leray surjection on `H¹` (G1 ∂̄-disk) + feed Schwartz ⟹ `H¹(𝔘, 𝒪)` finite-dim.
5. Comparison germ-rep ↔ sup-norm-rep ⟹ `FiniteDimensional ℂ (𝔘.cechH1 0)`; then general `D`.

## Net for the plan

Finiteness is **medium-large but de-risked**: dominated by reuse of the repo's HOF Montel + the
already-built nested cover + disk-Montel + G1. The dominant *new* risks are (i) the Schwartz
finite-codim lemma (bounded functional analysis) and (ii) the Leray/closed-range bookkeeping. The
representation clash is real but resolved by a cheap comparison iso, not a re-foundation. This
confirms the de-risk's `~800–1500 LoC, Med` estimate and lowers its variance. See
`docs/dolbeault_ladder_derisk.md`, `docs/riemann_roch_proof_plan.md §2`.
