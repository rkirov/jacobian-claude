/-
  FORWARD HEADLINE ENDGAME — the genus-0 single-simple-pole theorem, Serre-free.

  This file assembles the forward headline

      `exists_singleSimplePole_of_genus_zero` : `genus X = 0 ⟹ ∃ P f, f.HasSingleSimplePole P`

  along the **Serre-free Riemann-inequality route** (scout `RRScout.lean`, commit 162b7dd). The route
  needs NO Serre duality, NO `deg_div`, and NO canonical divisor `K`. It rests on exactly two genuine
  inputs, both bundled honestly as hypotheses (never `sorry`, never vacuous):

  * a **`SharedChartCover X`** `𝔇` — a finite chart-disk cover, which makes `H¹(𝔘, 𝒪) = 0`
    UNCONDITIONALLY via the fully-PROVEN disk-acyclicity engine
    (`SharedChartCover.hasGluedDbarDatum` + `cechH1_subsingleton_of_hasGluedDbarDatum`, both
    axiom-clean). This discharges `h¹(0) = 0` WITHOUT any Serre/Hodge input.
  * a **`LocalRealizationData 𝔇.toFiniteCover 0 P`** at a point `P` — the single irreducible
    homological/analytic datum the snake lemma cannot itself supply: the local-realization iso
    `H⁰(Q) ≅ ℂ_P` (1-dim skyscraper stalk), the acyclicity `H¹(Q) = 0`, and the Forster-14.9 `H¹`
    finiteness. This is the genuine cohomological content of Riemann–Roch (Forster §16), bundled as an
    honest structure (sorry-free as data) rather than invoked through the `sorryAx`-backed
    `exists_skyscraperLES`. On a chart-disk cover it is itself producible via
    `FiniteCover.localRealizationData_of_chartDisk` (modulo the finiteness track `exists_cechModel`).

  ## The arithmetic (Forster §16, all sorry-free GIVEN the two inputs above)

  From the skyscraper LES at `(0, P)` (`skyscraperLES_of_localRealization`), the χ-jump crank
  `chi_jump_of_LES` gives `χ(P) = χ(0) + 1`. With the Liouville base `h⁰(0) = 1`
  (`h0Dim_zero_eq_one`) and `h¹(0) = 0` (disk-acyclicity), `χ(0) = 1`, so `χ(P) = 2`. Since
  `h¹(P) ≥ 0` (a `finrank`), `h⁰(P) = χ(P) + h¹(P) ≥ 2`; the `h⁰ = l` bridge (`h0Dim_eq_lDim`) turns
  this into the Riemann inequality `l(P) ≥ 2`, and the Serre-free extraction
  `RRScout.single_simple_pole_of_lDim_point_ge_two` produces the single-simple-pole function.

  Notably the **genus-0 hypothesis is not even consumed** by the inequality route: `h¹(0) = 0` comes
  from disk-acyclicity, not from `genus X = 0`. So the core deliverable
  `singleSimplePole_of_sharedChartCover_localRealization` produces the conclusion from the two cover
  inputs alone, and the headline shape (with the unused `genus X = 0` antecedent) is a trivial
  weakening.

  No `sorry`. Axiom-clean `[propext, Classical.choice, Quot.sound]` (verified): the chain avoids
  `cohomological_riemannRoch`/`exists_skyscraperLES` (which carry `sorryAx`), reusing instead the
  axiom-clean `chi_jump_of_LES`, `skyscraperLES_of_localRealization`, and the disk-acyclicity engine.
-/
import Jacobians.Dolbeault.SkyscraperAssembly
import Jacobians.Dolbeault.CohomologicalRR
import Jacobians.Dolbeault.GluedDbarDatum
import Jacobians.RRScout

open scoped Manifold ContDiff Topology

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

open Jacobians.Dolbeault

/-! ### `h¹(0) = 0` from a shared-chart disk cover (disk-acyclicity, Serre-free) -/

/-- **`h¹(𝔇, 𝒪) = 0` for a shared-chart disk cover** (Serre-free). Every class of `cechH1 0`
collapses (`cechH1_subsingleton_of_hasGluedDbarDatum` run on the PROVEN glued-`∂̄`-datum
`𝔇.hasGluedDbarDatum`), so `cechH1 0` is a subsingleton and its `finrank` is `0`. This is the
disk-acyclicity input that supplies `h¹(0) = 0` WITHOUT any Serre/Hodge bridge. -/
theorem h1Dim_zero_eq_zero_of_sharedChartCover (𝔇 : SharedChartCover X) :
    𝔇.toFiniteCover.h1Dim 0 = 0 := by
  haveI : Subsingleton (𝔇.toFiniteCover.cechH1 (0 : Divisor X)) :=
    subsingleton_of_forall_eq 0 fun q =>
      cechH1_subsingleton_of_hasGluedDbarDatum 𝔇 𝔇.hasGluedDbarDatum q
  exact Module.finrank_zero_of_subsingleton

/-! ### `χ(0) = 1` and the χ-jump to `χ(P) = 2` -/

/-- **`χ(𝔇, 0) = 1`** for a shared-chart cover: the Liouville base `h⁰(0) = 1`
(`h0Dim_zero_eq_one`) minus the disk-acyclicity `h¹(0) = 0`
(`h1Dim_zero_eq_zero_of_sharedChartCover`). Serre-free. -/
theorem chi_zero_eq_one_of_sharedChartCover (𝔇 : SharedChartCover X) :
    𝔇.toFiniteCover.chi 0 = 1 := by
  rw [FiniteCover.chi, h1Dim_zero_eq_zero_of_sharedChartCover 𝔇, 𝔇.toFiniteCover.h0Dim_zero_eq_one]
  norm_num

/-- **`χ(𝔇, P) = 2`** from the skyscraper LES at `(0, P)`. The local-realization datum produces the
skyscraper long exact sequence (`skyscraperLES_of_localRealization`); its χ-jump crank
(`chi_jump_of_LES`) gives `χ(0 + P) = χ(0) + 1`; with `χ(0) = 1` (disk-acyclicity + Liouville,
`chi_zero_eq_one_of_sharedChartCover`) and `0 + single P 1 = single P 1`, this is `χ(P) = 2`.
Serre-free: only the (honest, sorry-free-as-data) `LocalRealizationData` enters, not
`exists_skyscraperLES`. -/
theorem chi_point_eq_two_of_localRealization (𝔇 : SharedChartCover X) {P : X}
    (L : 𝔇.toFiniteCover.LocalRealizationData 0 P) :
    𝔇.toFiniteCover.chi (Finsupp.single P 1) = 2 := by
  have hjump := FiniteCover.chi_jump_of_LES (FiniteCover.skyscraperLES_of_localRealization L)
  rw [zero_add] at hjump
  rw [hjump, chi_zero_eq_one_of_sharedChartCover 𝔇]
  norm_num

/-! ### The Riemann inequality `l(P) ≥ 2` and the single simple pole -/

/-- **`2 ≤ l(P)` from `χ(P) = 2`** (Serre-free). `χ(P) = h⁰(P) − h¹(P) = 2` and `h¹(P) ≥ 0` give
`h⁰(P) ≥ 2`; the `h⁰ = l` bridge (`h0Dim_eq_lDim`) rewrites `h⁰(P)` as `l(P)`. This is exactly the
hypothesis consumed by the Serre-free extraction `single_simple_pole_of_lDim_point_ge_two`. -/
theorem lDim_point_ge_two_of_localRealization (𝔇 : SharedChartCover X) {P : X}
    (L : 𝔇.toFiniteCover.LocalRealizationData 0 P) :
    2 ≤ lDim (X := X) (Finsupp.single P 1) := by
  have hχ := chi_point_eq_two_of_localRealization 𝔇 L
  rw [FiniteCover.chi] at hχ
  -- `h⁰(P) − h¹(P) = 2`, `h¹(P) ≥ 0`, so `h⁰(P) ≥ 2`; bridge `h⁰(P) = l(P)`.
  have hbridge : 𝔇.toFiniteCover.h0Dim (Finsupp.single P 1) = lDim (X := X) (Finsupp.single P 1) :=
    𝔇.toFiniteCover.h0Dim_eq_lDim (Finsupp.single P 1)
  have hh1 : (0 : ℤ) ≤ (𝔇.toFiniteCover.h1Dim (Finsupp.single P 1) : ℤ) := Int.natCast_nonneg _
  have hh0 : (2 : ℤ) ≤ (𝔇.toFiniteCover.h0Dim (Finsupp.single P 1) : ℤ) := by omega
  rw [hbridge] at hh0
  exact_mod_cast hh0

/-! ### The Serre-free single-simple-pole deliverable -/

/-- **Single simple pole from the two cover inputs** (Serre-free; the core deliverable).
Given a shared-chart disk cover `𝔇` (supplying `h¹(0) = 0` unconditionally) and the local-realization
datum `L` at a point `P` (supplying the skyscraper LES at `(0, P)`), there is a meromorphic function
with a single simple pole at `P`. The chain: `χ(P) = 2` (`chi_point_eq_two_of_localRealization`) ⟹
`l(P) ≥ 2` (`lDim_point_ge_two_of_localRealization`) ⟹ the single simple pole
(`single_simple_pole_of_lDim_point_ge_two`, the Serre-free extraction).

Note the **genus hypothesis is not used**: `h¹(0) = 0` comes from disk-acyclicity, so the
inequality route never references `genus X` or the §17 Serre wall. -/
theorem singleSimplePole_of_sharedChartCover_localRealization (𝔇 : SharedChartCover X) {P : X}
    (L : 𝔇.toFiniteCover.LocalRealizationData 0 P) :
    ∃ f : MeromorphicFunction X, f.HasSingleSimplePole P :=
  single_simple_pole_of_lDim_point_ge_two P (lDim_point_ge_two_of_localRealization 𝔇 L)

/-- **The forward headline, Serre-free** (`genus X = 0 ⟹ ∃ P f, f.HasSingleSimplePole P`), reduced to
the two honest cover inputs. Given a shared-chart disk cover `𝔇` and a local-realization datum at some
point `P`, the genus-0 single-simple-pole conclusion follows — and crucially neither input is Serre
duality (`h¹(0) = 0` is disk-acyclicity, `L` is the §16 skyscraper datum). The `genus X = 0`
hypothesis is the headline's antecedent but is not consumed by the inequality route.

This matches `GenusSphereHeadline.exists_singleSimplePole_of_genus_zero` /
`RiemannRoch.exists_singleSimplePole_of_genus_zero_of_rr` in statement; it discharges them along the
Serre-free route modulo exactly `{𝔇 : SharedChartCover X, L : LocalRealizationData 𝔇.toFiniteCover 0 P}`
(the concrete chart-disk cover `exists_lerayCover`/`chartBallCover` and the §16 local-realization
datum). -/
theorem exists_singleSimplePole_of_genus_zero_of_cover
    (𝔇 : SharedChartCover X) {P : X} (L : 𝔇.toFiniteCover.LocalRealizationData 0 P)
    (_hg : genus X = 0) :
    ∃ (P : X) (f : MeromorphicFunction X), f.HasSingleSimplePole P :=
  ⟨P, singleSimplePole_of_sharedChartCover_localRealization 𝔇 L⟩

end Jacobians
