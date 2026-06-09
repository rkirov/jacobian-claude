/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueRamifiedCenter
import Jacobians.Dolbeault.FormTracePrincipalPart

/-!
# The ramified geometric-trace identification `hcoh` (Forster §5 `z = wᵐ` normal form)

This file builds the genuine geometric content of `RamifiedCenterFacts.hcoh`
(`Jacobians/Dolbeault/SerreResidueRamifiedCenter.lean`): at a (possibly ramified) finite pole-value
centre `c` of `α = ω₀·g`, the **geometric** value-chart trace germ `valueChartTrace ω₀ f Φ` near `c`
*is* the **algebraic** `m`-sheet-sum trace of the per-preimage chart integrands.  It is the ramified
analogue of `exists_planar_section` (`FormTraceFibre.lean`, the unramified local biholomorphism that
identifies the geometric chart with the value chart), now for a ramification point of multiplicity
`m`, where the cover is the branched normal form `z = wᵐ` (Forster GTM 81, §5).

## The geometry (Miranda §VIII.3, Forster §5)

Near a ramification point `p` of multiplicity `m` over `c`, choose the centered chart `w = chart_p` at
`p` and the value coordinate `z` at `c`.  Forster §5: the cover reads `z − c = (w − w_p)ᵐ` after a
biholomorphic change.  For `z` near `c` (`z ≠ c`) the fibre splits into the `m` distinct unramified
sheets `w = w_p + ζʲ·w₀(z)` (`ζ` a primitive `m`-th root of unity, `w₀` a holomorphic branch of
`(z − c)^{1/m}`).  The value-chart trace `Tr_F α` over those `m` sheets is the `m`-sheet sum

> `∑_{j<m} h(w_p + ζʲ w₀(z)) · (d/dz)[w_p + ζʲ w₀(z)]`,    `h := chartIntegrand ω₀ g p`,

with `(d/dz)[w_p + ζʲ w₀(z)] = ζʲ w₀'(z) = ζʲ·(1/m) w₀(z)^{1−m}` (from `m w₀^{m−1} w₀' = 1`).  By the
proven roots-of-unity collapse (`Jacobians.RamifiedTrace.laurentTraceCoeff_eq_sheetSum`) this `m`-sheet
sum, applied to the **Laurent principal part** of `h` at `w_p`, equals the closed-form
`laurentTraceCoeff (z − c)` — exactly the algebraic `ramifiedTraceTerm` whose residue is the upstairs
residue (`resAt_laurentTraceCoeff`).  The holomorphic remainder of `h` contributes a holomorphic trace,
which the residue does not see.

## What this file delivers

* **`RamifiedSheetData`** (the genuine geometric input, the ramified analogue of the
  `exists_planar_section` *output*): at one preimage `p`, the multiplicity `m`, a primitive `m`-th root
  `ζ`, a holomorphic branch `w₀` of `(z − c)^{1/m}` on `𝓝[≠] c` (the **Forster §5 analytic atom**: the
  branched-cover `m`-th root), and the **geometric identification** `hgeom` that the geometric trace
  germ near `c` is the `m`-sheet sum read in `p`'s chart.  This is supplied as *data* — never asserted
  as a free lemma — exactly as the unramified moving coherence `MovingCoherenceDatum` is supplied as
  data (its monodromy bijection `hbij` is the unramified counterpart of `hgeom`).

* **`ramifiedSheetSum_eventuallyEq_laurentTraceTerm`** (the genuine new analytic content, FULLY
  PROVEN): from `RamifiedSheetData` the geometric `m`-sheet trace germ equals
  `ramifiedTraceTerm (principal part of h) m c + (analytic remainder trace)` on `𝓝[≠] c`.  This is the
  ramified Lemma 3.2 *at the level of the geometric sheet sum* — the roots-of-unity collapse
  (`laurentTraceCoeff_eq_sheetSum`) plus the principal-part split (`exists_principalPart_meromorphicAt`).

* **`RamifiedCenterFacts.ofSheetData`** (the sound capstone): assembles a `RamifiedCenterFacts` whose
  carried trace `T` is the *full* geometric `m`-sheet trace (NOT just the principal part), with `hcoh`
  the genuine geometric identification and `hmero`/`hres` discharged via the split + the proven atom.
  Unlike `RamifiedCenterFacts.ofFibreRamified` (whose `T := ramifiedTraceTerm` forces the FALSE
  "full trace = principal-part trace" `hcoh`), this constructor's `hcoh` is TRUE — `T` is the honest
  full trace.  Single-preimage form; the mixed-multiplicity fibre is the obvious sum.

## ⚠ Soundness

* `T` is the **full** geometric `m`-sheet trace, so `hcoh` is the genuine punctured germ-equality
  `valueChartTrace =ᶠ[𝓝[≠] c] T` (TRUE — no "principal part = full trace" junk).  `hmero`/`hres` are
  derived by *splitting* `T` into principal part (atom) + analytic remainder (residue `0`), never by
  asserting the remainder vanishes.
* Every trace statement is the `m`-sheet **SUM** (the atom's roots-of-unity factor `∑(ζʲ)⁰ = m`
  cancels the chain-rule `1/m`); there is no single-sheet "`m·Res`" shortcut (the false 9th field —
  absent).
* `hgeom` (geometric trace = `m`-sheet sum read in `p`'s chart) and the branch `w₀` are the GENUINE
  Forster §5 content, supplied as `RamifiedSheetData` *data*, not asserted.  At an unramified preimage
  (`m = 1`, `ζ = 1`, `w₀(z) = z − c`) the sheet sum reduces to the single planar section term — the
  `exists_planar_section` germ.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §5 (local normal form `z = wᵐ`).
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3, (3.1), Lemma 3.2 ramified case.
* `Jacobians/RamifiedResidueChangeOfVariables.lean` (`laurentTraceCoeff_eq_sheetSum`, the atom).
* `Jacobians/Dolbeault/FormTraceFibre.lean` (`exists_planar_section`, the unramified template).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTracePrincipalPart
  Jacobians.RamifiedTrace

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The Forster §5 normal-form sheet data (the genuine geometric input)

`RamifiedSheetData` packages, at one preimage `p` of multiplicity `m` over a centre `c`, the Forster
§5 local normal-form geometry as *data* (the ramified analogue of the `exists_planar_section` output):
a primitive `m`-th root `ζ`, a holomorphic branch `w₀` of `(z − c)^{1/m}` on a punctured neighbourhood
of `c`, the chain-rule identity for `w₀`, and — the geometric core — that the value-chart trace germ
near `c` is the `m`-sheet sum of the chart integrand of `α = ω₀·g` at `p`, read along the `m` sheets
`w = w_p + ζʲ w₀(z)`.  Everything else (the residue/meromorphy/`hcoh`) is *derived*. -/

/-- **Forster §5 ramified sheet data at one preimage.**  At a preimage `p` of multiplicity `m ≥ 1`
over the centre `c`, with chart coordinate `wp := chart_p p`:

* `ζ` a primitive `m`-th root of unity;
* `w₀ : ℂ → ℂ` a holomorphic branch of `(z − c)^{1/m}` on `𝓝[≠] c` (`hw₀_an`), nonvanishing there
  (`hw₀_ne`), with `w₀(z)ᵐ = z − c` (`hw₀_pow`) and the chain-rule derivative `w₀'(z) = (1/m) w₀^{1−m}`
  (`hw₀_deriv`) — the **Forster §5 analytic atom** (the branched-cover `m`-th root);
* the **geometric identification** `hgeom`: the value-chart trace germ `valueChartTrace ω₀ f Φ` equals,
  on `𝓝[≠] c`, the `m`-sheet sum `∑_{j<m} h(wp + ζʲ w₀(z))·(d/dz)[wp + ζʲ w₀(z)]` of the chart
  integrand `h := chartIntegrand ω₀ g p`.

This is the genuine §VIII.3 / Forster §5 content, supplied as *data* (as the unramified
`MovingCoherenceDatum` is), never asserted as a free lemma; the residue identity, meromorphy, and the
abstract `hcoh` are all *derived* from it (`RamifiedCenterFacts.ofSheetData`). -/
structure RamifiedSheetData (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (c : ℂ) where
  /-- The ramification preimage over `c`. -/
  p : X
  /-- The ramification multiplicity (`≥ 1`). -/
  m : ℕ
  /-- The multiplicity is positive. -/
  hm : 0 < m
  /-- A primitive `m`-th root of unity (the sheet rotation). -/
  ζ : ℂ
  /-- `ζ` is a primitive `m`-th root of unity. -/
  hζ : IsPrimitiveRoot ζ m
  /-- The holomorphic branch of `(z − c)^{1/m}`. -/
  w₀ : ℂ → ℂ
  /-- The branch is analytic on a punctured neighbourhood of `c`. -/
  hw₀_an : ∀ᶠ z in 𝓝[≠] c, AnalyticAt ℂ w₀ z
  /-- The branch is nonzero off `c`. -/
  hw₀_ne : ∀ᶠ z in 𝓝[≠] c, w₀ z ≠ 0
  /-- The branch tends to `0` at `c` (`(z − c)^{1/m} → 0`). -/
  hw₀_tendsto : Tendsto w₀ (𝓝[≠] c) (𝓝 0)
  /-- The branch is an `m`-th root: `w₀(z)ᵐ = z − c`. -/
  hw₀_pow : ∀ᶠ z in 𝓝[≠] c, w₀ z ^ (m : ℤ) = z - c
  /-- The chain-rule derivative `w₀'(z) = (1/m) w₀(z)^{1−m}` (from `m w₀^{m−1} w₀' = 1`). -/
  hw₀_deriv : ∀ᶠ z in 𝓝[≠] c, deriv w₀ z = (m : ℂ)⁻¹ * w₀ z ^ (1 - (m : ℤ))
  /-- `g`'s chart-pullback is meromorphic at `p`'s chart centre (so the chart integrand of `α = ω₀·g`
  has an isolated singularity — true since `p` is an isolated pole of `α`). -/
  hg_mero : MeromorphicAt (fun z => g ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p)
  /-- **The geometric trace identification** (Forster §5): the value-chart trace germ near `c` is the
  `m`-sheet sum of the chart integrand of `α = ω₀·g` at `p`, read along `w = wp + ζʲ w₀(z)`. -/
  hgeom : valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] c]
    fun z => ∑ j ∈ Finset.range m,
      chartIntegrand ω₀ g p ((chartAt ℂ p) p + ζ ^ j * w₀ z)
        * deriv (fun ζz => (chartAt ℂ p) p + ζ ^ j * w₀ ζz) z
  /-- **Trace of holomorphic is holomorphic** (Forster §5): the `m`-sheet sum along `w = wp + ζʲ w₀(z)`
  of any function `R` analytic at `wp = chart_p p` is analytic at `c`.  This is the standard fact that
  the trace of a *holomorphic* form along the branched cover is holomorphic (the residue does not see
  the holomorphic part); it is genuinely true and supplied as part of the Forster §5 normal-form
  package (the symmetric-function descent of `∑_j R(ζʲ w₀)` to a holomorphic function of
  `w₀ᵐ = z − c`).  It discharges the analytic-remainder trace in the principal-part split. -/
  hrem_an : ∀ R : ℂ → ℂ, AnalyticAt ℂ R ((chartAt ℂ p) p) →
    AnalyticAt ℂ (fun z => ∑ j ∈ Finset.range m,
      R ((chartAt ℂ p) p + ζ ^ j * w₀ z)
        * deriv (fun ζz => (chartAt ℂ p) p + ζ ^ j * w₀ ζz) z) c

/-! ### The sheet-`j` derivative `(d/dz)[wp + ζʲ w₀(z)] = ζʲ w₀'(z)`

The sheet `z ↦ wp + ζʲ w₀(z)` has derivative `ζʲ w₀'(z)` wherever `w₀` is differentiable: it is the
constant `wp` plus the scalar `ζʲ` times `w₀`. -/

/-- The sheet-`j` derivative.  `(d/dz)[wp + ζʲ w₀(z)] = ζʲ · w₀'(z)` (unconditional: constant `wp`
plus the field scalar `ζʲ` times `w₀`). -/
theorem deriv_sheet_eq (w₀ : ℂ → ℂ) (z wp ζj : ℂ) :
    deriv (fun ζz => wp + ζj * w₀ ζz) z = ζj * deriv w₀ z := by
  have h1 : deriv (fun ζz => wp + ζj * w₀ ζz) z = deriv (fun ζz => ζj * w₀ ζz) z :=
    deriv_const_add (f := fun ζz => ζj * w₀ ζz) wp
  rw [h1, deriv_const_mul_field]

/-! ### The planar `m`-sheet trace of a Laurent polynomial integrand (the atom, on the geometry)

The reusable algebraic core: when the chart integrand near `wp` is the Laurent polynomial
`W ↦ ∑_i cf_i (W − wp)^{n_i}`, its `m`-sheet sum along `w = wp + ζʲ w₀(z)` is exactly the closed-form
`laurentTraceCoeff (z − c) = ramifiedTraceTerm`, by the proven roots-of-unity collapse
`laurentTraceCoeff_eq_sheetSum`.  The branch `w₀` (`w₀ ≠ 0`, `w₀ᵐ = z − c`, `w₀' = (1/m) w₀^{1−m}`)
turns the geometric sheet sum into the atom's LHS verbatim. -/

/-- **The geometric `m`-sheet sum of a Laurent-polynomial integrand is `ramifiedTraceTerm`.**  For the
Laurent polynomial integrand `hpoly W := ∑_{i ∈ s} cf_i (W − wp)^{n_i}` and the branch `w₀` at `z`
(`w₀ z ≠ 0`, `w₀(z)ᵐ = z − c`, `w₀'(z) = (1/m) w₀(z)^{1−m}`, `ζ` a primitive `m`-th root), the
`m`-sheet sum `∑_{j<m} hpoly(wp + ζʲ w₀(z))·(d/dz)[wp + ζʲ w₀(z)]` equals
`ramifiedTraceTerm s cf n m c z`.  Pure algebra: substitute `W − wp = ζʲ w₀(z)` and the chain-rule
derivative, then apply the atom's soundness identity `laurentTraceCoeff_eq_sheetSum`. -/
theorem ramifiedSheetSum_laurentPoly {ι : Type*} (s : Finset ι) (cf : ι → ℂ) (n : ι → ℤ) {m : ℕ}
    (hm : 0 < m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m) {w₀ : ℂ → ℂ} {z wp c : ℂ}
    (hne : w₀ z ≠ 0) (hpow : w₀ z ^ (m : ℤ) = z - c)
    (hderiv : deriv w₀ z = (m : ℂ)⁻¹ * w₀ z ^ (1 - (m : ℤ))) :
    (∑ j ∈ Finset.range m, (∑ i ∈ s, cf i * (wp + ζ ^ j * w₀ z - wp) ^ n i)
        * deriv (fun ζz => wp + ζ ^ j * w₀ ζz) z)
      = ramifiedTraceTerm s cf n m c z := by
  -- Rewrite each summand: `(wp + ζʲ w₀ − wp) = ζʲ w₀`, and the derivative `= ζʲ·(1/m) w₀^{1−m}`.
  have hstep : ∀ j ∈ Finset.range m,
      (∑ i ∈ s, cf i * (wp + ζ ^ j * w₀ z - wp) ^ n i)
          * deriv (fun ζz => wp + ζ ^ j * w₀ ζz) z
        = (∑ i ∈ s, cf i * (ζ ^ j * w₀ z) ^ n i)
          * (ζ ^ j * ((m : ℂ)⁻¹ * w₀ z ^ (1 - (m : ℤ)))) := by
    intro j _
    rw [deriv_sheet_eq w₀ z wp (ζ ^ j), hderiv, add_sub_cancel_left]
  rw [Finset.sum_congr rfl hstep]
  -- The atom's soundness identity, evaluated at the branch `w₀ z` (`= (z − c)^{1/m}`).
  rw [laurentTraceCoeff_eq_sheetSum s cf n hm hζ (w₀ z) hne]
  -- `laurentTraceCoeff … (w₀ zᵐ) = laurentTraceCoeff … (z − c) = ramifiedTraceTerm … z`.
  rw [hpow]
  rfl

/-! ### The principal-part split of the geometric sheet sum (the genuine ramified Lemma 3.2)

From the sheet data `S`, the geometric `m`-sheet trace germ (= `valueChartTrace`) decomposes on a
punctured neighbourhood of `c` as `ramifiedTraceTerm (principal part of the chart integrand) + (the
sheet sum of the analytic remainder)`.  The first term is the algebraic `m`-sheet-sum trace (meromorphic,
residue = upstairs residue, by the proven atom); the second is analytic at `c` (`hrem_an`).  Hence the
full trace is meromorphic at `c` with residue the upstairs residue — the ramified Lemma 3.2. -/

namespace RamifiedSheetData

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
  {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ}

/-- The geometric `m`-sheet trace germ carried as `T` (the RHS of `hgeom`): the honest *full* trace,
`∑_{j<m} h(wp + ζʲ w₀(z))·(d/dz)[wp + ζʲ w₀(z)]` with `h = chartIntegrand ω₀ g p`. -/
noncomputable def traceFull (S : RamifiedSheetData ω₀ g f Φ c) : ℂ → ℂ :=
  fun z => ∑ j ∈ Finset.range S.m,
    chartIntegrand ω₀ g S.p ((chartAt ℂ S.p) S.p + S.ζ ^ j * S.w₀ z)
      * deriv (fun ζz => (chartAt ℂ S.p) S.p + S.ζ ^ j * S.w₀ ζz) z

/-- `valueChartTrace` germ-equals the full geometric trace `traceFull` near `c` — exactly `hgeom`. -/
theorem hcoh (S : RamifiedSheetData ω₀ g f Φ c) :
    valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] c] S.traceFull := S.hgeom

/-- The chart integrand of `α = ω₀·g` at the preimage `p`, the per-sheet integrand `h`. -/
private noncomputable def hInt (S : RamifiedSheetData ω₀ g f Φ c) : ℂ → ℂ :=
  chartIntegrand ω₀ g S.p

private theorem hInt_mero (S : RamifiedSheetData ω₀ g f Φ c) :
    MeromorphicAt S.hInt ((chartAt ℂ S.p) S.p) :=
  meromorphicAt_chartIntegrand ω₀ g S.p S.hg_mero

/-- The sheet map `z ↦ wp + ζʲ w₀(z)` tends to `wp` *within `{≠ wp}`* along `𝓝[≠] c`: it tends to `wp`
(since `w₀ → 0`) and stays `≠ wp` (since `ζʲ ≠ 0` and `w₀ ≠ 0` off `c`).  This lets the integrand's
principal-part split (a `𝓝[≠] wp` germ-equality) pull back to the sheet points near `c`. -/
private theorem tendsto_sheet (S : RamifiedSheetData ω₀ g f Φ c) (j : ℕ) :
    Tendsto (fun z => (chartAt ℂ S.p) S.p + S.ζ ^ j * S.w₀ z) (𝓝[≠] c)
      (𝓝[≠] ((chartAt ℂ S.p) S.p)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · -- Tendsto to `wp`: `wp + ζʲ·w₀ → wp + ζʲ·0 = wp`.
    have h0 : Tendsto (fun z => (chartAt ℂ S.p) S.p + S.ζ ^ j * S.w₀ z) (𝓝[≠] c)
        (𝓝 ((chartAt ℂ S.p) S.p + S.ζ ^ j * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul S.hw₀_tendsto)
    simpa using h0
  · -- Eventually `≠ wp`: `ζʲ·w₀ z ≠ 0`.
    have hζj : S.ζ ^ j ≠ 0 := pow_ne_zero j (S.hζ.ne_zero S.hm.ne')
    filter_upwards [S.hw₀_ne] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    -- `wp + ζʲ w₀ z = wp ⟹ ζʲ w₀ z = 0 ⟹ w₀ z = 0`, contradiction.
    have hzero : S.ζ ^ j * S.w₀ z = 0 := by
      have := add_left_cancel (a := (chartAt ℂ S.p) S.p) (b := S.ζ ^ j * S.w₀ z) (c := 0)
        (by rw [add_zero]; exact hcon)
      exact this
    exact hz (by simpa [hζj] using hzero)

/-! ### The principal-part split and the derived facts (A)/(B) -/

/-- **The principal-part split of the geometric trace** (the genuine ramified Lemma 3.2).  There are a
degree `N`, principal-part coefficients `b`, and an analytic remainder trace `Rem` (`AnalyticAt ℂ Rem
c`) such that on `𝓝[≠] c` the full geometric trace splits as

> `traceFull = ramifiedTraceTerm (Icc 1 N) b (k ↦ −k) m c  +  Rem`,

with the residue of the `ramifiedTraceTerm` part equal to the upstairs residue `formFnResidue ω₀ g p`.
The `ramifiedTraceTerm` part is the `m`-sheet sum of the integrand's Laurent **principal part** (the
proven atom on the geometry, `ramifiedSheetSum_laurentPoly`); `Rem` is the `m`-sheet sum of the
integrand's analytic remainder (analytic at `c` by `hrem_an`). -/
theorem exists_split (S : RamifiedSheetData ω₀ g f Φ c) :
    ∃ (N : ℕ) (b : ℕ → ℂ) (Rem : ℂ → ℂ), AnalyticAt ℂ Rem c ∧
      S.traceFull =ᶠ[𝓝[≠] c]
        (fun z => ramifiedTraceTerm (Finset.Icc 1 N) b (fun k => -(k : ℤ)) S.m c z + Rem z) ∧
      resAt (ramifiedTraceTerm (Finset.Icc 1 N) b (fun k => -(k : ℤ)) S.m c) c
        = formFnResidue ω₀ g S.p := by
  classical
  set wp := (chartAt ℂ S.p) S.p with hwp
  -- Principal part of the chart integrand `h = hInt` at `wp`.
  obtain ⟨N, b, R, hR_an, hR_eq⟩ := exists_principalPart_meromorphicAt S.hInt_mero
  -- The Laurent-poly form of `negTail wp b N` (centred at `wp`), as the atom's integrand.
  set Rem : ℂ → ℂ := fun z => ∑ j ∈ Finset.range S.m,
    R (wp + S.ζ ^ j * S.w₀ z) * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z with hRem
  refine ⟨N, b, Rem, S.hrem_an R hR_an, ?_, ?_⟩
  · -- The germ split.  Pull the integrand split `hR_eq` back along each of the `m` sheet maps.
    -- Eventually (on `𝓝[≠] c`): every sheet point satisfies the integrand split AND `w₀ z ≠ 0` etc.
    have hsheets : ∀ᶠ z in 𝓝[≠] c, ∀ j ∈ Finset.range S.m,
        S.hInt (wp + S.ζ ^ j * S.w₀ z)
          = negTail wp b N (wp + S.ζ ^ j * S.w₀ z) + R (wp + S.ζ ^ j * S.w₀ z) := by
      rw [eventually_all_finset]
      intro j _
      exact (hR_eq.comp_tendsto (S.tendsto_sheet j))
    filter_upwards [hsheets, S.hw₀_ne, S.hw₀_pow, S.hw₀_deriv, self_mem_nhdsWithin]
      with z hz hne hpow hderiv _
    -- Goal: `traceFull z = ramifiedTraceTerm … z + Rem z`.  Read `traceFull z` as a sum and split.
    show (∑ j ∈ Finset.range S.m,
        S.hInt (wp + S.ζ ^ j * S.w₀ z) * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z)
      = ramifiedTraceTerm (Finset.Icc 1 N) b (fun k => -(k : ℤ)) S.m c z + Rem z
    -- Step 1: replace `hInt(sheet)` by `negTail(sheet) + R(sheet)`, distribute, regroup as
    -- `(negTail-trace) + (R-trace = Rem z)`.
    have hstep1 : (∑ j ∈ Finset.range S.m,
          S.hInt (wp + S.ζ ^ j * S.w₀ z) * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z)
        = (∑ j ∈ Finset.range S.m,
            negTail wp b N (wp + S.ζ ^ j * S.w₀ z) * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z)
          + Rem z := by
      rw [hRem, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [hz j hj]; ring
    -- Step 2: the negTail-trace is `ramifiedTraceTerm` via the proven atom.
    have hstep2 : (∑ j ∈ Finset.range S.m,
          negTail wp b N (wp + S.ζ ^ j * S.w₀ z) * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z)
        = ramifiedTraceTerm (Finset.Icc 1 N) b (fun k => -(k : ℤ)) S.m c z := by
      rw [show (∑ j ∈ Finset.range S.m,
            negTail wp b N (wp + S.ζ ^ j * S.w₀ z) * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z)
          = ∑ j ∈ Finset.range S.m,
            (∑ k ∈ Finset.Icc 1 N, b k * (wp + S.ζ ^ j * S.w₀ z - wp) ^ (-(k : ℤ)))
              * deriv (fun ζz => wp + S.ζ ^ j * S.w₀ ζz) z
        from Finset.sum_congr rfl (fun j _ => by rw [negTail])]
      exact ramifiedSheetSum_laurentPoly (Finset.Icc 1 N) b (fun k => -(k : ℤ)) S.hm S.hζ hne hpow
        hderiv
    rw [hstep1, hstep2]
  · -- The residue of the `ramifiedTraceTerm` part = upstairs residue = `formFnResidue ω₀ g p`.
    rw [resAt_ramifiedTraceTerm (Finset.Icc 1 N) b (fun k => -(k : ℤ)) S.hm c]
    -- `negTail wp b N` rewritten as `(Laurent poly centred at 0)(· − wp)`.
    have hnegtail_eq : (negTail wp b N)
        = fun w => (fun w' => ∑ k ∈ Finset.Icc 1 N, b k * (w' - 0) ^ (-(k : ℤ))) (w - wp) := by
      funext w; simp only [negTail, sub_zero]
    -- `resAt (Laurent poly of pp) 0 = resAt (negTail wp b N) wp` (shift-covariance).
    have hshift : resAt (fun w => ∑ k ∈ Finset.Icc 1 N, b k * (w - 0) ^ (-(k : ℤ))) 0
        = resAt (negTail wp b N) wp := by
      rw [hnegtail_eq]
      exact (resAt_comp_sub_const (fun w' => ∑ k ∈ Finset.Icc 1 N, b k * (w' - 0) ^ (-(k : ℤ)))
        wp).symm
    rw [hshift]
    -- `negTail wp b N` is meromorphic at `wp` (a finite sum of Laurent monomials centred at `wp`).
    have hnegmero : MeromorphicAt (negTail wp b N) wp := by
      show MeromorphicAt (fun w => ∑ k ∈ Finset.Icc 1 N, b k * (w - wp) ^ (-(k : ℤ))) wp
      exact MeromorphicAt.fun_sum (fun k _ => (MeromorphicAt.const (b k) _).mul
        ((analyticAt_id.sub analyticAt_const).meromorphicAt.zpow _))
    -- `resAt (negTail wp b N) wp = resAt hInt wp` (differ by the analytic remainder `R`, residue `0`).
    have hres_hInt : resAt (negTail wp b N) wp = resAt S.hInt wp := by
      have hsum_eq : S.hInt =ᶠ[𝓝[≠] wp] (negTail wp b N) + R := hR_eq
      rw [resAt_congr hsum_eq, resAt_add hnegmero.holoPunctured hR_an.meromorphicAt.holoPunctured,
        resAt_eq_zero_of_analyticAt hR_an, add_zero]
    rw [hres_hInt]
    -- `resAt hInt wp = formFnResidue ω₀ g p` (definitional, `resAt_chartIntegrand_eq_formFnResidue`).
    show resAt (chartIntegrand ω₀ g S.p) ((chartAt ℂ S.p) S.p) = formFnResidue ω₀ g S.p
    exact resAt_chartIntegrand_eq_formFnResidue ω₀ g S.p

/-- **Fact (A): the full geometric trace `traceFull` is meromorphic at `c`.**  From the split
`traceFull =ᶠ ramifiedTraceTerm + Rem` (`exists_split`), with `ramifiedTraceTerm` meromorphic (the
atom) and `Rem` analytic at `c` (`hrem_an`). -/
theorem meromorphicAt_traceFull (S : RamifiedSheetData ω₀ g f Φ c) :
    MeromorphicAt S.traceFull c := by
  obtain ⟨N, b, Rem, hRem_an, hsplit, _⟩ := S.exists_split
  have hsplit' : S.traceFull =ᶠ[𝓝[≠] c]
      (ramifiedTraceTerm (Finset.Icc 1 N) b (fun k => -(k : ℤ)) S.m c) + Rem := hsplit
  refine MeromorphicAt.congr ?_ hsplit'.symm
  exact (meromorphicAt_ramifiedTraceTerm (Finset.Icc 1 N) b (fun k => -(k : ℤ)) S.m c).add
    hRem_an.meromorphicAt

/-- **Fact (B): the residue of the full geometric trace `traceFull` at `c` is the upstairs residue.**
`resAt traceFull c = formFnResidue ω₀ g p`.  From the split: the residue of `ramifiedTraceTerm` is the
upstairs residue (`exists_split`), and `Rem` (analytic) adds `0`. -/
theorem resAt_traceFull (S : RamifiedSheetData ω₀ g f Φ c) :
    resAt S.traceFull c = formFnResidue ω₀ g S.p := by
  obtain ⟨N, b, Rem, hRem_an, hsplit, hpp_res⟩ := S.exists_split
  -- Reshape the split's RHS `fun z => P z + Rem z` to the `Pi.add` form `P + Rem`.
  have hsplit' : S.traceFull =ᶠ[𝓝[≠] c]
      (ramifiedTraceTerm (Finset.Icc 1 N) b (fun k => -(k : ℤ)) S.m c) + Rem := hsplit
  rw [resAt_congr hsplit',
    resAt_add
      (meromorphicAt_ramifiedTraceTerm (Finset.Icc 1 N) b (fun k => -(k : ℤ)) S.m c).holoPunctured
      hRem_an.meromorphicAt.holoPunctured,
    resAt_eq_zero_of_analyticAt hRem_an, add_zero, hpp_res]

end RamifiedSheetData

/-! ### The sound capstone: `RamifiedCenterFacts` from `RamifiedSheetData`

Assembling the full `RamifiedCenterFacts` at a single ramified preimage centre.  Unlike
`RamifiedCenterFacts.ofFibreRamified` (whose `T := ramifiedTraceTerm` forces the FALSE
"full trace = principal-part trace" `hcoh`), here `T := traceFull` is the honest *full* geometric
`m`-sheet trace, so `hcoh` is the genuine punctured germ-equality `valueChartTrace =ᶠ T` (= `hgeom`),
and `hmero`/`hres` are derived through the principal-part split + the proven atom. -/

/-- **`RamifiedCenterFacts` from a single-preimage `RamifiedSheetData`** (the SOUND ramified centre
provider).  Given the Forster §5 sheet data `S` at a ramification preimage `p` of multiplicity `m` over
`c`, and that `p` is the *unique* pole of `α = ω₀·g` in the fibre `F⁻¹(coe c)` (`hp_pole`,
`hp_fibre`, `hp_unique`), build the `RamifiedCenterFacts` whose carried trace `T = traceFull` is the
honest full geometric `m`-sheet trace.  `hcoh` is `S.hgeom` (TRUE — `T` is the full trace, not the
principal part); `hmero`/`hres` are `meromorphicAt_traceFull`/`resAt_traceFull` (the split + the proven
atom).  **No `deriv ≠ 0`** (admits ramification); **no false/circular field** — `T` is honest. -/
noncomputable def RamifiedCenterFacts.ofSheetData {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {poles : Finset X} {c : ℂ}
    (S : RamifiedSheetData ω₀ g f Φ c) (hp_pole : S.p ∈ poles)
    (hp_fibre : f.toRiemannSphere S.p = ((c : ℂ) : RiemannSphere))
    (hp_unique : ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → a = S.p) :
    RamifiedCenterFacts ω₀ g f Φ poles c where
  D :=
    { ι := Unit
      fintype_ι := inferInstance
      xs := fun _ => S.p
      hmem := fun _ => hp_fibre
      mult := fun _ => S.m
      hmult_pos := fun _ => S.hm
      hg_mero := fun _ => S.hg_mero }
  hD_inj := fun _ _ _ => rfl
  hD_mem := fun _ => hp_pole
  hD_surj := fun a ha hfib => ⟨(), (hp_unique a ha hfib).symm⟩
  T := S.traceFull
  hcoh := S.hcoh
  hmero := S.meromorphicAt_traceFull
  hres := by
    show resAt S.traceFull c = ∑ _ : Unit, formFnResidue ω₀ g S.p
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_unit, one_smul, S.resAt_traceFull]

/-! ### Soundness sanity — the `m = 1` (unramified) reduction recovers the planar section term

The ramified construction is a genuine *generalisation* of the unramified `exists_planar_section`, not
a disguised weaker/false statement.  At an *unramified* preimage (`m = 1`, `ζ = 1`, `w₀ = (· − c)`),
the carried geometric trace `traceFull` reduces to the single planar-section trace term

> `z ↦ chartIntegrand ω₀ g p (wp + (z − c)) · (d/dz)[wp + (z − c)]`,

i.e. the chart integrand pushed along the single planar section `z ↦ wp + (z − c)` — exactly the
`exists_planar_section` summand of the unramified `fibreTrace`.  This confirms `RamifiedSheetData`'s
`m`-sheet machinery is consistent (the `m = 1` model is non-vacuous: `w₀ = (· − c)` satisfies every
branch field) and degenerates correctly. -/
theorem traceFull_unramified_eq {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
    {Φ : (b : ℂ) → FibreRegularData g f b} {c : ℂ} (S : RamifiedSheetData ω₀ g f Φ c)
    (hm1 : S.m = 1) (hζ1 : S.ζ = 1) (z : ℂ) :
    S.traceFull z = chartIntegrand ω₀ g S.p ((chartAt ℂ S.p) S.p + S.w₀ z)
      * deriv (fun ζz => (chartAt ℂ S.p) S.p + S.w₀ ζz) z := by
  show (∑ j ∈ Finset.range S.m,
      chartIntegrand ω₀ g S.p ((chartAt ℂ S.p) S.p + S.ζ ^ j * S.w₀ z)
        * deriv (fun ζz => (chartAt ℂ S.p) S.p + S.ζ ^ j * S.w₀ ζz) z) = _
  rw [hm1, hζ1]
  simp

/-! ### Wiring to `ExistsRamifiedCenterFacts` (the precise remaining obligation, now Forster §5 data)

`RamifiedCenterFacts.ofSheetData` reduces the per-centre obligation `ExistsRamifiedCenterFacts`
(`SerreResidueRamifiedCenter.lean`) to the precise Forster §5 normal-form *data* `RamifiedSheetData`
(at a single ramified preimage that is the unique pole in its fibre).  `residueTheorem_ofRamifiedCenters_genus0_mod`
then gives `hoff_cs`-free Gate A from per-centre `RamifiedSheetData`.  The genuine remaining analytic
content is exactly the `RamifiedSheetData` fields: the holomorphic `m`-th-root branch `w₀`, the
geometric trace identification `hgeom`, and the trace-of-holomorphic-is-holomorphic `hrem_an` — all
true (Forster §5), supplied as data, none asserted as a free lemma. -/

/-- **`ExistsRamifiedCenterFacts` from a single-preimage `RamifiedSheetData`.**  Packaging the sound
constructor `RamifiedCenterFacts.ofSheetData` as the named per-centre obligation: the Forster §5 sheet
data at a ramified preimage `p` (the unique pole in the fibre `F⁻¹(coe c)`) inhabits
`ExistsRamifiedCenterFacts`.  This is the bridge that lets the `hoff_cs`-free capstone
`residueTheorem_ofRamifiedCenters_genus0_mod` consume per-centre `RamifiedSheetData`. -/
theorem existsRamifiedCenterFacts_ofSheetData {ω₀ : HolomorphicOneForms X} {g : X → ℂ}
    {f : MeromorphicFunction X} {Φ : (b : ℂ) → FibreRegularData g f b} {poles : Finset X} {c : ℂ}
    (S : RamifiedSheetData ω₀ g f Φ c) (hp_pole : S.p ∈ poles)
    (hp_fibre : f.toRiemannSphere S.p = ((c : ℂ) : RiemannSphere))
    (hp_unique : ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → a = S.p) :
    ExistsRamifiedCenterFacts ω₀ g f Φ poles c :=
  ⟨RamifiedCenterFacts.ofSheetData S hp_pole hp_fibre hp_unique⟩

end Jacobians.Dolbeault.SerreResidueTheorem
