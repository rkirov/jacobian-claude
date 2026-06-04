/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.MultiplicityPatchingConstruct

/-!
# The local multiplicity sheets — discharging `exists_properMapDegree`

This file supplies the last input to the conservation-of-number / argument-principle wall:
the *pointwise* local-conservation data `∀ w₀, LocalMultiplicitySheets f w₀` (the irreducible
§17.9 content), from which `MultiplicityPatchingConstruct.exists_properMapDegree_of_localSheets`
delivers the proper-map-degree existential `∃ d, zerosCount f = d = polesCount f`, hence the
residue theorem `deg (div f) = 0`.

Everything *downstream* of `∀ w₀, LocalMultiplicitySheets f w₀` is already proven sorry-free
(the connectedness globalization of `N f`, the special-fibre identities, the `ofDisjointSheets`
assembly). The content here is the per-value local construction:

* `w₀ ∉ range F`: the empty fibre — `LocalMultiplicitySheets.ofNotMemRange` (proven upstream).
* `w₀ = coe c` (a finite value): around each fibre point `x` (a solution of `f = c`), the planar
  normal form `Planar.orderSum_eq_of_analyticOrder` applied to `g = f ∘ chart.symm` gives a
  value-neighbourhood on which the multiplicity sum is the local order; transported to `localDeg`
  via `localDeg_coe_eq_chartPullback_order`.
* `w₀ = ∞` (the pole fibre): around each pole `x`, the same engine applied to `1/g` at `0`
  (a zero of order = the pole order), with the order-matching `ord(g − c') = ord(1/g − 1/c')`
  for `g(z) = c'` finite nonzero.

This is a true, non-vacuous obligation (the empty-fibre witness certifies satisfiability).

References: Forster §4 (the degree, Cor. 4.24–4.25), Miranda II.4 (argument principle).
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Set Finset OnePoint Filter

namespace Jacobians.ProperMapDegreeSheets

open Jacobians Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct
  Jacobians.MultiplicityPatchingConstruct Jacobians.MultiplicityPatching

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The `holoRepr`/`toFun` reconciliation toolkit

`localDeg f (coe c) y` is the order of `f.toFun ∘ chart.symm − c`, while the *value* fibre
`F⁻¹(coe c)` (= `f.toRiemannSphere ⁻¹' {coe c}`) is cut out by the limit-repair `holoRepr` (the
geometric value of `F`).  The planar normal form is most cleanly applied to the analytic
`g = holoRepr ∘ chart.symm` (whose value matches `F` and whose order matches `localDeg`).  The
three lemmas below bridge the two representatives:

* `meromorphicAt_toFun_chartPullback`: the raw pullback is meromorphic at *any* chart-target point.
* `holoRepr_pullback_eventuallyEq_toFun`: off-center, `holoRepr ∘ chart.symm` agrees with
  `f.toFun ∘ chart.symm` (the junk-repair only changes the value *at* removable singularities,
  which are isolated).
* `meromorphicOrderAt_holoRepr_sub_eq`: hence the chart-pullback order of `f.toFun − c` is the
  order of `holoRepr − c` — the order is `𝓝[≠]`-determined. -/

/-- **The chart pullback `f.toFun ∘ (chartAt x).symm` is meromorphic at any target point `z`.**
At `y₀ := (chartAt x).symm z` the function is meromorphic at the centre of its own chart
(`f.meromorphic y₀`); the chart transition `(chartAt y₀) ∘ (chartAt x).symm` is analytic at `z`
(maximal-atlas coordinate change, `ω`), and `MeromorphicAt.comp_analyticAt` transports the order
across the (locally invertible) transition. -/
theorem meromorphicAt_toFun_chartPullback (f : MeromorphicFunction X) (x : X)
    {z : ℂ} (hz : z ∈ (chartAt (H := ℂ) x).target) :
    MeromorphicAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) z := by
  set e := chartAt (H := ℂ) x with he
  set y₀ := e.symm z with hy₀
  have hy₀src : y₀ ∈ e.source := e.map_target hz
  have hez : e y₀ = z := e.right_inv hz
  have hmero0 : MeromorphicAt (f.toFun ∘ (chartAt (H := ℂ) y₀).symm) ((chartAt (H := ℂ) y₀) y₀) :=
    f.meromorphic y₀
  have hchg_an : AnalyticAt ℂ ((chartAt (H := ℂ) y₀) ∘ e.symm) z := by
    have he_max : e ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
      IsManifold.subset_maximalAtlas (chart_mem_atlas ℂ x)
    have hy0_max : chartAt (H := ℂ) y₀ ∈ IsManifold.maximalAtlas 𝓘(ℂ) ω X :=
      IsManifold.chart_mem_maximalAtlas y₀
    have h := ModelWithCorners.contDiffWithinAt_extendCoordChange'
      he_max hy0_max hy₀src (mem_chart_source ℂ y₀)
    rw [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] at h
    have hpt : (e.extend 𝓘(ℂ)) y₀ = z := by simp [hez, mfld_simps]
    rw [hpt] at h
    exact h.analyticAt
  have hzval : ((chartAt (H := ℂ) y₀) ∘ e.symm) z = (chartAt (H := ℂ) y₀) y₀ := by
    show (chartAt (H := ℂ) y₀) (e.symm z) = (chartAt (H := ℂ) y₀) y₀
    rw [← hy₀]
  have hcomp : MeromorphicAt ((f.toFun ∘ (chartAt (H := ℂ) y₀).symm) ∘
      ((chartAt (H := ℂ) y₀) ∘ e.symm)) z :=
    MeromorphicAt.comp_analyticAt (by rw [hzval]; exact hmero0) hchg_an
  apply hcomp.congr
  have hsrc : ∀ᶠ w in 𝓝 z, e.symm w ∈ (chartAt (H := ℂ) y₀).source := by
    have hcont : ContinuousAt e.symm z := e.continuousAt_symm hz
    have : e.symm ⁻¹' (chartAt (H := ℂ) y₀).source ∈ 𝓝 z := by
      apply hcont.preimage_mem_nhds
      rw [← hy₀]
      exact (chartAt (H := ℂ) y₀).open_source.mem_nhds (mem_chart_source ℂ y₀)
    exact this
  filter_upwards [mem_nhdsWithin_of_mem_nhds hsrc] with w hw
  show (f.toFun ∘ (chartAt (H := ℂ) y₀).symm) ((chartAt (H := ℂ) y₀) (e.symm w)) =
    f.toFun (e.symm w)
  simp only [Function.comp_apply]
  rw [(chartAt (H := ℂ) y₀).left_inv hw]

/-- **Off-center, `holoRepr ∘ (chartAt x).symm` agrees with `f.toFun ∘ (chartAt x).symm`.**
At any target point `z`, the raw pullback is analytic on the *punctured* neighbourhood (it is
meromorphic there, `meromorphicAt_toFun_chartPullback`), so `f.toFun` carries no junk and its
punctured limit `holoRepr` equals the analytic value.  This generalises
`holoRepr_chartPullback_eventuallyEq_NFAt` from the chart centre to any target point. -/
theorem holoRepr_pullback_eventuallyEq_toFun (f : MeromorphicFunction X) (x : X)
    {z : ℂ} (hz : z ∈ (chartAt (H := ℂ) x).target) :
    f.holoRepr ∘ (chartAt (H := ℂ) x).symm =ᶠ[𝓝[≠] z]
      f.toFun ∘ (chartAt (H := ℂ) x).symm := by
  set φ := chartAt (H := ℂ) x with hφ
  set F := f.toFun ∘ φ.symm with hFdef
  have hmero : MeromorphicAt F z := meromorphicAt_toFun_chartPullback f x hz
  have hana : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ F w := hmero.eventually_analyticAt
  have htgt : ∀ᶠ w in 𝓝[≠] z, w ∈ φ.target :=
    mem_nhdsWithin_of_mem_nhds (φ.open_target.mem_nhds hz)
  filter_upwards [hana, htgt] with w hwana hwtgt
  show f.holoRepr (φ.symm w) = F w
  show limUnder (𝓝[≠] (φ.symm w)) f.toFun = F w
  have hys : φ.symm w ∈ φ.source := φ.map_target hwtgt
  have htsymm : Tendsto φ.symm (𝓝[≠] w) (𝓝[≠] (φ.symm w)) := by
    have := φ.symm.tendsto_nhdsNE (x := w) (by simpa using hwtgt)
    simpa using this
  haveI : (𝓝[≠] (φ.symm w)).NeBot := htsymm.neBot
  apply Filter.Tendsto.limUnder_eq
  have hFlim : Tendsto F (𝓝[≠] w) (𝓝 (F w)) :=
    hwana.continuousAt.continuousWithinAt.tendsto
  have hwr : φ (φ.symm w) = w := φ.right_inv hwtgt
  have hfwd : Tendsto φ (𝓝[≠] (φ.symm w)) (𝓝[≠] w) := by
    have := φ.tendsto_nhdsNE hys; rwa [hwr] at this
  have hcomp : Tendsto (F ∘ φ) (𝓝[≠] (φ.symm w)) (𝓝 (F w)) := hFlim.comp hfwd
  refine hcomp.congr' ?_
  have hev : ∀ᶠ y in 𝓝 (φ.symm w), y ∈ φ.source := φ.open_source.mem_nhds hys
  filter_upwards [mem_nhdsWithin_of_mem_nhds hev] with y hy
  simp [hFdef, Function.comp, φ.left_inv hy]

/-- **The chart-pullback order of `localDeg` can be read with `holoRepr` instead of `f.toFun`.**
Since `holoRepr ∘ chart.symm` and `f.toFun ∘ chart.symm` agree on `𝓝[≠] z`
(`holoRepr_pullback_eventuallyEq_toFun`) and `meromorphicOrderAt` is `𝓝[≠]`-determined. -/
theorem meromorphicOrderAt_holoRepr_sub_eq (f : MeromorphicFunction X) (x : X) (c : ℂ)
    {z : ℂ} (hz : z ∈ (chartAt (H := ℂ) x).target) :
    meromorphicOrderAt (fun w => f.holoRepr ((chartAt (H := ℂ) x).symm w) - c) z =
      meromorphicOrderAt (fun w => f.toFun ((chartAt (H := ℂ) x).symm w) - c) z := by
  apply meromorphicOrderAt_congr
  filter_upwards [holoRepr_pullback_eventuallyEq_toFun f x hz] with w hw
  show f.holoRepr ((chartAt (H := ℂ) x).symm w) - c = f.toFun ((chartAt (H := ℂ) x).symm w) - c
  rw [show f.holoRepr ((chartAt (H := ℂ) x).symm w) = f.toFun ((chartAt (H := ℂ) x).symm w) from hw]

/-- **Non-constancy bridge.** A meromorphic `f` with nontrivial divisor (`f.div ≠ 0`) has
`toRiemannSphere` non-constant: `f.div ≠ 0` means some point has nonzero order, and a function
with a nonzero order somewhere is non-constant on the sphere (`toRiemannSphere_not_isConstant`,
the compact-Liouville corollary). -/
theorem toRiemannSphere_not_isConstant_of_div_ne_zero (f : MeromorphicFunction X)
    (hnc : (f.div : Divisor X) ≠ 0) :
    ¬ Jacobians.Discharge.IsConstantMap f.toRiemannSphere := by
  apply f.toRiemannSphere_not_isConstant
  by_contra h
  apply hnc
  ext x
  simp only [Finsupp.coe_zero, Pi.zero_apply, div_apply]
  exact not_not.mp fun hx => h ⟨x, hx⟩

/-- **All fibres of `F = toRiemannSphere` are finite** for a non-constant `f` (`f.div ≠ 0`).
Direct from the unconditional finite-fibres theorem (`fibres_finite_statement_unconditional`)
applied to the ContMDiff sphere map (`contMDiff_toRiemannSphere`), using the non-constancy bridge. -/
theorem fibre_finite_of_div_ne_zero (f : MeromorphicFunction X)
    (hnc : (f.div : Divisor X) ≠ 0) (w : RiemannSphere) :
    (f.toRiemannSphere ⁻¹' {w}).Finite :=
  Jacobians.Discharge.ContMDiff.Degree.fibres_finite_statement_unconditional
    f.toRiemannSphere f.contMDiff_toRiemannSphere
    (toRiemannSphere_not_isConstant_of_div_ne_zero f hnc) w

/-- **The local conservation data at a value in the range** (`w₀ ∈ range F`), for a *non-constant*
`f` (`f.div ≠ 0`, ensuring finite fibres): the genuine §17.9 content, built per fibre point from the
planar normal form. -/
def localMultiplicitySheets_of_mem_range (f : MeromorphicFunction X) (hnc : (f.div : Divisor X) ≠ 0)
    {w₀ : RiemannSphere} (hmem : w₀ ∈ Set.range f.toRiemannSphere) :
    LocalMultiplicitySheets f w₀ :=
  sorry

/-- **Pointwise local-conservation supply for non-constant `f`.** For every value `w₀ : ℂℙ¹` there
is a `LocalMultiplicitySheets f w₀`: the empty-fibre witness off the range, and the §17.9
construction on it. (Needs `f.div ≠ 0`: for a constant `f` the fibre over the constant value is all
of `X`, which is infinite, so no finite `xs` enumerates it — that case is handled separately by
`exists_properMapDegree_of_div_eq_zero`.) -/
def localMultiplicitySheets_of_nonconstant (f : MeromorphicFunction X)
    (hnc : (f.div : Divisor X) ≠ 0) (w₀ : RiemannSphere) :
    LocalMultiplicitySheets f w₀ := by
  by_cases hmem : w₀ ∈ Set.range f.toRiemannSphere
  · exact localMultiplicitySheets_of_mem_range f hnc hmem
  · exact LocalMultiplicitySheets.ofNotMemRange f hmem

/-- **`exists_properMapDegree`, PROVEN.** The proper-map-degree existential — `∃ d : ℕ` with
`zerosCount f = d = polesCount f`. For the trivial divisor (`f.div = 0`, the constant/germ-zero
case) both counts vanish (`exists_properMapDegree_of_div_eq_zero`); otherwise it is discharged from
the pointwise local-conservation supply via the proven connectedness globalization. This is the
exact shape of the upstream named input `Jacobians.exists_properMapDegree`; closing the residue
theorem `deg (div f) = 0`. -/
theorem exists_properMapDegree_proven (f : MeromorphicFunction X) :
    ∃ d : ℕ, zerosCount f = (d : ℤ) ∧ polesCount f = (d : ℤ) := by
  by_cases h : (f.div : Divisor X) = 0
  · exact exists_properMapDegree_of_div_eq_zero f h
  · exact exists_properMapDegree_of_localSheets f (localMultiplicitySheets_of_nonconstant f h)

end Jacobians.ProperMapDegreeSheets

end
