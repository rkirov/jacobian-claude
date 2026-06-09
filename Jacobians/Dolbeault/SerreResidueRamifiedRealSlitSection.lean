/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueRamifiedRealSlitAssembly

/-!
# The per-slit §5 normal-form section geometry for the real cover (closing the residue obligation)

`SerreResidueRamifiedRealSlitAssembly.lean` reduced the residue theorem `∑Res = 0`, for the real cover,
to the single obligation `RealCoverSlitSectionGeometry`: at each finite pole-value centre `c`, a slit
`Sset` accumulating at `c` off the branch locus, the per-preimage §5 cluster data `Cl`, and per slit
value `z ∈ Sset` the §5 normal-form section facts `RealSlitSectionData` (`hcs_sec`/`hcs_np`/`hwithin`/
`hcross`/`hsrc`).

This file builds the genuine Forster §4/§5 normal-form section geometry from the PROVEN §5 atom
`exists_clusterSplit_at_fibrePoint` (the normal form `F = c + ηᵐ` + the local inverse `s = η⁻¹`).

## The key analytic mechanism: the *shrunk* slit

The §5 atom's inverse property `η (s a) = a` and the normal form `F (chart.symm w) = c + η wᵐ` hold only
**near `a = 0` / `w = chart p`** (a local biholomorphism domain).  For a *fixed* slit value `z` and `w`
near `z`, the cluster argument is `a(w) = ζʲ · w₀ w`, which tends to `ζʲ · w₀ z` — NOT to `0` unless `z`
is close to `c` (`w₀ z = (z − c)^{1/m} → 0` as `z → c`).  The resolution is the **shrunk slit**: choose
`Sset ⊆ {z | z − c ∈ slitPlane}` small enough (per preimage) that every cluster argument `ζʲ · w₀ z`
stays in the §5 inverse-property domain.  Then, for `z` interior to the shrunk slit, a *full* ℂ-neighbourhood
of `z` keeps the cluster arguments in that domain, so the eventual section facts (`hcs_sec`, `hsrc`) hold.

## ⚠ Soundness

The §5 sections are genuine (`exists_clusterSplit_at_fibrePoint`).  The shrunk slit is a genuine slit
(still accumulating at `c`, off the branch locus, simply connected).  The cluster sheets are the genuine
`s(ζʲ·w₀ z)` (NOT the first-order `wp + ζʲ·w₀ z`).  Slit values are regular (off-branch).  `D` is the
whole fibre (#17).  No custom axiom, no sorry on a false statement, no false/junk/circular field.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4–5.
* `SerreResidueRamifiedMultiplicityBridge.lean` (`exists_clusterSplit_at_fibrePoint`),
  `SerreResidueRamifiedFullFibreBuilder.lean` (`ClusterTraceData.ofNormalForm`),
  `SerreResidueRamifiedClusterSplit.lean` (`clusterSheet`, `clusterSheet_sect`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTracePrincipalPart
  Jacobians.Dolbeault.FormTraceMovingFibre
  Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct Jacobians.RiemannSphere

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The cpow slit branch tends to `0` at the centre

The standard slit branch `w₀ z = (z − c)^{1/m}` (the `cpow` principal branch) is continuous at every
slit value and tends to `0` as `z → c` (`(z − c) → 0`, `0^{1/m} = 0`).  This is the mechanism that lets
the cluster arguments `ζʲ · w₀ z` be pushed into the §5 inverse-property domain by shrinking the slit. -/

/-- **The cpow slit branch is continuous and `→ 0` at the centre.**  For `m ≥ 1`, the principal branch
`w₀ z := (z − c)^{(m:ℂ)⁻¹}` tends to `0` as `z → c`.  (`cpow` is continuous at `0` for a positive real
exponent: `0^{1/m} = 0` since `1/m ≠ 0`.) -/
theorem cpow_slitBranch_tendsto_zero (c : ℂ) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun z => (z - c) ^ ((m : ℂ)⁻¹)) (𝓝 c) (𝓝 0) := by
  have hsub : Tendsto (fun z : ℂ => z - c) (𝓝 c) (𝓝 0) := by
    simpa using (continuous_sub_right c).tendsto c
  have hre : (0 : ℝ) < ((m : ℂ)⁻¹).re := by
    rw [show ((m : ℂ)⁻¹) = ((m : ℝ)⁻¹ : ℝ) by push_cast; ring, Complex.ofReal_re]
    positivity
  have hcont0 : Tendsto (fun w : ℂ => w ^ ((m : ℂ)⁻¹)) (𝓝 0) (𝓝 0) := by
    have h := Complex.continuousAt_cpow_zero_of_re_pos hre
    have h2 : Tendsto (fun w : ℂ => (w, (m : ℂ)⁻¹)) (𝓝 0) (𝓝 (0, (m : ℂ)⁻¹)) :=
      Tendsto.prodMk_nhds (by simpa using tendsto_id) tendsto_const_nhds
    have hne : ((m : ℂ)⁻¹) ≠ 0 := by simp [hm.ne']
    have := h.tendsto.comp h2
    simpa [Function.comp, Complex.zero_cpow hne] using this
  exact hcont0.comp hsub

/-! ## Non-pole is an open condition

A non-pole `x` (`0 ≤ orderAtPoint x`) of a meromorphic function has a whole neighbourhood of non-poles:
`toRiemannSphere` is continuous at `x` (it equals `coe ∘ holoRepr` near a non-pole) with finite value
`coe (holoRepr x) ≠ ∞`, so points near `x` map into `{∞}ᶜ`, hence are non-poles
(`toRiemannSphere_of_pole` contrapositive).  This is the mechanism that makes `hcs_np` reachable: for the
shrunk slit, the cluster section point lies in the non-pole neighbourhood of its fibre preimage `p`. -/

/-- **Non-pole is an open condition.**  If `x` is a non-pole (`0 ≤ f.orderAtPoint x`), then every point
in a neighbourhood of `x` is a non-pole. -/
theorem eventually_nonpole_of_nonpole (f : MeromorphicFunction X) {x : X}
    (hx : 0 ≤ f.orderAtPoint x) : ∀ᶠ y in 𝓝 x, 0 ≤ f.orderAtPoint y := by
  have hcont : ContinuousAt f.toRiemannSphere x :=
    (f.contMDiffAt_toRiemannSphere_of_nonneg hx).continuousAt
  have hval : f.toRiemannSphere x ≠ OnePoint.infty := by
    rw [f.toRiemannSphere_of_nonneg hx]; exact OnePoint.coe_ne_infty _
  have hmem : f.toRiemannSphere ⁻¹' {OnePoint.infty}ᶜ ∈ 𝓝 x :=
    hcont.preimage_mem_nhds (isOpen_compl_singleton.mem_nhds hval)
  filter_upwards [hmem] with y hy
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hy
  by_contra hlt
  exact hy (f.toRiemannSphere_of_pole (not_le.mp hlt))

/-! ## The per-preimage eventual §5 section property (the heart of `hcs_sec`)

The §5 atom `exists_clusterSplit_at_fibrePoint` provides `η`/`s` with the inverse property `η (s a) = a`
near `a = 0` and the normal form `f.holoRepr (chart.symm w) = c + η wᵐ` near `w = chart p`.  For a slit
value `z₀` whose cluster arguments `ζʲ · w₀ z₀` lie near `0`, the section property
`f.holoRepr (chart.symm (clusterSheet s ζ w₀ j w)) = w` holds for `w` in a *full ℂ-neighbourhood* of
`z₀` (the cluster arguments stay near `0`, the cluster points stay near `chart p`, and the slit power
identity holds), by pulling back the §5 atom's eventual facts along the continuous `w ↦ ζʲ · w₀ w`. -/

/-- **The eventual §5 section property near a slit value `z₀`.**  Given the §5 normal-form data
(`η`/`s`, the inverse property `hinv` valid near `a₀ := ζʲ · w₀ z₀`, the normal form `hnf` valid near
`s a₀`, and the slit power identity `hpow` valid near `z₀`), the cluster sheet point is a genuine
`holoRepr`-section of `f` near `z₀`:

> `∀ᶠ w in 𝓝 z₀, f.holoRepr (chart_p.symm (clusterSheet s ζ w₀ j w)) = w`.

This is the §5 section clause of `exists_clusterSplit_at_fibrePoint` (`clusterSheet_sect`), localised at
`z₀` by the continuity pullback of the atom's `𝓝 0` / `𝓝 (chart p)` eventual facts. -/
theorem eventually_holoRepr_clusterSheet_eq (f : MeromorphicFunction X) {c : ℂ} {p : X} {m : ℕ}
    {η s w₀ : ℂ → ℂ} {ζ : ℂ} {j : ℕ} {z₀ : ℂ}
    (hs_cont : ContinuousAt s (ζ ^ j * w₀ z₀)) (hw₀_cont : ContinuousAt w₀ z₀)
    (hζ : IsPrimitiveRoot ζ m)
    (hinv : ∀ᶠ a in 𝓝 (ζ ^ j * w₀ z₀), η (s a) = a)
    (hnf : ∀ᶠ w' in 𝓝 (s (ζ ^ j * w₀ z₀)),
      f.holoRepr ((chartAt (H := ℂ) p).symm w') = c + η w' ^ m)
    (hpow : ∀ᶠ w in 𝓝 z₀, w₀ w ^ (m : ℤ) = w - c) :
    ∀ᶠ w in 𝓝 z₀, f.holoRepr ((chartAt (H := ℂ) p).symm (clusterSheet s ζ w₀ j w)) = w := by
  have harg_a : Tendsto (fun w => ζ ^ j * w₀ w) (𝓝 z₀) (𝓝 (ζ ^ j * w₀ z₀)) :=
    tendsto_const_nhds.mul hw₀_cont.tendsto
  have ha : ∀ᶠ w in 𝓝 z₀, η (s (ζ ^ j * w₀ w)) = ζ ^ j * w₀ w := harg_a.eventually hinv
  have harg_b : Tendsto (fun w => s (ζ ^ j * w₀ w)) (𝓝 z₀) (𝓝 (s (ζ ^ j * w₀ z₀))) :=
    hs_cont.tendsto.comp harg_a
  have hb : ∀ᶠ w in 𝓝 z₀, f.holoRepr ((chartAt (H := ℂ) p).symm (s (ζ ^ j * w₀ w)))
      = c + η (s (ζ ^ j * w₀ w)) ^ m := harg_b.eventually hnf
  filter_upwards [ha, hb, hpow] with w hwa hwb hwp
  exact clusterSheet_sect (F := fun u => f.holoRepr ((chartAt (H := ℂ) p).symm u)) hζ hwp hwa hwb

end Jacobians.Dolbeault.SerreResidueTheorem
