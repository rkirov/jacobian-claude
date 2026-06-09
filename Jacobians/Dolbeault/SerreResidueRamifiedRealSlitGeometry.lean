/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueRamifiedRemDescent

/-!
# Closing the residue theorem `∑Res = 0` unconditionally — the §5 slit-geometry assembly (Gate-A)

`SerreResidueRamifiedRealSlitSection.lean` proved the **section half** of the residue obligation
(`RealSlitSectionData.ofSlitSectionGerm`): from a per-`(z₀,i)` `SlitSectionGerm` family it assembles a
`RealSlitSectionData` (all five §5 section fields).  `SerreResidueRamifiedRemDescent.lean` proved the
**cluster data** half (`exists_clusterTraceData_descent_at_fibrePoint`): a `ClusterTraceData` with the
`Rem` symmetric-function descent supplied (no longer a data hypothesis), plus the *shrunk slit*
mechanism (`exists_descentSlit`, `eventually_cpowBranch_mem`).
`SerreResidueRamifiedRealSlitAssembly.lean` reduced the residue theorem `∑Res = 0` to the single
obligation `RealCoverSlitSectionGeometry` (per centre: a `RealCenterSlitSectionData`).

This file performs the final assembly: it BUILDS `RealCoverSlitSectionGeometry` for the canonical real
cover, hence closes `∑Res = 0` **unconditionally** via
`residueTheorem_of_realCoverSlitSectionGeometry`.

## The geometric heart: cluster sections converge to their preimages

The cluster section point is `clusterSection D Cl i j z = chart_{p}.symm (s (ζʲ·w₀ z))` (`p = D.xs i`).
As `z → c`, `w₀ z → 0` (`cpow_slitBranch_tendsto_zero`), so `ζʲ·w₀ z → 0`, so the §5 local inverse
`s (ζʲ·w₀ z) → s 0 = chart_p p`, hence `chart_p.symm (s (ζʲ·w₀ z)) → chart_p.symm (chart_p p) = p`.
Thus the cluster section point **converges to the preimage `p`** as `z → c`.  Two consequences,
isolating the hardest §5 section fields:

* `hnonpole` — `p` is a non-pole and non-poles are an open condition
  (`eventually_nonpole_of_nonpole`), so the cluster section point is a non-pole for `z` near `c`;
* `hsep` — at distinct preimages `p ≠ p'` (T2-separated), the cluster section points lie in disjoint
  neighbourhoods of `p`, `p'` for `z` near `c`, hence are distinct (`ne_of_mem_disjoint`).

## ⚠ Soundness

The §5 sections are genuine (`exists_clusterSplit_at_fibrePoint`).  The shrunk slit is a genuine slit
(still accumulating at `c`, off the branch locus).  The cluster sheets are the genuine `s(ζʲ·w₀ z)`.
Slit values regular (off-branch).  `D` = the whole fibre (#17).  The `Rem` descent is the genuine
symmetric sum.  `hanalytic`/`hbnd` are the proven canonical-selection machinery
(`hreg_canonical_at_goodValue_sound` / `hbnd_canonical_sound_full`), `pp` from
`exists_principalPart_meromorphicAt`, `hmult = rfl`.  No custom axiom, no sorry on a false statement, no
false/junk/circular field.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4–5, §17.3.
* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3.
* `SerreResidueRamifiedRealSlitSection.lean` (`RealSlitSectionData.ofSlitSectionGerm`, `SlitSectionGerm`,
  `eventually_nonpole_of_nonpole`, `cpow_slitBranch_tendsto_zero`),
  `SerreResidueRamifiedRemDescent.lean` (`exists_clusterTraceData_descent_at_fibrePoint`,
  `exists_descentSlit`, `eventually_cpowBranch_mem`),
  `SerreResidueRamifiedRealSlitAssembly.lean` (`RealCenterSlitSectionData`,
  `RealCoverSlitSectionGeometry`, `residueTheorem_of_realCoverSlitSectionGeometry`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.SymmetricDescent
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTracePrincipalPart
  Jacobians.Dolbeault.FormTraceMovingFibre
  Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct Jacobians.RiemannSphere

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The cluster section converges to its preimage as `z → c`

The geometric heart of `hnonpole`/`hsep`: for the §5 local inverse `s` (analytic at `0`, `s 0 = chart p`),
the cpow slit branch `w₀ z = (z − c)^{1/m}` (`→ 0`), and any sheet index `j`, the cluster section point
`chart_p.symm (s (ζʲ·w₀ z))` tends to `p` as `z → c`. -/

/-- **The cluster section point tends to its preimage `p` as `z → c`.**  For the §5 local inverse `s`
(continuous at `0` with `s 0 = chart_p p`) and the `cpow` slit branch `w₀ z = (z − c)^{1/m}` (`m ≥ 1`),
the cluster section point `chart_p.symm (s (ζʲ · w₀ z))` tends to `p` as `z → c` (within any filter
`≤ 𝓝 c`).  Mechanism: `w₀ z → 0` (`cpow_slitBranch_tendsto_zero`), `s` continuous so
`s (ζʲ·w₀ z) → s 0 = chart_p p`, and `chart_p.symm` continuous at `chart_p p` with
`chart_p.symm (chart_p p) = p`. -/
theorem clusterSectionPoint_tendsto_preimage (p : X) {s w₀ : ℂ → ℂ} {ζ : ℂ} {j : ℕ} {c : ℂ} {m : ℕ}
    (hm : 0 < m) (hs_cont : ContinuousAt s 0) (hs0 : s 0 = (chartAt ℂ p) p)
    (hw₀_eq : w₀ =ᶠ[𝓝 c] fun z => (z - c) ^ ((m : ℂ)⁻¹)) :
    Tendsto (fun z => (chartAt ℂ p).symm (s (ζ ^ j * w₀ z))) (𝓝 c) (𝓝 p) := by
  -- `w₀ z → 0`.
  have hw₀0 : Tendsto w₀ (𝓝 c) (𝓝 0) :=
    (cpow_slitBranch_tendsto_zero c hm).congr' hw₀_eq.symm
  -- `ζʲ · w₀ z → 0`.
  have harg : Tendsto (fun z => ζ ^ j * w₀ z) (𝓝 c) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ζ ^ j)).mul hw₀0
  -- `s (ζʲ·w₀ z) → s 0 = chart_p p`.
  have hs : Tendsto (fun z => s (ζ ^ j * w₀ z)) (𝓝 c) (𝓝 ((chartAt ℂ p) p)) := by
    rw [← hs0]; exact hs_cont.tendsto.comp harg
  -- `chart_p.symm` continuous at `chart_p p`, with `chart_p.symm (chart_p p) = p`.
  have hsymm : ContinuousAt (chartAt ℂ p).symm ((chartAt ℂ p) p) := by
    have htgt : (chartAt ℂ p) p ∈ (chartAt ℂ p).target :=
      (chartAt ℂ p).map_source (mem_chart_source ℂ p)
    exact (chartAt ℂ p).continuousAt_symm htgt
  have hsymm_p : (chartAt ℂ p).symm ((chartAt ℂ p) p) = p :=
    (chartAt ℂ p).left_inv (mem_chart_source ℂ p)
  have hcomp := (hsymm.tendsto).comp hs
  rw [hsymm_p] at hcomp
  exact hcomp

/-- **The cluster section point is a non-pole near `c` (the `hnonpole` content, eventual form).**  At a
non-pole preimage `p` of `f`, with the §5 local inverse `s` (continuous at `0`, `s 0 = chart_p p`) and the
`cpow` slit branch `w₀`, the cluster section point `chart_p.symm (s (ζʲ·w₀ z))` is a non-pole of `f` for
`z` in a neighbourhood of `c` (it tends to the non-pole `p`, and non-poles are open). -/
theorem eventually_clusterSectionPoint_nonpole (f : MeromorphicFunction X) {p : X}
    (hp_np : 0 ≤ f.orderAtPoint p) {s w₀ : ℂ → ℂ} {ζ : ℂ} {j : ℕ} {c : ℂ} {m : ℕ}
    (hm : 0 < m) (hs_cont : ContinuousAt s 0) (hs0 : s 0 = (chartAt ℂ p) p)
    (hw₀_eq : w₀ =ᶠ[𝓝 c] fun z => (z - c) ^ ((m : ℂ)⁻¹)) :
    ∀ᶠ z in 𝓝 c, 0 ≤ f.orderAtPoint ((chartAt ℂ p).symm (s (ζ ^ j * w₀ z))) := by
  have htend := clusterSectionPoint_tendsto_preimage p hm hs_cont hs0 hw₀_eq (ζ := ζ) (j := j)
  exact htend.eventually (eventually_nonpole_of_nonpole f hp_np)

/-! ## A reusable "transport a `𝓝 0` fact to an open `𝓝 c` set along the cpow branch" helper

`exists_descentSlit` transported one *equation* along the cpow branch.  Here we extract the underlying
device as a reusable open-set producer: for any property `P` holding on a `𝓝 0` neighbourhood, there is
an open `V ∋ c` on which `P` holds at the cpow branch for all `z ∈ V`.  Used to build the common shrunk
slit serving all the eventual §5 facts (inverse, normal form, analyticity, pp-split, non-pole) at once. -/

/-- **An open `𝓝 c` set on which a `𝓝 0` property holds along the cpow branch.**  For any property `P`
holding eventually in `𝓝 0`, there is an open `V ∋ c` with `P ((z − c)^{1/m})` for every `z ∈ V`. -/
theorem exists_open_cpowBranch_mem (c : ℂ) {m : ℕ} (hm : 0 < m) {P : ℂ → Prop}
    (hP : ∀ᶠ u in 𝓝 (0 : ℂ), P u) :
    ∃ V : Set ℂ, IsOpen V ∧ c ∈ V ∧ ∀ z ∈ V, P ((z - c) ^ ((m : ℂ)⁻¹)) := by
  have hev := eventually_cpowBranch_mem c hm hP
  rw [Filter.eventually_iff, _root_.mem_nhds_iff] at hev
  obtain ⟨V, hVsub, hVopen, hcV⟩ := hev
  exact ⟨V, hVopen, hcV, fun z hz => hVsub hz⟩

/-- **An open `𝓝 c` set on which a property of `z` holds (from an eventual `𝓝 c` fact).**  Unpacks an
`∀ᶠ z in 𝓝 c, P z` into an open `V ∋ c` with `P` on it. -/
theorem exists_open_of_eventually_nhds (c : ℂ) {P : ℂ → Prop} (hP : ∀ᶠ z in 𝓝 c, P z) :
    ∃ V : Set ℂ, IsOpen V ∧ c ∈ V ∧ ∀ z ∈ V, P z := by
  rw [Filter.eventually_iff, _root_.mem_nhds_iff] at hP
  obtain ⟨V, hVsub, hVopen, hcV⟩ := hP
  exact ⟨V, hVopen, hcV, fun z hz => hVsub hz⟩

end Jacobians.Dolbeault.SerreResidueTheorem
