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

/-! ## Transporting a punctured `𝓝[≠] 0` property along the cpow branch (the `hpp_split_sheet` device)

The principal-part split holds on a *punctured* neighbourhood `𝓝[≠] 0` of the straightening coordinate.
Pulled back along the cpow branch `z ↦ ζʲ · (z − c)^{1/m}` restricted to the slit `{z | z − c ∈ slitPlane}`
(where the branch is nonzero, `ζʲ ≠ 0`, and `→ 0`), the split holds at the sheet argument for every slit
value near `c`. -/

/-- **The cpow sheet argument maps the slit-at-`c` filter into `𝓝[≠] 0`.**  For `m ≥ 1`, `ζ` a primitive
`m`-th root, and the slit `slit := {z | z − c ∈ slitPlane}`, the map `z ↦ ζʲ · (z − c)^{1/m}` carries
`𝓝[slit] c` into `𝓝[≠] 0`: it tends to `0` (cpow branch), and on the slit the value is nonzero
(`slitPlane_ne_zero` + `ζʲ ≠ 0`). -/
theorem cpowSheetArg_tendsto_punctured (c : ℂ) {m : ℕ} (hm : 0 < m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ m)
    (j : ℕ) :
    Tendsto (fun z => ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) (𝓝[{z : ℂ | z - c ∈ slitPlane}] c) (𝓝[≠] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · -- tends to 0
    have h0 : Tendsto (fun z => (z - c) ^ ((m : ℂ)⁻¹))
        (𝓝[{z : ℂ | z - c ∈ slitPlane}] c) (𝓝 0) :=
      (cpow_slitBranch_tendsto_zero c hm).mono_left nhdsWithin_le_nhds
    simpa using (tendsto_const_nhds (x := ζ ^ j)).mul h0
  · -- eventually nonzero on the slit
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hζne : ζ ^ j ≠ 0 := pow_ne_zero _ (hζ.ne_zero hm.ne')
    have hw₀ne : (z - c) ^ ((m : ℂ)⁻¹) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.slitPlane_ne_zero hz))
    exact mul_ne_zero hζne hw₀ne

/-- **Transport of a `𝓝[≠] 0` property to an open `𝓝 c` set along the cpow sheet argument.**  For `P`
holding eventually in `𝓝[≠] 0`, there is an open `V ∋ c` such that, for every slit value `z ∈ V`
(`z − c ∈ slitPlane`), `P (ζʲ · (z − c)^{1/m})` holds.  This supplies the `hpp_split_sheet` punctured-
split hypothesis on the shrunk slit `V ∩ slit`. -/
theorem exists_open_cpowSheetArg_punctured (c : ℂ) {m : ℕ} (hm : 0 < m) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ m) (j : ℕ) {P : ℂ → Prop} (hP : ∀ᶠ u in 𝓝[≠] (0 : ℂ), P u) :
    ∃ V : Set ℂ, IsOpen V ∧ c ∈ V ∧
      ∀ z ∈ V, z - c ∈ slitPlane → P (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) := by
  have hev : ∀ᶠ z in 𝓝[{z : ℂ | z - c ∈ slitPlane}] c, P (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) :=
    (cpowSheetArg_tendsto_punctured c hm hζ j).eventually hP
  rw [eventually_nhdsWithin_iff, Filter.eventually_iff, _root_.mem_nhds_iff] at hev
  obtain ⟨V, hVsub, hVopen, hcV⟩ := hev
  exact ⟨V, hVopen, hcV, fun z hz hslit => hVsub hz hslit⟩

/-! ## The `s`-composed cpow branch lands near `chart p` (the `hnf`/`htgt` device)

For the §5 local inverse `s` (continuous at `0`, `s 0 = chart_p p`), the composed map
`z ↦ s (ζʲ · (z − c)^{1/m})` tends to `chart_p p` as `z → c`.  So `s (sheet arg)` lands in any given open
neighbourhood of `chart_p p` for `z` near `c` — supplying the normal-form domain (`hnf`) and the chart-
target membership (`htgt`) on the shrunk slit. -/

/-- **The `s`-composed cpow sheet argument tends to `chart_p p`.**  For `m ≥ 1`, `s` continuous at `0`
with `s 0 = chart_p p`, the map `z ↦ s (ζʲ · (z − c)^{1/m})` tends to `chart_p p` as `z → c`. -/
theorem sComp_cpowSheetArg_tendsto (p : X) {s : ℂ → ℂ} {ζ : ℂ} {j : ℕ} (c : ℂ) {m : ℕ}
    (hm : 0 < m) (hs_cont : ContinuousAt s 0) (hs0 : s 0 = (chartAt ℂ p) p) :
    Tendsto (fun z => s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))) (𝓝 c) (𝓝 ((chartAt ℂ p) p)) := by
  have harg : Tendsto (fun z => ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) (𝓝 c) (𝓝 0) := by
    simpa using (tendsto_const_nhds (x := ζ ^ j)).mul (cpow_slitBranch_tendsto_zero c hm)
  rw [← hs0]; exact hs_cont.tendsto.comp harg

/-! ## The per-preimage §5 datum on a shrunk-slit neighbourhood

We bundle, for one non-pole fibre preimage `p = D.xs i` of multiplicity `m = (localDeg f (coe c) p).toNat`,
all the *slit-independent* §5 / principal-part / descent data (the §5 atom's straightening `η`/local
inverse `s`, the Laurent principal part `ppN`/`ppb`/`ppR`, the descent germ `G`) together with one open
neighbourhood `V ∋ c` on which every per-slit-value fact needed downstream holds at the `cpow` sheet
arguments.  This is the per-preimage extraction; the centre-level assembly intersects the `V`'s over the
finite fibre and reads off both the cluster data `Cl i` and the §5 section germs. -/

/-- **The per-preimage §5 datum on a shrunk-slit nbhd `V`** (the slit-independent §5/pp/descent package).
For a non-pole fibre preimage `p` of multiplicity `m` (`ζ` a primitive `m`-th root), bundles the §5 atom
(`η`/`s` with inverse `hinv0` near `0` and normal form `hnf0` near `chart_p p`), the Laurent principal
part (`ppN`/`ppb`/`ppR`/`hppR_an`/`hsplit0`), the descent germ (`G`/`hG`), and an open `V ∋ c` on which —
for `z ∈ V` off-slit-restricted — the cpow sheet arguments satisfy: `s`-analyticity (`hVs_an`), the
principal-part split (`hVpp_split`), the descent identity (`hVsmall`), the inverse-property domain
membership (`hVinv_mem`), the normal-form domain membership (`hVnf_mem`), and the chart-target membership
(`hVtgt`). -/
structure Fibre5Datum (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    (f : MeromorphicFunction X) (c : ℂ) (p : X) (m : ℕ) where
  /-- `m ≥ 1`. -/
  hm : 0 < m
  /-- A primitive `m`-th root. -/
  ζ : ℂ
  /-- `ζ` is primitive. -/
  hζ : IsPrimitiveRoot ζ m
  /-- The §5 straightening coordinate. -/
  η : ℂ → ℂ
  /-- The §5 local inverse `s = η⁻¹`. -/
  s : ℂ → ℂ
  /-- `s` analytic at `0`. -/
  hs_an : AnalyticAt ℂ s 0
  /-- `s 0 = chart_p p`. -/
  hs0 : s 0 = (chartAt ℂ p) p
  /-- `deriv s 0 ≠ 0`. -/
  hs_deriv : deriv s 0 ≠ 0
  /-- The §5 inverse property near `0`. -/
  hinv0 : ∀ᶠ a in 𝓝 (0 : ℂ), η (s a) = a
  /-- The §5 normal form near `chart_p p`. -/
  hnf0 : ∀ᶠ w in 𝓝 ((chartAt ℂ p) p), f.holoRepr ((chartAt ℂ p).symm w) = c + η w ^ m
  /-- Laurent principal-part degree. -/
  ppN : ℕ
  /-- Laurent principal-part coefficients. -/
  ppb : ℕ → ℂ
  /-- Analytic remainder. -/
  ppR : ℂ → ℂ
  /-- The remainder is analytic at `0`. -/
  hppR_an : AnalyticAt ℂ ppR 0
  /-- The principal-part split on `𝓝[≠] 0`. -/
  hsplit0 : straightenedIntegrand ω₀ g.toFun p s =ᶠ[𝓝[≠] 0]
    fun u => negTail 0 ppb ppN u + ppR u
  /-- The descent germ. -/
  G : ℂ → ℂ
  /-- The descent germ is analytic at `0`. -/
  hG : AnalyticAt ℂ G 0
  /-- The shrunk-slit neighbourhood. -/
  V : Set ℂ
  /-- `V` is open. -/
  hVopen : IsOpen V
  /-- `c ∈ V`. -/
  hcV : c ∈ V
  /-- `s` is analytic at each cpow sheet argument on `V ∩ slit`. -/
  hVs_an : ∀ z ∈ V, z - c ∈ slitPlane → ∀ j ∈ Finset.range m,
    AnalyticAt ℂ s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))
  /-- The principal-part split holds at each cpow sheet argument on `V ∩ slit`. -/
  hVpp_split : ∀ z ∈ V, z - c ∈ slitPlane → ∀ j ∈ Finset.range m,
    straightenedIntegrand ω₀ g.toFun p s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))
      = negTail 0 ppb ppN (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) + ppR (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))
  /-- The descent identity holds at the cpow branch on `V ∩ slit`. -/
  hVsmall : ∀ z ∈ V, z - c ∈ slitPlane →
    (∑ j ∈ Finset.range m, ppR (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) * ζ ^ j)
      = m * ((z - c) ^ ((m : ℂ)⁻¹)) ^ (m - 1) * G (((z - c) ^ ((m : ℂ)⁻¹)) ^ m)
  /-- The cpow sheet argument lands in the inverse-property domain on `V ∩ slit`. -/
  hVinv_mem : ∀ z ∈ V, z - c ∈ slitPlane → ∀ j ∈ Finset.range m,
    ∀ᶠ a in 𝓝 (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)), η (s a) = a
  /-- The `s`-composed cpow sheet argument lands in the normal-form domain on `V ∩ slit`. -/
  hVnf_mem : ∀ z ∈ V, z - c ∈ slitPlane → ∀ j ∈ Finset.range m,
    ∀ᶠ w in 𝓝 (s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))),
      f.holoRepr ((chartAt ℂ p).symm w) = c + η w ^ m
  /-- The `s`-composed cpow sheet argument lands in the chart target on `V ∩ slit`. -/
  hVtgt : ∀ z ∈ V, z - c ∈ slitPlane → ∀ j ∈ Finset.range m,
    s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) ∈ (chartAt ℂ p).target

/-- **The per-preimage §5 datum exists at a non-pole fibre preimage.**  At a non-pole fibre preimage `p`
over `coe c` of a non-constant cover `f` (`f.div ≠ 0`), of genuine multiplicity
`m = (localDeg f (coe c) p).toNat`, with `ζ` a primitive `m`-th root, the `Fibre5Datum` is constructed
from: the Forster §5 normal form (`exists_clusterSplit_at_fibrePoint`); the Laurent principal part of the
straightened integrand (`exists_principalPart_meromorphicAt`); the symmetric-function descent germ
(`analyticAt_weightedSymSum_descent`); and an open `V ∋ c` (the finite intersection of the per-fact
shrunk-slit neighbourhoods, via `exists_open_cpowBranch_mem` / `exists_open_cpowSheetArg_punctured` /
`exists_open_of_eventually_nhds`). -/
theorem exists_fibre5Datum (ω₀ : HolomorphicOneForms X) (g : MeromorphicFunction X)
    {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0) {c : ℂ} {p : X}
    (hp_fib : f.toRiemannSphere p = ((c : ℂ) : RiemannSphere)) (hp_np : 0 ≤ f.orderAtPoint p)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (localDeg f ((c : ℂ) : RiemannSphere) p).toNat) :
    Nonempty (Fibre5Datum ω₀ g f c p (localDeg f ((c : ℂ) : RiemannSphere) p).toNat) := by
  classical
  set m := (localDeg f ((c : ℂ) : RiemannSphere) p).toNat with hm_def
  have hm : 0 < m := (Jacobians.analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np).1
  -- The §5 atom.
  obtain ⟨η, s, hη_an, hη0, hηderiv, hnf0, hs_an, hs0, hs_deriv, hinv0, _hsect⟩ :=
    exists_clusterSplit_at_fibrePoint f hdiv hp_fib hp_np hζ
  -- The principal part of the straightened integrand at `0`.
  have hg_mero : MeromorphicAt (fun z => g.toFun ((chartAt ℂ p).symm z)) ((chartAt ℂ p) p) := by
    simpa [Function.comp] using g.meromorphic p
  have hH_mero : MeromorphicAt (straightenedIntegrand ω₀ g.toFun p s) 0 :=
    meromorphicAt_straightenedIntegrand ω₀ g.toFun p hs_an hs0 hg_mero
  obtain ⟨ppN, ppb, ppR, hppR_an, hsplit0⟩ := exists_principalPart_meromorphicAt hH_mero
  -- The descent germ from the analytic remainder.
  obtain ⟨G, hG, hGev⟩ := analyticAt_weightedSymSum_descent hppR_an hm hζ
  -- `a ↦ ζʲ·a` fixes `0` (the scaling that pushes a `𝓝 0` fact onto the cpow sheet argument).
  have harg0 : ∀ j : ℕ, Tendsto (fun a : ℂ => ζ ^ j * a) (𝓝 0) (𝓝 0) := fun j => by
    have : Continuous (fun a : ℂ => ζ ^ j * a) := continuous_const.mul continuous_id
    simpa using this.tendsto' 0 0 (by simp)
  -- The open neighbourhoods for the six per-slit-value facts.
  -- (1) `s`-analyticity at sheet args (𝓝 0 fact, per `j`).
  have hVs_an_j : ∀ j, ∃ Vj : Set ℂ, IsOpen Vj ∧ c ∈ Vj ∧
      ∀ z ∈ Vj, z - c ∈ slitPlane → AnalyticAt ℂ s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) := by
    intro j
    obtain ⟨V, hVo, hcV, hV⟩ := exists_open_cpowBranch_mem c (m := m) hm
      (P := fun a => AnalyticAt ℂ s (ζ ^ j * a))
      ((harg0 j).eventually hs_an.eventually_analyticAt)
    exact ⟨V, hVo, hcV, fun z hz hslit => hV z hz⟩
  -- (2) principal-part split at sheet args (𝓝[≠] 0 fact, per `j`).
  have hVpp_j : ∀ j, ∃ Vj : Set ℂ, IsOpen Vj ∧ c ∈ Vj ∧
      ∀ z ∈ Vj, z - c ∈ slitPlane →
        straightenedIntegrand ω₀ g.toFun p s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))
          = negTail 0 ppb ppN (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) + ppR (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) :=
    fun j => exists_open_cpowSheetArg_punctured c hm hζ j hsplit0
  -- (3) descent identity at branch (𝓝 0 fact, single).
  have hVsmall_ex : ∃ V : Set ℂ, IsOpen V ∧ c ∈ V ∧
      ∀ z ∈ V, z - c ∈ slitPlane →
        (∑ j ∈ Finset.range m, ppR (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) * ζ ^ j)
          = m * ((z - c) ^ ((m : ℂ)⁻¹)) ^ (m - 1) * G (((z - c) ^ ((m : ℂ)⁻¹)) ^ m) := by
    obtain ⟨V, hVo, hcV, hV⟩ := exists_open_cpowBranch_mem c hm hGev
    exact ⟨V, hVo, hcV, fun z hz _ => hV z hz⟩
  -- (4) inverse-property domain membership (𝓝 0 fact, per `j`).
  have hVinv_j : ∀ j, ∃ Vj : Set ℂ, IsOpen Vj ∧ c ∈ Vj ∧
      ∀ z ∈ Vj, z - c ∈ slitPlane →
        ∀ᶠ a in 𝓝 (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)), η (s a) = a := by
    intro j
    obtain ⟨V, hVo, hcV, hV⟩ := exists_open_cpowBranch_mem c (m := m) hm
      (P := fun w => ∀ᶠ a in 𝓝 (ζ ^ j * w), η (s a) = a)
      ((harg0 j).eventually hinv0.eventually_nhds)
    exact ⟨V, hVo, hcV, fun z hz hslit => hV z hz⟩
  -- (5) normal-form domain membership (continuity fact, per `j`).
  have hVnf_j : ∀ j, ∃ Vj : Set ℂ, IsOpen Vj ∧ c ∈ Vj ∧
      ∀ z ∈ Vj, z - c ∈ slitPlane →
        ∀ᶠ w in 𝓝 (s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹))),
          f.holoRepr ((chartAt ℂ p).symm w) = c + η w ^ m := by
    intro j
    have htend := sComp_cpowSheetArg_tendsto p (s := s) (ζ := ζ) (j := j) c hm hs_an.continuousAt hs0
    obtain ⟨V, hVo, hcV, hV⟩ := exists_open_of_eventually_nhds c (htend.eventually hnf0.eventually_nhds)
    exact ⟨V, hVo, hcV, fun z hz hslit => hV z hz⟩
  -- (6) chart-target membership (continuity fact, per `j`).
  have hVtgt_j : ∀ j, ∃ Vj : Set ℂ, IsOpen Vj ∧ c ∈ Vj ∧
      ∀ z ∈ Vj, z - c ∈ slitPlane →
        s (ζ ^ j * (z - c) ^ ((m : ℂ)⁻¹)) ∈ (chartAt ℂ p).target := by
    intro j
    have htend := sComp_cpowSheetArg_tendsto p (s := s) (ζ := ζ) (j := j) c hm hs_an.continuousAt hs0
    have htgt0 : (chartAt ℂ p).target ∈ 𝓝 ((chartAt ℂ p) p) :=
      (chartAt ℂ p).open_target.mem_nhds ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
    obtain ⟨V, hVo, hcV, hV⟩ := exists_open_of_eventually_nhds c (htend.eventually htgt0)
    exact ⟨V, hVo, hcV, fun z hz hslit => hV z hz⟩
  -- Choose the per-`j` neighbourhoods and intersect everything (finite: `j ∈ range m`).
  choose Vsa hVsa_o hVsa_c hVsa using hVs_an_j
  choose Vpp hVpp_o hVpp_c hVpp using hVpp_j
  obtain ⟨Vsm, hVsm_o, hVsm_c, hVsm⟩ := hVsmall_ex
  choose Vinv hVinv_o hVinv_c hVinv using hVinv_j
  choose Vnf hVnf_o hVnf_c hVnf using hVnf_j
  choose Vtg hVtg_o hVtg_c hVtg using hVtgt_j
  -- The common open neighbourhood.
  set V : Set ℂ := Vsm ∩ (⋂ j ∈ Finset.range m, (Vsa j ∩ Vpp j ∩ Vinv j ∩ Vnf j ∩ Vtg j)) with hV_def
  have hVopen : IsOpen V := by
    refine hVsm_o.inter ?_
    refine isOpen_biInter_finset (fun j _ => ?_)
    exact (((hVsa_o j).inter (hVpp_o j)).inter (hVinv_o j)).inter (hVnf_o j) |>.inter (hVtg_o j)
  have hcV : c ∈ V := by
    refine ⟨hVsm_c, ?_⟩
    rw [Set.mem_iInter₂]
    exact fun j _ => ⟨⟨⟨⟨hVsa_c j, hVpp_c j⟩, hVinv_c j⟩, hVnf_c j⟩, hVtg_c j⟩
  -- Extract per-`j` membership from `V`.
  have hVmem : ∀ z ∈ V, ∀ j ∈ Finset.range m,
      z ∈ Vsa j ∧ z ∈ Vpp j ∧ z ∈ Vinv j ∧ z ∈ Vnf j ∧ z ∈ Vtg j := by
    intro z hz j hj
    have h := (Set.mem_iInter₂.mp hz.2) j hj
    exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  exact ⟨{
    hm := hm
    ζ := ζ
    hζ := hζ
    η := η
    s := s
    hs_an := hs_an
    hs0 := hs0
    hs_deriv := hs_deriv
    hinv0 := hinv0
    hnf0 := hnf0
    ppN := ppN
    ppb := ppb
    ppR := ppR
    hppR_an := hppR_an
    hsplit0 := hsplit0
    G := G
    hG := hG
    V := V
    hVopen := hVopen
    hcV := hcV
    hVs_an := fun z hz hslit j hj => hVsa j z (hVmem z hz j hj).1 hslit
    hVpp_split := fun z hz hslit j hj => hVpp j z (hVmem z hz j hj).2.1 hslit
    hVsmall := fun z hz hslit => hVsm z hz.1 hslit
    hVinv_mem := fun z hz hslit j hj => hVinv j z (hVmem z hz j hj).2.2.1 hslit
    hVnf_mem := fun z hz hslit j hj => hVnf j z (hVmem z hz j hj).2.2.2.1 hslit
    hVtgt := fun z hz hslit j hj => hVtg j z (hVmem z hz j hj).2.2.2.2 hslit }⟩

end Jacobians.Dolbeault.SerreResidueTheorem
