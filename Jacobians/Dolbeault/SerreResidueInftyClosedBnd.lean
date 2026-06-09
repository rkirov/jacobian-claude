/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueInftyCoherence
import Jacobians.Dolbeault.FormTraceBundleBridge

/-!
# Gate A `∑Res = 0` — discharging the branch-value boundedness `hbnd` (§VIII.3, the trace extends)

`Jacobians.Dolbeault.SerreResidueTheorem.residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyClosed`
(`SerreResidueInftyCoherence.lean`) reduced Gate A `∑Res = 0` (genus `0`, simple `∞`-poles, canonical
full-fibre selection) to *exactly* the discrete genericity bookkeeping plus the **branch-value
boundedness** `hbnd`:

> `∀ b₀ ∈ br, b₀ ∉ image cs → Tendsto (fun z => (z − b₀)·valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0)`,

the §VIII.3 / Miranda statement that the symmetric fibre-sum trace extends with at worst a removable /
simple-pole singularity across a branch value.  This file **discharges `hbnd`** for the canonical
selection, mirroring the already-proven off-centre analyticity discharge `hreg_canonical_of_offBranch`.

## The route (the architecturally-correct symmetric SUM, not colliding sheets)

At a branch value `b₀`, the canonical fibre selection `Φ` is degenerate (sheets collide), so the
moving-sum representation cannot be read *at* `b₀`.  Instead we read it at **nearby off-branch good
values** `z → b₀`, where the fibre is honest, and pass to the limit.  Concretely we feed the proven
chain

* `hevBr_of_regularData` (`FormTraceBundleBridge`) — assembles, from the *regular-value* sphere-sheet
  data near `b₀` (available off `image cs ∪ br` from `hgood_reg`/`hgmero_reg`) plus the local-form
  agreement `αBr = ω₀·g` at the fibre (`hαBrAgree`), the eventual sphere-sheet coherence near `b₀`;
* `hbnd_of_eventual_sphereCoherence` (`FormTraceRationalityNFPatched`) — turns that eventual coherence
  into `hbnd`, via the bundle-trace germ bridge `hbridgeBr_of_eventual_sphereCoherence` and the **proven
  axiom-clean bundle SUM boundedness** `TraceForm.traceLocalCoeff_mul_sub_tendsto_zero` (properness +
  finite-subcover over the fibre `F⁻¹{coe b₀}`, the per-preimage normal-form ratio `(F − b₀)/F' → 0`).

The branch values `b₀ ∈ br` that are *not* genuine branch points (`b₀ ∉ branchValues f`) are handled
trivially: there `coe b₀ ∉ branchLocus`, so the trace is *analytic* at `b₀` (`hreg_canonical_of_offBranch`
applied at `b₀`), hence continuous, and `(z − b₀)·trace(z) → 0·trace(b₀) = 0`.

## Soundness (non-circularity + junk-freeness)

`hbnd` is a genuine **local** boundedness/limit statement at the branch value `b₀`; it is *not* a disguise
of the global residue cancellation.  Its discharge bottoms out in the bundle SUM boundedness, whose proof
is the properness/finite-subcover/normal-form-ratio argument — it never references `∑Res = 0`.  The local
form `αBr = ω₀·g` near the fibre is a geometric input (the standard Mittag–Leffler/cutoff residual; `b₀`
is off the pole-values, so `g` is holomorphic at the whole fibre over `coe b₀`), not a residue identity —
exactly the kind of genericity bookkeeping the discrete hypotheses already carry.  The limit is taken on
the *punctured* filter `𝓝[≠] b₀`, never evaluating the literal value at `b₀`, so no junk-value defect.
Sanity witness: `f(z) = z²` at its branch value `0` — the fibre is the single double point `0`, the trace
has at worst a simple pole, and `(z − 0)·trace → 0`.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `hev_canonical_of_offBranch` — the eventual sphere-sheet coherence at a genuine branch value, from the
  regular-value `g`-data + the local-form agreement (the `hev` input of `hbnd_of_eventual_sphereCoherence`).
* `hbnd_canonical_of_offBranch` — the branch-value boundedness `hbnd` for the canonical selection, with
  genuine branch values discharged via the bundle SUM and non-branch `br`-values via analyticity.
* `residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyClosed_bnd` — Gate A `∑Res = 0`
  (genus `0`, simple `∞`-poles, canonical selection) resting on **only the discrete genericity
  bookkeeping** (no `hbnd`, no `hcoh_geom`): `hbnd` is discharged here, `hcoh_geom` upstream.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3, pp. 251–256 (the trace is
  single-valued by symmetry; the SUM extends across branch points; Lemma 3.2).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22, §10, §17.
* `Jacobians/TraceForm.lean` (`traceLocalCoeff_mul_sub_tendsto_zero` — the proven bundle SUM boundedness).
* `Jacobians/Dolbeault/FormTraceBundleBridge.lean` (`hevBr_of_regularData`).
* `Jacobians/Dolbeault/FormTraceRationalityNFPatched.lean` (`hbnd_of_eventual_sphereCoherence`).
* `Jacobians/Dolbeault/SerreResidueDirectGenus0GermDischarge.lean` (`hreg_canonical_of_offBranch`,
  the off-centre analyticity discharge this file mirrors).
* `docs/serre_17_build_plan.md`, `docs/miranda_VIII3_confirmation_2026-06-08.md`, `human_input.md`.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTraceFullFibre
  Jacobians.Dolbeault.FormTraceMovingFibre RiemannSphere

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ## The eventual sphere-sheet coherence at a branch value (the `hev` input)

The §VIII.3 boundedness route reads the moving-sum representation at **nearby off-branch good values**.
We assemble the eventual sphere-sheet coherence near a branch value `b₀` from the regular-value data
the capstone already supplies (`hgood_reg`/`hgmero_reg`, giving sphere systems off `image cs ∪ br`) and
the one genuine residual — the local-form agreement `αBr = ω₀·g` at the fibre.  This mirrors the
off-centre analyticity helper `hreg_canonical_of_offBranch`, but produces the *eventual* coherence on
`𝓝[≠] b₀` (the input to `hbnd_of_eventual_sphereCoherence`) rather than analyticity *at* a single value. -/

/-- **The eventual sphere-sheet coherence at a branch value, for the canonical selection.**  At a value
`b₀` off the pole-centres, the eventual sphere-sheet coherence

> `∀ᶠ z in 𝓝[≠] b₀, ∃ S hderiv hmero, valueChartTrace ω₀ f Φ z = sphere-fibre trace at z ∧ αBr = ω₀·g`

holds, given:

* `hgood_reg`/`hgmero_reg` — every value off `image cs ∪ br` is a good value with near-value
  `g`-meromorphy (`br ⊇ branchValues f`, so such values are off the branch locus);
* `hαBrAgree` — `αBr = ω₀·g` at **every fibre point** `F⁻¹(coe z)` for `z` near `b₀` (the genuine
  geometric residual: `b₀` is off the pole-values, so `g` is holomorphic at the whole fibre over `coe
  b₀`, and a global holomorphic `αBr` agreeing with `ω₀·g` near the fibre exists by the standard
  Mittag–Leffler/cutoff construction).  Stated at *every* fibre point — the canonical sphere-sheet
  points `S.sheet i (coe z)` are fibre points (`sheet_section`), so the per-sheet agreement specializes.

The sphere systems and the canonical-fibre conditions are built inline from `exists_sphereSheetSystem`
(off-branch) and `canonicalFibreSelection_hΦinj`/`hΦrange`; the meromorphy at the sphere-sheet fibre
points is transferred from the full-fibre `g`-data exactly as in `hreg_canonical_of_offBranch`.  This is
the `hev` argument `hbnd_of_eventual_sphereCoherence` consumes. -/
theorem hev_canonical_of_offBranch (hdiv : (f.div : Divisor X) ≠ 0) {m : ℕ} {cs : Fin m → ℂ}
    {br : Finset ℂ} (hbr : branchValues f hdiv ⊆ br) {b₀ : ℂ}
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (αBr : HolomorphicOneForms X)
    (hαBrAgree : ∀ᶠ z in 𝓝[≠] b₀, ∀ y : X, f.toRiemannSphere y = (((z : ℂ) : RiemannSphere)) →
      αBr.toFun y = g y • ω₀.toFun y) :
    ∀ᶠ z in 𝓝[≠] b₀,
      ∃ (S : Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)))
        (hderiv : ∀ i, deriv (fun w => f.holoRepr
            ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
          ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
            (S.sheet i (((z : ℂ) : RiemannSphere)))) ≠ 0)
        (_hmero : ∀ i, MeromorphicAt
          (fun w => g ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere)))).symm w))
          ((chartAt ℂ (S.sheet i (((z : ℂ) : RiemannSphere))))
            (S.sheet i (((z : ℂ) : RiemannSphere))))),
        valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z
            = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv _hmero)).traceCoeff z ∧
        (∀ i, αBr.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))
          = g (S.sheet i (((z : ℂ) : RiemannSphere)))
            • ω₀.toFun (S.sheet i (((z : ℂ) : RiemannSphere)))) := by
  classical
  -- The off-branch sphere system at each regular value `z` (off `image cs ∪ br`).
  set Sreg : ∀ z, z ∉ Finset.univ.image cs ∪ br →
      Jacobians.LocalSheetSystem f.toRiemannSphere (((z : ℂ) : RiemannSphere)) := fun z hz =>
    (exists_sphereSheetSystem f (exists_orderAtPoint_ne_zero f hdiv)
      (coe_notMem_branchLocus_of_notMem_branchValues f hdiv
        (fun h => (fun hmem => hz (Finset.mem_union_right _ hmem)) (hbr h)))).some with hSreg
  -- `coe z ∉ branchLocus` for `z ∉ image cs ∪ br`.
  have hoff : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br),
      (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere := fun z hz =>
    coe_notMem_branchLocus_of_notMem_branchValues f hdiv
      (fun h => (fun hmem => hz (Finset.mem_union_right _ hmem)) (hbr h))
  -- The sphere-sheet fibre point lies in the full fibre `F⁻¹(coe z)` (good value); its `g`-data follows.
  have hmeroReg : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
      MeromorphicAt (fun w => g
          ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).symm w))
        ((chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))))
          ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))) := by
    intro z hz i
    have hfib : (Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)) ∈
        f.toRiemannSphere ⁻¹' {(((z : ℂ) : RiemannSphere))} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact (Sreg z hz).sheet_section i _ (Sreg z hz).mem_V
    rw [← canonicalFibreSelection_xs_range g f hdiv (hgood_reg z hz),
      canonicalFibreSelection_eq_ofFullFibre g f hdiv (hgood_reg z hz)] at hfib
    obtain ⟨j, hj⟩ := hfib
    have hpt : (Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)) = fullFibreEnum f hdiv z j := hj.symm
    rw [hpt]; exact (hgood_reg z hz).2 j
  -- Apply the proven assembly `hevBr_of_regularData` (with `Φ := canonicalFibreSelection`).
  refine hevBr_of_regularData ω₀ g f (canonicalFibreSelection g f hdiv) cs br αBr Sreg
    -- `hderivReg`: each fibre point is a regular point (off-branch local injectivity).
    (fun z hz i => sheet_holoRepr_deriv_ne_zero f hdiv (hoff z hz)
      ((Sreg z hz).sheet_section i _ (Sreg z hz).mem_V))
    hmeroReg
    -- `hΦinjReg` / `hΦrangeReg`: the canonical selection's full-fibre conditions near each regular `z`.
    (fun z hz => canonicalFibreSelection_hΦinjReg g f hdiv (hoff z hz) (hgmero_reg z hz))
    (fun z hz => canonicalFibreSelection_hΦrangeReg g f hdiv (hoff z hz) (hgmero_reg z hz))
    -- `hsheetInjReg`: intrinsic to any `LocalSheetSystem` (`sheet_inj` over the open base `S.V`).
    (fun z hz => by
      have hVnhds : ((fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' (Sreg z hz).V) ∈ 𝓝 z :=
        (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds
          ((Sreg z hz).isOpen_V.mem_nhds (Sreg z hz).mem_V)
      filter_upwards [hVnhds] with b' hb'
      exact (Sreg z hz).sheet_inj (((b' : ℂ) : RiemannSphere)) hb')
    -- `hsheetMemReg`: each sheet eventually passes through its own chart source (continuity at base).
    (fun z hz => by
      have hev : ∀ i : Fin (Sreg z hz).n, ∀ᶠ b' in 𝓝 z,
          (Sreg z hz).sheet i (((b' : ℂ) : RiemannSphere)) ∈
            (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source := by
        intro i
        have hcont : ContinuousAt ((Sreg z hz).holoReprSheet i) z :=
          ((Sreg z hz).holoReprSheet_contMDiffAt i).continuousAt
        have hsrc : (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source ∈
            𝓝 ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere))) :=
          (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).open_source.mem_nhds
            (mem_chart_source ℂ _)
        have := hcont.preimage_mem_nhds (show
          (chartAt ℂ ((Sreg z hz).sheet i (((z : ℂ) : RiemannSphere)))).source ∈
            𝓝 ((Sreg z hz).holoReprSheet i z) from hsrc)
        filter_upwards [this] with b' hb' using hb'
      rw [eventually_all]; exact hev)
    -- `hαBrAgree` at the sphere-sheet fibre points: each `Sreg.sheet i (coe z)` maps to `coe z`
    -- (`sheet_section`), so the fibre-point agreement specializes.
    (by
      filter_upwards [hαBrAgree] with z hz hz_reg i
      exact hz _ ((Sreg z hz_reg).sheet_section i _ (Sreg z hz_reg).mem_V))

/-! ## The branch-value boundedness `hbnd` (the §VIII.3 close, canonical selection)

`hbnd` for the canonical selection dispatches each `b₀ ∈ br` (off the pole-centres) by whether it is a
*genuine* branch point:

* `b₀ ∈ branchValues f` (`coe b₀ ∈ branchLocus`): the **bundle SUM** route — the eventual sphere-sheet
  coherence `hev_canonical_of_offBranch` feeds `hbnd_of_eventual_sphereCoherence`, whose boundedness is
  the proven axiom-clean `traceLocalCoeff_mul_sub_tendsto_zero`.
* `b₀ ∈ br \ branchValues f` (`coe b₀ ∉ branchLocus`): a regular value, where `valueChartTrace` is
  **analytic** at `b₀` (`hreg_canonical_at_goodValue`, the moving-datum coherence), hence continuous, so
  `(z − b₀)·trace(z) → 0·trace(b₀) = 0`. -/

/-- **Analyticity of the canonical trace at a good value** (the moving-datum coherence, off any centre
set).  At a value `w` that is a good value (`coe w` off the branch locus, `g`-meromorphic at the full
fibre) with the near-value `g`-meromorphy `hgmero_w` and the fibre points non-poles of `α` (so `g` is
analytic there, `hg_an`), the canonical full-fibre trace is `AnalyticAt w`.  This is
`analyticAt_valueChartTrace_of_movingDatum` applied to `movingCoherenceDatum_canonical`, the same engine
`hreg_canonical_of_offBranch` uses — here exposed at an *individual* good value (no centre exclusion). -/
theorem hreg_canonical_at_goodValue (hdiv : (f.div : Divisor X) ≠ 0) {w : ℂ}
    (hw_good : GoodValue g f hdiv w)
    (hgmero_w : ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an : ∀ y : X, f.toRiemannSphere y = (((w : ℂ) : RiemannSphere)) →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ y).symm z)) ((chartAt ℂ y) y)) :
    AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) w := by
  classical
  set hoff := hw_good.1 with hoffdef
  set S : Jacobians.LocalSheetSystem f.toRiemannSphere (((w : ℂ) : RiemannSphere)) :=
    (exists_sphereSheetSystem f (exists_orderAtPoint_ne_zero f hdiv) hoff).some with hS
  -- The reference sheet-fibre `g`-meromorphy at `coe w` (good value ⟹ full fibre = sphere fibre).
  have hmeroS : ∀ k, MeromorphicAt
      (fun z => g ((chartAt ℂ (S.sheet k (((w : ℂ) : RiemannSphere)))).symm z))
      ((chartAt ℂ (S.sheet k (((w : ℂ) : RiemannSphere)))) (S.sheet k (((w : ℂ) : RiemannSphere)))) := by
    intro k
    have hfib : S.sheet k (((w : ℂ) : RiemannSphere)) ∈
        f.toRiemannSphere ⁻¹' {(((w : ℂ) : RiemannSphere))} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff]; exact S.sheet_section k _ S.mem_V
    rw [← canonicalFibreSelection_xs_range g f hdiv hw_good,
      canonicalFibreSelection_eq_ofFullFibre g f hdiv hw_good] at hfib
    obtain ⟨j, hj⟩ := hfib
    have hpt : S.sheet k (((w : ℂ) : RiemannSphere)) = fullFibreEnum f hdiv w j := hj.symm
    rw [hpt]; exact hw_good.2 j
  set C : MovingCoherenceDatum ω₀ g f (canonicalFibreSelection g f hdiv) w :=
    movingCoherenceDatum_canonical hdiv hoff S hmeroS hgmero_w with hC
  -- The fixed fibre points `C.D.xs k` lie in the full fibre `F⁻¹(coe w)` (its range = canonical range =
  -- fibre at the good value `w`), so `g` is analytic there by `hg_an`.
  refine analyticAt_valueChartTrace_of_movingDatum C (fun k => ?_)
  have himg : Finset.univ.image C.D.xs
      = Finset.univ.image (canonicalFibreSelection g f hdiv w).xs := by
    rw [hC]
    exact movingCoherenceDatum_canonical_D_image (ω₀ := ω₀) hdiv hoff S hmeroS hgmero_w hw_good
  have hmemImg : C.D.xs k ∈ Finset.univ.image (canonicalFibreSelection g f hdiv w).xs := by
    rw [← himg]; exact Finset.mem_image_of_mem C.D.xs (Finset.mem_univ k)
  rw [Finset.mem_image] at hmemImg
  obtain ⟨j, _, hj⟩ := hmemImg
  have hfib : f.toRiemannSphere (C.D.xs k) = (((w : ℂ) : RiemannSphere)) := by
    rw [← hj]
    have : (canonicalFibreSelection g f hdiv w).xs j ∈
        Set.range (canonicalFibreSelection g f hdiv w).xs := ⟨j, rfl⟩
    rw [canonicalFibreSelection_xs_range g f hdiv hw_good] at this
    rwa [Set.mem_preimage, Set.mem_singleton_iff] at this
  exact hg_an _ hfib

/-- **`hbnd` for the canonical selection at a `br`-value off the pole-centres.**  Both the genuine
branch-value (bundle SUM) and the regular `br`-value (analyticity) cases are covered:

* if `b₀ ∈ branchValues f`, the bundle SUM route via `hev_canonical_of_offBranch` +
  `hbnd_of_eventual_sphereCoherence` (resting on `traceLocalCoeff_mul_sub_tendsto_zero`), needing the
  local form `αBr` agreeing with `ω₀·g` at the fibre near `b₀` (`hαBrAgree`);
* if `b₀ ∉ branchValues f`, the trace is analytic at `b₀` (`hreg_canonical_at_goodValue`, needing the
  good-value `g`-data `hgood_b₀`/`hgmero_b₀`/`hg_an_b₀`), hence continuous, giving `(z − b₀)·trace → 0`. -/
theorem hbnd_canonical_of_offBranch (hdiv : (f.div : Divisor X) ≠ 0) {m : ℕ} {cs : Fin m → ℂ}
    {br : Finset ℂ} (hbr : branchValues f hdiv ⊆ br) {b₀ : ℂ} (_hb₀br : b₀ ∈ br)
    (_hb₀cs : b₀ ∉ Finset.univ.image cs)
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    -- Genuine-branch data: a local form `αBr` agreeing with `ω₀·g` at the fibre near `b₀`.
    (αBr : HolomorphicOneForms X)
    (hαBrAgree : ∀ᶠ z in 𝓝[≠] b₀, ∀ y : X, f.toRiemannSphere y = (((z : ℂ) : RiemannSphere)) →
      αBr.toFun y = g y • ω₀.toFun y)
    -- Regular-`br`-value data (used only when `b₀ ∉ branchValues f`): the good-value `g`-data at `b₀`.
    (hgood_b₀ : b₀ ∉ branchValues f hdiv → GoodValue g f hdiv b₀)
    (hgmero_b₀ : b₀ ∉ branchValues f hdiv → ∀ᶠ b' in 𝓝 b₀, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an_b₀ : b₀ ∉ branchValues f hdiv → ∀ y : X,
      f.toRiemannSphere y = (((b₀ : ℂ) : RiemannSphere)) →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ y).symm z)) ((chartAt ℂ y) y)) :
    Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv) z)
      (𝓝[≠] b₀) (𝓝 0) := by
  by_cases hb₀branch : b₀ ∈ branchValues f hdiv
  · -- Genuine branch point: the bundle SUM route.
    refine hbnd_of_eventual_sphereCoherence ω₀ g f (canonicalFibreSelection g f hdiv) αBr
      (hncF_of_div_ne_zero f hdiv) ((mem_branchValues f hdiv).mp hb₀branch) ?_
    exact hev_canonical_of_offBranch hdiv hbr hgood_reg hgmero_reg αBr hαBrAgree
  · -- Regular `br`-value: the trace is analytic at `b₀`, hence `(z − b₀)·trace → 0` by continuity.
    have han : AnalyticAt ℂ (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) b₀ :=
      hreg_canonical_at_goodValue hdiv (hgood_b₀ hb₀branch) (hgmero_b₀ hb₀branch) (hg_an_b₀ hb₀branch)
    have hcont : ContinuousAt (valueChartTrace ω₀ f (canonicalFibreSelection g f hdiv)) b₀ :=
      han.continuousAt
    -- `(z − b₀) → 0` and `trace z → trace b₀`, so the product `→ 0 · trace b₀ = 0`.
    have hsub : Tendsto (fun z : ℂ => z - b₀) (𝓝[≠] b₀) (𝓝 0) := by
      have : Tendsto (fun z : ℂ => z - b₀) (𝓝 b₀) (𝓝 0) := by
        have := (continuous_sub_right b₀).tendsto b₀
        simpa using this
      exact this.mono_left nhdsWithin_le_nhds
    have hmul := hsub.mul (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    simpa using hmul

/-! ## The genus-`0` capstone with `hbnd` discharged — Gate A rests on genericity alone

Wiring `hbnd_canonical_of_offBranch` into `residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyClosed`,
the branch-value boundedness `hbnd` is **discharged**.  Gate A `∑Res = 0` (genus `0`, simple `∞`-poles,
canonical selection) now rests on **only the discrete genericity bookkeeping**: the off-branch
pole-values, good values, the near-value `g`-meromorphy, `g` holomorphic off the poles, the simple
`∞`-poles, and the per-branch local form `αBr` agreeing with `ω₀·g` at the fibre (the standard
Mittag–Leffler/cutoff residual).  No `hbnd`, no `hcoh_geom` — both are now theorems. -/

/-- **Gate A `∑Res = 0` (genus `0`, simple `∞`-poles, canonical selection) — `hbnd` AND the
`∞`-coherence FULLY DISCHARGED.**  Identical to
`residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyClosed`, with the branch-value
boundedness `hbnd` *constructed internally* via `hbnd_canonical_of_offBranch`:

* genuine branch values `b₀ ∈ branchValues f` use the **proven axiom-clean bundle SUM boundedness**
  (`traceLocalCoeff_mul_sub_tendsto_zero`, the §VIII.3 symmetric SUM extends across branch points), fed
  by the eventual sphere-sheet coherence assembled from the regular-value `g`-data near `b₀` and the
  local-form agreement `hαBrAgree`;
* regular `br`-values `b₀ ∉ branchValues f` use analyticity of the trace at `b₀` (the moving-datum
  coherence), needing the good-value `g`-data `hgood_brOff`/`hgmero_brOff` there.

The two new genericity inputs over `…_inftyClosed` are exactly: the per-branch local form `αBr`
agreeing with `ω₀·g` at the fibre near each branch value (`αBr`/`hαBrAgree`), and the good-value
`g`-data at the *non-branch* `br`-values (`hgood_brOff`/`hgmero_brOff`, vacuous when `br =
branchValues f`).  `hg_an` at the non-branch `br`-fibres is derived internally from `hg_an_offpoles`
(non-pole-value ⟹ non-pole fibre points).  **Gate A now rests on genericity bookkeeping alone.** -/
theorem residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyClosed_bnd
    (hdiv : (f.div : Divisor X) ≠ 0)
    (hgood : ∀ p, (∃ a ∈ poles, f.toRiemannSphere a = (((p : ℂ) : RiemannSphere))) →
      GoodValue g f hdiv p)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ) (hbr : branchValues f hdiv ⊆ br)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hoff_cs : ∀ i, (((cs i : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hc_good : ∀ i, GoodValue g f hdiv (cs i))
    (hgmero : ∀ i, ∀ᶠ b' in 𝓝 (cs i), ∀ j,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hgood_reg : ∀ w ∉ Finset.univ.image cs ∪ br, GoodValue g f hdiv w)
    (hgmero_reg : ∀ w (_hw : w ∉ Finset.univ.image cs ∪ br), ∀ᶠ b' in 𝓝 w, ∀ j,
      MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
        ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j)))
    (hg_an_offpoles : ∀ x : X, x ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x))
    (hsimpleInf : ∀ i, f.orderAtPoint (inftyFibreEnum f i) = -1)
    (hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (inftyFibreEnum f i)).symm z))
      ((chartAt ℂ (inftyFibreEnum f i)) (inftyFibreEnum f i)))
    (hnonpole_inf_an : ∀ k, inftyFibreEnum f k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (inftyFibreEnum f k)).symm z))
        ((chartAt ℂ (inftyFibreEnum f k)) (inftyFibreEnum f k)))
    -- The per-branch local form agreeing with `ω₀·g` at the fibre (the genuine genericity residual).
    (αBr : ℂ → HolomorphicOneForms X)
    (hαBrAgree : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      ∀ᶠ z in 𝓝[≠] b₀, ∀ y : X, f.toRiemannSphere y = (((z : ℂ) : RiemannSphere)) →
        (αBr b₀).toFun y = g y • ω₀.toFun y)
    -- The good-value `g`-data at the non-branch `br`-values (vacuous when `br = branchValues f`).
    (hgood_brOff : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs → b₀ ∉ branchValues f hdiv →
      GoodValue g f hdiv b₀)
    (hgmero_brOff : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs → b₀ ∉ branchValues f hdiv →
      ∀ᶠ b' in 𝓝 b₀, ∀ j,
        MeromorphicAt (fun u => g ((chartAt ℂ (fullFibreEnum f hdiv b' j)).symm u))
          ((chartAt ℂ (fullFibreEnum f hdiv b' j)) (fullFibreEnum f hdiv b' j))) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_ofCanonicalSimpleInfty_genus0_germ_CfullHreg_inftyClosed hdiv hgood m cs ρ hcs_ball
    hcs_inj br hbr hcenters_cs hoff_cs hc_good hgmero hgood_reg hgmero_reg hg_an_offpoles hsimpleInf
    hmeroInf hnonpole_inf_an
    (fun b₀ hb₀br hb₀cs =>
      hbnd_canonical_of_offBranch hdiv hbr hb₀br hb₀cs hgood_reg hgmero_reg (αBr b₀)
        (hαBrAgree b₀ hb₀br hb₀cs)
        (hgood_brOff b₀ hb₀br hb₀cs) (hgmero_brOff b₀ hb₀br hb₀cs)
        -- `hg_an` at the non-branch `br`-fibres: `b₀ ∉ image cs` ⟹ non-pole-value ⟹ non-pole fibre.
        (fun _hbv y hy => hg_an_offpoles y (notMem_poles_of_fibrePoint_offCentres hcenters_cs hb₀cs hy)))

end Jacobians.Dolbeault.SerreResidueTheorem
