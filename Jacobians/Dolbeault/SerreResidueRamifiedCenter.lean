/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueDirectGenus0Germ
import Jacobians.RamifiedResidueChangeOfVariables

/-!
# Gate A `∑Res = 0` — admitting *ramified* finite pole-value centres (Miranda §VIII.3 ramified)

The genus-`0` close `residueTheorem_ofCanonicalSimpleInfty_genus0_germ`
(`SerreResidueDirectGenus0Germ.lean`) consumes the per-centre full-fibre moving coherence `Cfull i`
*only* to obtain, at each finite pole-value centre `cs i`, the **two facts** the principal-part close
needs (see `docs/gate_a_hoff_cs_localization_2026-06-09.md`):

* **(A) meromorphy** `MeromorphicAt (valueChartTracePatched ω₀ f Φ br) (cs i)`;
* **(B) residue identity** `resAt (valueChartTracePatched ω₀ f Φ br) (cs i)
    = ∑_{p ∈ pole-fibre} formFnResidue ω₀ g p`.

In the *unramified* case (`cs i` off `f`'s branch locus, the `hoff_cs` hypothesis), `Cfull i` realises
both facts through the chain `FibreRegularData → fibreTrace → resAt_traceCoeff'` (the unramified Lemma
3.2), all of which bake in `deriv ≠ 0` at every fibre point.  At a **ramified** centre the fibre points
*are* the ramification points (`deriv = 0`), so that whole route is structurally impossible — but the
two facts (A)/(B) are *still true*: they are exactly the **ramified Lemma 3.2** (Miranda §VIII.3, (3.1)),
now proven as the algebraic `m`-sheet-sum atom `Jacobians.RamifiedTrace.resAt_laurentTraceCoeff` /
`meromorphicAt_laurentTraceCoeff`.

This file performs the *structural integration* the localization called for, in two layers.

## Layer 1 — the fact-based discharge (axiom-clean, no new analysis)

`globalTraceData_of_genus0_germ_facts` is `globalTraceData_of_genus0_germ` with the `Cfull`
field-group (`Cfull`, `hfull_inj`, `hpole_image`, `hnonpole_an`) **replaced** by the two facts (A)/(B)
taken *directly as hypotheses* per centre — exactly the abstraction boundary at which a ramified centre
plugs in.  This is a pure refactor of the existing proof (the `Cfull` route is one way to supply (A)/(B);
the ramified atom is another), so it is sorry-free and axiom-clean.  The unramified `…_germ` capstone is
recovered as the special case where (A)/(B) come from `Cfull` (sanity: `…_facts_of_Cfull`).

## Layer 2 — the ramified centre provider (the genuine §VIII.3 content)

`RamifiedCenterFacts` bundles facts (A)/(B) at one centre, and `RamifiedCenterFacts.ofRamifiedTrace`
*derives* them from the genuine ramified ingredients via the proven atom:

* a `FibreRamifiedData` — the preimages `pⱼ ∈ F⁻¹(coe c)` with multiplicities `mⱼ` (`∑ mⱼ = deg`),
  **allowing `deriv = 0`** (the ramified analogue of `FibreRegularData`);
* the **geometric-trace ramified identification** (the one hard analytic piece, Forster §5 local normal
  form `f = wᵐ`): the geometric trace germ `valueChartTrace ω₀ f Φ` near `c` germ-equals the algebraic
  `m`-sheet-sum trace of the per-preimage chart integrands.  This is the ramified analogue of the
  unramified `MovingCoherenceDatum.coherent_punctured`; it is supplied as a precise hypothesis
  (`hcoh`).  The atom then discharges (A) (`meromorphicAt_laurentTraceCoeff`) and (B)
  (`resAt_laurentTraceCoeff`, summed over the mixed-multiplicity fibre).

The geometric branch ↔ `z = wᵐ` normal-form identification `hcoh` is the genuine remaining analytic
build (the ramified analogue of `exists_planar_section`); it is stated precisely and **not asserted
without the normal form** (no false/circular field, no custom axiom).  The atom — the residue/algebra
core — is *done* (`Jacobians/RamifiedResidueChangeOfVariables.lean`).

## ⚠ Soundness

Every statement about the trace is the `m`-sheet **SUM** (a single sheet's residue under `wᵐ` is
`m·Res_w`, FALSE; the atom's roots-of-unity factor `∑_{j<m}(ζʲ)⁰ = m` cancels the chain-rule `1/m`).
`hcoh` is the genuine geometric content (the manifold cover *is* `z = wᵐ` at a ramification point), not
a disguised residue identity; at an *unramified* centre (`m = 1`) it reduces to the unramified moving
coherence.  No `hoff_cs` reappears under another name; no full RR is used (no circularity).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3, pp. 252–253 (the trace `Tr`,
  formula **(3.1)**, Lemma 3.2 ramified case).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §5 (local normal form `z = wᵐ` at a ramification
  point of multiplicity `m`).
* `Jacobians/RamifiedResidueChangeOfVariables.lean` (the proven ramified residue atom).
* `docs/gate_a_hoff_cs_localization_2026-06-09.md` (the 3 consumption sites + the 2 consumed facts).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTraceLiouville
  Jacobians.Dolbeault.FormTraceMovingFibre Jacobians.Dolbeault.FormTraceFullFibre
  Jacobians.Dolbeault.FormTracePrincipalPart

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ## Layer 1 — the fact-based discharge of the finite centres

`globalTraceData_of_genus0_germ` uses the per-centre full-fibre coherence `Cfull i` at *exactly* two
places: the meromorphy `hT_mero i` (fact A) and the finite Lemma-3.2 residue identity (fact B, via
`hres_fin_of_fullFibreCoherence`).  Replacing the whole `Cfull` field-group by these two facts as
direct per-centre hypotheses gives the identical `GlobalTraceData` — the abstraction boundary at which a
ramified centre (whose `Cfull` cannot exist) supplies (A)/(B) from the ramified atom instead. -/

/-- **`GlobalTraceData` from the per-centre facts (A)/(B), `Cfull`-free.**  Identical to
`globalTraceData_of_genus0_germ` with the `Cfull` field-group (`Cfull`/`hfull_inj`/`hpole_image`/
`hnonpole_an`) replaced by, at each finite pole-value centre `cs i`:

* `hT_mero_cs i` — **(A)** `MeromorphicAt (valueChartTracePatched ω₀ f Φ br) (cs i)`;
* `hres_fin_cs i` — **(B)** `resAt (valueChartTracePatched ω₀ f Φ br) (cs i) = ∑ⱼ formFnResidue ω₀ g
  ((D (cs i)).xs j)` (the pole-fibre residue sum).

Everything else (`D` the pole sub-fibre, its enumeration fields, `hcenters_cs`, the off-centre
analyticity `hreg`/`hbnd`, and the entire `∞`-group) is verbatim.  Producing one ⇒ Gate A `∑Res = 0`.
The unramified capstone supplies (A)/(B) from `Cfull`; a ramified centre supplies them from the
ramified atom — both feed *this* def. -/
noncomputable def globalTraceData_of_genus0_germ_facts
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs) (br : Finset ℂ)
    (hreg : ∀ w ∉ Finset.univ.image cs ∪ br, AnalyticAt ℂ (valueChartTrace ω₀ f Φ) w)
    (hbnd : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
      Tendsto (fun z => (z - b₀) * valueChartTrace ω₀ f Φ z) (𝓝[≠] b₀) (𝓝 0))
    (D : (p : ℂ) → FibreRegularData g f p)
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (D p).xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    -- (A): meromorphy of the patched trace at each finite pole-value centre.
    (hT_mero_cs : ∀ i, MeromorphicAt (valueChartTracePatched ω₀ f Φ br) (cs i))
    -- (B): the finite Lemma-3.2 residue identity at each centre (the pole-fibre residue sum).
    (hres_fin_cs : ∀ i, resAt (valueChartTracePatched ω₀ f Φ br) (cs i)
      = ∑ j, formFnResidue ω₀ g ((D (cs i)).xs j))
    (Dinf_full : InftyFibreDataNF g f)
    (hcoh_full : recipCoeff (valueChartTracePatched ω₀ f Φ br)
      =ᶠ[𝓝[≠] 0] recipCoeff (inftyMovingSumNF ω₀ f Dinf_full))
    (hfullInf_inj : Function.Injective Dinf_full.xs)
    {ιInfP : Type} [Fintype ιInfP] (xsInf_po : ιInfP → X)
    (hpoInf_inj : Function.Injective xsInf_po)
    (hpoInf_mem : ∀ j, xsInf_po j ∈ poles ∧ f.toRiemannSphere (xsInf_po j) = OnePoint.infty)
    (hpoInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ j, xsInf_po j = a)
    (hpole_image_inf : (Finset.univ.image Dinf_full.xs).filter (· ∈ poles)
      = Finset.univ.image xsInf_po)
    (hnonpole_inf_an : ∀ k, Dinf_full.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ (Dinf_full.xs k)).symm z))
        ((chartAt ℂ (Dinf_full.xs k)) (Dinf_full.xs k))) :
    GlobalTraceData ω₀ g f poles := by
  classical
  set T := valueChartTracePatched ω₀ f Φ br with hT
  -- Principal-part `LaurentForm` from the per-centre meromorphy (A).
  set hPP := exists_laurentForm_principalPart cs ρ hcs_ball hcs_inj hT_mero_cs with hPP_def
  set L := hPP.choose with hL_def
  have hLcenters : Finset.univ.image L.a = Finset.univ.image cs := hPP.choose_spec.1
  have hLrem : ∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧ (T - L.R) =ᶠ[𝓝[≠] (cs j)] R :=
    hPP.choose_spec.2
  -- The remainder `T − L.R` is germ-regular (FREE): analytic off the centres + the pole removed at them.
  have hT_off : ∀ z ∉ Finset.univ.image L.a, AnalyticAt ℂ T z := by
    intro z hz; rw [hLcenters] at hz; exact hT_off_patched hreg hbnd hz
  have hLR_off : ∀ z ∉ Finset.univ.image L.a, AnalyticAt ℂ L.R z := by
    intro z hz
    show AnalyticAt ℂ (fun w => ∑ p, L.c p * (w - L.a p) ^ L.n p) z
    refine Finset.analyticAt_fun_sum _ (fun p _ => ?_)
    refine analyticAt_const.mul ?_
    have hbase : AnalyticAt ℂ (fun w : ℂ => w - L.a p) z := analyticAt_id.sub analyticAt_const
    have hzap : z ≠ L.a p := fun h => hz (h ▸ Finset.mem_image_of_mem L.a (Finset.mem_univ p))
    exact hbase.zpow (sub_ne_zero.mpr hzap)
  have hoff_rem : ∀ z ∉ Finset.univ.image L.a, AnalyticAt ℂ (T - L.R) z := fun z hz =>
    (hT_off z hz).sub (hLR_off z hz)
  have hrem : ∀ p ∈ Finset.univ.image L.a,
      ∃ R : ℂ → ℂ, AnalyticAt ℂ R p ∧ (T - L.R) =ᶠ[𝓝[≠] p] R := by
    intro p hp; rw [hLcenters] at hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp; exact hLrem i
  refine
    { L := L
      D := D
      hxs_inj := hxs_inj
      hxs_mem := hxs_mem
      hxs_surj := hxs_surj
      hcenters := by rw [hLcenters]; exact hcenters_cs
      hL32 := ?_
      infty_eq := ?_ }
  · -- Finite Lemma 3.2 from fact (B): the centre's trace residue is the pole-fibre `formFnResidue` sum.
    intro p hp
    rw [hLcenters] at hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    have hLHS :
        (∑ j, resAt ((fibreTrace ω₀ f (D (cs i))).coeff j) ((fibreTrace ω₀ f (D (cs i))).pre j))
          = ∑ j, formFnResidue ω₀ g ((D (cs i)).xs j) :=
      Finset.sum_congr rfl (fun j _ => resAt_fibreTrace_coeff ω₀ f (D (cs i)) j)
    obtain ⟨R, hR_an, hR_eq⟩ := hLrem i
    rw [hLHS, ← hres_fin_cs i, resAt_eq_laurentR_of_principalPart (hT_mero_cs i) hR_an hR_eq]
  · -- The `∞`-residue identity via germ-Cauchy (the `hcont_int`-free route), verbatim.
    exact infty_eq_of_remainderRegular hoff_rem hrem Dinf_full hcoh_full hfullInf_inj xsInf_po
      hpoInf_inj hpoInf_mem hpoInf_surj hpole_image_inf
      (fun k hk => formFnResidue_eq_zero_of_analyticAt ω₀ g _ (hnonpole_inf_an k hk))

/-! ### Layer 1, sanity — the unramified `Cfull` route is one way to supply (A)/(B)

The unramified capstone supplies the two facts from the per-centre full-fibre moving coherence `Cfull i`:
fact (A) is `(meromorphicAt_traceCoeff_fibreTrace (Cfull i).D).congr (Cfull.coherent_punctured …)`, fact
(B) is `hres_fin_of_fullFibreCoherence`.  We expose this as a sanity lemma confirming `…_facts` is a
*generalisation* of `…_germ` (the ramified atom supplies the same two facts at a ramified centre). -/

/-- **The (A)/(B) facts from a per-centre full-fibre moving coherence `Cfull i`** (the unramified
route).  Confirms `globalTraceData_of_genus0_germ_facts` subsumes the unramified `Cfull`-based discharge:
`Cfull i` supplies fact (A) (`hT_mero_cs`, via `coherent_punctured` + `meromorphicAt_traceCoeff_fibreTrace`)
and fact (B) (`hres_fin_cs`, via `hres_fin_of_fullFibreCoherence`). -/
theorem facts_of_Cfull {Φ : (b : ℂ) → FibreRegularData g f b} {br : Finset ℂ} {m : ℕ} {cs : Fin m → ℂ}
    (D : (p : ℂ) → FibreRegularData g f p)
    (Cfull : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (hfull_inj : ∀ i, Function.Injective (Cfull i).D.xs)
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hpole_image : ∀ i, (Finset.univ.image (Cfull i).D.xs).filter (· ∈ poles)
      = Finset.univ.image (D (cs i)).xs)
    (hnonpole_an : ∀ i, ∀ k, (Cfull i).D.xs k ∉ poles →
      AnalyticAt ℂ (fun z => g ((chartAt ℂ ((Cfull i).D.xs k)).symm z))
        ((chartAt ℂ ((Cfull i).D.xs k)) ((Cfull i).D.xs k))) :
    (∀ i, MeromorphicAt (valueChartTracePatched ω₀ f Φ br) (cs i)) ∧
      (∀ i, resAt (valueChartTracePatched ω₀ f Φ br) (cs i)
        = ∑ j, formFnResidue ω₀ g ((D (cs i)).xs j)) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · -- (A): the patched trace germ-equals the full-fibre trace (meromorphic) off `cs i`.
    have hgerm : valueChartTracePatched ω₀ f Φ br
        =ᶠ[𝓝[≠] (cs i)] (fibreTrace ω₀ f (Cfull i).D).traceCoeff :=
      (valueChartTracePatched_eventuallyEq ω₀ f Φ br (cs i)).trans (Cfull i).coherent_punctured
    exact (meromorphicAt_traceCoeff_fibreTrace ω₀ f (Cfull i).D).congr hgerm.symm
  · -- (B): the full-fibre coherence residue identity.
    exact hres_fin_of_fullFibreCoherence (poles := poles) D i (Cfull i) (hfull_inj i) (hxs_inj (cs i))
      (hpole_image i)
      (fun k hk => formFnResidue_eq_zero_of_analyticAt ω₀ g _ (hnonpole_an i k hk))

/-! ## Layer 2 — the ramified centre provider (Miranda §VIII.3 (3.1), via the proven atom)

At a *ramified* finite pole-value centre `c` the fibre `F⁻¹(coe c)` is a finite family of preimages
`pⱼ` of multiplicities `mⱼ` (`∑ mⱼ = deg`), and the regular-fibre route (`FibreRegularData`/`fibreTrace`,
which bake `deriv ≠ 0`) is structurally impossible.  But facts (A)/(B) still hold — they are exactly the
**ramified Lemma 3.2** (Miranda §VIII.3, formula (3.1)), proven as the algebraic `m`-sheet-sum atom
`Jacobians.RamifiedTrace`.  We build the parallel ramified structure here. -/

/-- **Per-fibre ramified data** for the cover `f` over a *ramified* base value `c : ℂ` (the ramified
analogue of `FibreRegularData`).  A finite family of preimages `xs : ι → X` over `coe c`, each carrying
a **ramification multiplicity** `mult i ≥ 1` (`= 1` at an unramified point), with the chart-pullback of
`g` meromorphic at each (so the chart integrand of `α = ω₀·g` has an isolated singularity there).  Unlike
`FibreRegularData` there is **no `deriv ≠ 0` field** — the preimages may be ramification points
(`deriv = 0`), exactly the case `FibreRegularData` cannot express.  The total multiplicity equals the
fibre degree; the per-preimage normal form `f = w^{mult i}` (Forster §5) is the geometric content the
trace identification rests on. -/
structure FibreRamifiedData (g : X → ℂ) (f : MeromorphicFunction X) (c : ℂ) where
  /-- The preimage index. -/
  ι : Type
  /-- Finiteness of the index. -/
  fintype_ι : Fintype ι
  /-- The preimages over `coe c`. -/
  xs : ι → X
  /-- Each preimage maps to `coe c` on the sphere. -/
  hmem : ∀ i, f.toRiemannSphere (xs i) = ((c : ℂ) : RiemannSphere)
  /-- The ramification multiplicity of each preimage (`≥ 1`; `= 1` unramified). -/
  mult : ι → ℕ
  /-- Multiplicities are positive. -/
  hmult_pos : ∀ i, 0 < mult i
  /-- `g`'s chart-pullback is meromorphic at each preimage (so the chart integrand of `α = ω₀·g` has an
  isolated singularity there). -/
  hg_mero : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (xs i)).symm z)) ((chartAt ℂ (xs i)) (xs i))

attribute [instance] FibreRamifiedData.fintype_ι

/-- **The bundled facts (A)/(B) at one finite pole-value centre `c`.**  Exactly the two facts
`globalTraceData_of_genus0_germ_facts` consumes per centre, abstracted as a single structure so a
ramified centre can supply them through the ramified atom (and an unramified centre through `Cfull` —
`facts_of_Cfull`).  The carried trace germ `T` is the §VIII.3 trace of `α` read in the value chart at
`c` (algebraically: the `m`-sheet-sum trace of the per-preimage chart integrands); `hcoh` is the
geometric identification of `valueChartTrace` with it (the genuine §VIII.3 content), and `hmero`/`hres`
are the atom's outputs. -/
structure RamifiedCenterFacts (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (Φ : (b : ℂ) → FibreRegularData g f b) (poles : Finset X) (c : ℂ) where
  /-- The ramified fibre over `c` (the preimages with multiplicities). -/
  D : FibreRamifiedData g f c
  /-- `D.xs` is injective (each preimage once). -/
  hD_inj : Function.Injective D.xs
  /-- `D.xs` enumerates exactly the poles of `α` in the fibre `F⁻¹(coe c)`. -/
  hD_mem : ∀ i, D.xs i ∈ poles
  hD_surj : ∀ a ∈ poles, f.toRiemannSphere a = ((c : ℂ) : RiemannSphere) → ∃ i, D.xs i = a
  /-- The value-chart trace germ at `c` (the algebraic `m`-sheet-sum trace). -/
  T : ℂ → ℂ
  /-- **The geometric-trace ramified identification** (the genuine §VIII.3 content, Forster §5 normal
  form `f = wᵐ`): the geometric trace germ equals `T` on a punctured neighbourhood of `c`. -/
  hcoh : valueChartTrace ω₀ f Φ =ᶠ[𝓝[≠] c] T
  /-- **(A)** `T` is meromorphic at `c` (the ramified Fact A — atom `meromorphicAt_laurentTraceCoeff`). -/
  hmero : MeromorphicAt T c
  /-- **(B)** the residue of `T` at `c` is the pole-fibre residue sum (the ramified Lemma 3.2 — atom
  `resAt_laurentTraceCoeff`, summed over the mixed-multiplicity preimages). -/
  hres : resAt T c = ∑ i, formFnResidue ω₀ g (D.xs i)

namespace RamifiedCenterFacts

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}
  {Φ : (b : ℂ) → FibreRegularData g f b} {poles : Finset X} {c : ℂ}

/-- **Fact (A) from a `RamifiedCenterFacts`.**  The patched trace is meromorphic at `c`: it germ-equals
`valueChartTrace` (patch inert off `c`), which germ-equals `T` (the geometric identification `hcoh`),
which is meromorphic (the atom's Fact A). -/
theorem meromorphicAt_patched (R : RamifiedCenterFacts ω₀ g f Φ poles c) (br : Finset ℂ) :
    MeromorphicAt (valueChartTracePatched ω₀ f Φ br) c := by
  have hgerm : valueChartTracePatched ω₀ f Φ br =ᶠ[𝓝[≠] c] R.T :=
    (valueChartTracePatched_eventuallyEq ω₀ f Φ br c).trans R.hcoh
  exact R.hmero.congr hgerm.symm

/-- **Fact (B) from a `RamifiedCenterFacts`.**  The residue of the patched trace at `c` equals the
pole-fibre residue sum: take residues across the same germ-equality (`resAt_congr`), then `R.hres`
(the ramified Lemma 3.2). -/
theorem resAt_patched (R : RamifiedCenterFacts ω₀ g f Φ poles c) (br : Finset ℂ) :
    resAt (valueChartTracePatched ω₀ f Φ br) c = ∑ i, formFnResidue ω₀ g (R.D.xs i) := by
  have hgerm : valueChartTracePatched ω₀ f Φ br =ᶠ[𝓝[≠] c] R.T :=
    (valueChartTracePatched_eventuallyEq ω₀ f Φ br c).trans R.hcoh
  rw [resAt_congr hgerm, R.hres]

end RamifiedCenterFacts

end Jacobians.Dolbeault.SerreResidueTheorem
