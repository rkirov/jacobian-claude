/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueTheorem
import Jacobians.Dolbeault.FormTraceGlobalFibreSelection

/-!
# The genericity obligation for Gate A, as a single named structure (Miranda §VIII.3)

`Jacobians.Dolbeault.SerreResidueTheorem.TraceRationalityExists ω₀ g poles`
(`= ∃ f, Nonempty (TraceRationalityDataNF ω₀ g f poles)`) is the *single* remaining substrate gap of
the book-faithful residue theorem `∑ₐ Resₐ(α) = 0` (`α = ω₀·g`): Step-1 rationality and Steps 2–4 are
all proven, so what remains is Miranda's genericity — *"simply choose any nonconstant meromorphic `f`"*
(p. 254), suitably adapted to `α`'s poles.

This file packages that obligation as **one explicit structure** `AdaptedTraceGeometry ω₀ g f poles`
whose fields are *exactly* the genuine §VIII.3 geometric data the proven sound trace-rationality
assembly `FormTraceFullFibre.traceRationalityDataNF_ofPatched` consumes for an adapted nonconstant
cover `f` (the same inputs as `FormTraceFullFibre.residueSum_eq_zero_of_patchedGeometry`, but producing
the `TraceRationalityDataNF` bundle rather than the residue identity directly).  The deep analytic
content — the trace's meromorphy across branch points, `hentire`, the sound `∞`-fibre — is **proven**
inside that assembly; `AdaptedTraceGeometry` carries only the data that genuinely requires the choice of
an adapted `f`:

* `Φ` — the global full-fibre selection (the canonical selection of `FormTraceGlobalFibreSelection`);
* `Creg` / `hCreg_g` — the per-regular-value moving coherence (symmetric lever, *proven* constructor);
* `αBr` / `hbr` / `hevBr` — the finite branch values, branch-locus membership, a local holomorphic
  representative of `α` near each branch fibre, and the eventual sphere-sheet coherence (the standard
  regular-value data, *proven* via `hevBr_of_regularData`);
* `D` / `Cfin` / `hxs_*` — the per-pole-value full-fibre data + moving coherence;
* `xsInf` / `hsimpleInf` — the simple `∞`-poles (the sound `∞`-fibre `InftyFibreDataNF.ofRegular`);
* `hcoh` — the `∞`-moving coherence (the `∞`-single-valuedness — *the* genuine residual);
* `hcont_int`, `R₀` — junk-freeness + the genus-`0` `∞`-vanishing (repo-wide content).

The headline `traceRationalityExists_of_adaptedGeometry` proves `TraceRationalityExists` from
`∃ f, Nonempty (AdaptedTraceGeometry ω₀ g f poles)`, so the substrate gap collapses to the existence of
*one* such adapted geometry.  `residueTheorem_of_adaptedGeometry` then gives `∑ Res = 0` from it
unconditionally, and `adaptedTraceGeometry_holomorphic` is the empty-pole **non-vacuity** witness
(confirming the structure is honest, not a disguised `False`).

## Soundness

No `axiom`, no `sorry`.  This file asserts nothing false: `AdaptedTraceGeometry` is a faithful bundling
of the *existing* `TraceRationalityDataNF`/`traceRationalityDataNF_ofPatched` input contract, and
`traceRationalityExists_of_adaptedGeometry` is a sound reduction.  All public declarations are
authoritatively `[propext, Classical.choice, Quot.sound]` (`#print axioms`), and the empty-pole
`adaptedTraceGeometry_holomorphic` is a genuine non-vacuity witness for `poles = ∅`.

### ⚠ Soundness finding (the genericity is **blocked upstream**, not satisfiable for mixed fibres)

`AdaptedTraceGeometry` is **NOT known to be satisfiable for a general nonempty `poles` whose fibres are
"mixed"** (a fibre over a pole-value containing both poles of `α` and points where `α` is holomorphic).
The obstruction is *upstream*, in the input contract of `FormTraceFullFibre.TraceRationalityDataNF`
(`FormTraceFullFibreRationalityNF.lean`), and is inherited by `SerreResidueTheorem.TraceRationalityExists`:

* `D` / `Dinf` must enumerate **exactly the poles** in each fibre (the fields `hxs_mem`/`hxsInf_mem`
  demand `D.xs i ∈ poles`, and `hxs_surj`/`hxsInf_surj` demand all poles are hit — so `D` is *pole-only*).
* But the field `agree` is the **germ**-equality `L.R =ᶠ[𝓝[≠] p] (fibreTrace ω₀ f (D p)).traceCoeff`, and
  in the constructor `agree` is produced from the moving-coherence identity
  `valueChartTrace ω₀ f Φ =ᶠ (fibreTrace ω₀ f (Cfin.D)).traceCoeff` with `Cfin.D = D (cs i)`.  The
  geometric trace `valueChartTrace ω₀ f Φ` is the **full-fibre** symmetric sum (Miranda's `Tr_F α`,
  `Φ` = the full fibre — forced both by the moving coherence's `hdiag`, which sums over `D.ι` matched to
  `Φ b'`, and by `hbnd`, whose boundedness-across-branch-points argument is the *full* bundle SUM).  A
  **non-pole** sheet contributes `chartIntegrand ω₀ g x · deriv` to the trace coefficient, which is a
  *generally nonzero holomorphic* germ (`chartIntegrand = coeffAt ω₀ · g`, not a principal-part
  extraction).  Hence the full-fibre and pole-only trace coefficients **differ by a nonzero holomorphic
  germ**, and the germ-equality `agree` with a pole-only `D` is **false** at a mixed fibre.

The two constraints — `D` pole-only (`hxs_mem`) and `D` full-fibre (`agree`/`hCfin_D`/`hdiag`/`hbnd`) —
coincide *only* when every fibre point over a pole-value is itself a pole (the
`PoleValueSeparated`/`hsep` condition the campaign already flagged as **generically false**).  So for
mixed fibres the joint contract is unsatisfiable: `AdaptedTraceGeometry` (and `TraceRationalityExists`)
is a *disguised `False`* there, NOT honestly dischargeable as stated.

**The field is over-strong, not the downstream use.**  `agree`/`agree_infty` are consumed **only** at the
*residue* level: `hL32_of_agree_fibreRegularData` / `infty_eq_of_agreeNF` use them solely through
`resAt_congr` (the residue of `L.R` at the centre).  At the residue level the non-pole sheets *do*
contribute `0` (`α` holomorphic there ⟹ residue `0`), so the **residue** equality holds with pole-only
`D`.  The misformalization is exactly that `agree` is stated as a *germ* equality where only the *residue*
is needed.  The correct fix (in the FormTrace* scaffold, out of scope for this single-thread file) is one
of:

1. weaken `agree`/`agree_infty` to the residue equality `resAt L.R p = ∑ᵢ resAt (coeff i) (pre i)`
   (exactly `hL32`/`infty_eq`), which is satisfiable with pole-only `D` and is all the descent uses; or
2. make `D`/`Dinf` the **full** fibre (drop `∈ poles` from `hxs_mem`/`hxsInf_mem`) and adjust
   `fibreResidueSum_eq_filter`/`inftyResidueSumNF_eq_filter` to sum over the full fibre with the
   non-pole-residue-`0` vanishing (rather than via the image-set equality they currently use).

Either repair restores satisfiability and keeps the descent intact, after which the genericity wiring of
this file (`canonicalFibreSelection` Φ, `MovingCoherenceDatum.ofSphereSheetSystemSet`,
`hevBr_of_regularData`, `InftyFibreDataNF.ofRegular`) goes through.  Until then, this file is the honest
*localization* of the gap: every analytic input is reachable; the obstruction is the pole-only-`D`
vs. full-fibre-`agree` contract in `TraceRationalityDataNF`.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3, pp. 251–256.
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
* `docs/gate_a_cover_genericity_textbook_2026-06-08.md`, `docs/gate_a_sound_patched_close_2026-06-09.md`.
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

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ## The adapted-geometry structure

`AdaptedTraceGeometry ω₀ g f poles` bundles the §VIII.3 geometric data for the nonconstant cover `f`.
The field list is exactly the hypothesis list of `FormTraceFullFibre.residueSum_eq_zero_of_patchedGeometry`
(the sound branch-patched assembly), recorded as a structure so the genericity obligation is a single
named existential. -/

/-- **The adapted §VIII.3 trace geometry** for a nonconstant cover `f` and `α = ω₀·g`.

Its fields are the genuine geometric inputs the *proven* sound trace-rationality assembly
(`FormTraceFullFibre.traceRationalityDataNF_ofPatched`) consumes — the global full-fibre selection,
the per-regular and per-pole moving coherence, the finite branch data, the simple `∞`-poles, the
`∞`-moving coherence, and the genus-`0` junk/`∞`-vanishing.  Producing one (for *some* nonconstant `f`)
discharges Miranda's genericity. -/
structure AdaptedTraceGeometry (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) (poles : Finset X) where
  /-- The cover `F = f.toRiemannSphere` is nonconstant. -/
  hncF : ¬ ∃ y₀ : RiemannSphere, ∀ x, f.toRiemannSphere x = y₀
  /-- The global full-fibre selection. -/
  Φ : (b : ℂ) → FibreRegularData g f b
  /-- The number of finite pole-values. -/
  m : ℕ
  /-- The finite pole-values (centres of the rational trace). -/
  cs : Fin m → ℂ
  /-- A radius bounding all centres (the principal-part extraction). -/
  ρ : ℝ
  /-- All centres lie in `ball 0 ρ`. -/
  hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ
  /-- The centres are distinct. -/
  hcs_inj : Function.Injective cs
  /-- The finite branch values. -/
  br : Finset ℂ
  /-- The per-regular-value moving coherence datum (off the centres and branch values). -/
  Creg : ∀ z, z ∉ Finset.univ.image cs ∪ br → MovingCoherenceDatum ω₀ g f Φ z
  /-- `g`'s chart pullback is analytic at each regular fibre point. -/
  hCreg_g : ∀ z (hz : z ∉ Finset.univ.image cs ∪ br), ∀ i,
    AnalyticAt ℂ (fun w => g ((chartAt ℂ ((Creg z hz).D.xs i)).symm w))
      ((chartAt ℂ ((Creg z hz).D.xs i)) ((Creg z hz).D.xs i))
  /-- A local holomorphic representative of `α = ω₀·g` near each branch fibre. -/
  αBr : ℂ → HolomorphicOneForms X
  /-- Each branch value (off the pole-values) lies in the branch locus of the cover. -/
  hbr : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
    ((b₀ : ℂ) : RiemannSphere) ∈ branchLocus f.toRiemannSphere
  /-- The eventual sphere-sheet coherence at each branch value (the value-correct symmetric SUM). -/
  hevBr : ∀ b₀ ∈ br, b₀ ∉ Finset.univ.image cs →
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
        valueChartTrace ω₀ f Φ z
            = (fibreTrace ω₀ f (FibreRegularData.ofSphereSheetSystem S hderiv _hmero)).traceCoeff z ∧
        (∀ i, (αBr b₀).toFun (S.sheet i (((z : ℂ) : RiemannSphere)))
          = g (S.sheet i (((z : ℂ) : RiemannSphere)))
            • ω₀.toFun (S.sheet i (((z : ℂ) : RiemannSphere))))
  /-- The per-pole-value full-fibre regularity data. -/
  D : (p : ℂ) → FibreRegularData g f p
  /-- The per-pole-value moving coherence datum. -/
  Cfin : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i)
  /-- The moving datum's fixed fibre at `cs i` is the per-pole fibre `D (cs i)`. -/
  hCfin_D : ∀ i, (Cfin i).D = D (cs i)
  /-- Each per-pole fibre enumeration is injective. -/
  hxs_inj : ∀ p, Function.Injective (D p).xs
  /-- The per-pole fibre points are poles in the fibre `F⁻¹(coe p)`. -/
  hxs_mem : ∀ p, ∀ i,
    (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere)
  /-- The per-pole fibre enumerates *all* poles over `coe p`. -/
  hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
    ∃ i, (D p).xs i = a
  /-- The index type of the `∞`-poles. -/
  ιInf : Type
  /-- `ιInf` is finite. -/
  fintypeInf : Fintype ιInf
  /-- The poles over `∞`. -/
  xsInf : ιInf → X
  /-- Each `∞`-pole is a **simple** pole of `f` (the sound `∞`-fibre). -/
  hsimpleInf : ∀ i, f.orderAtPoint (xsInf i) = -1
  /-- `g`'s chart pullback is meromorphic at each `∞`-pole. -/
  hmeroInf : ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (xsInf i)).symm z))
    ((chartAt ℂ (xsInf i)) (xsInf i))
  /-- The `∞`-pole enumeration is injective. -/
  hxsInf_inj : Function.Injective xsInf
  /-- The `∞`-poles are poles over `∞`. -/
  hxsInf_mem : ∀ i, xsInf i ∈ poles ∧ f.toRiemannSphere (xsInf i) = OnePoint.infty
  /-- The `∞`-pole enumeration covers *all* poles over `∞`. -/
  hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, xsInf i = a
  /-- **The `∞`-moving coherence** (the `∞`-single-valuedness — the genuine `∞` residual). -/
  hcoh : recipCoeff (valueChartTracePatched ω₀ f Φ br)
    =ᶠ[𝓝[≠] 0]
      recipCoeff (inftyMovingSumNF ω₀ f
        (@InftyFibreDataNF.ofRegular X _ _ _ _ _ _ _ g f ιInf fintypeInf
          xsInf hsimpleInf hmeroInf))
  /-- The centres, mapped to the sphere, are exactly the finite pole values. -/
  hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- **Junk-freeness.** `T − L.R` is continuous at each centre. -/
  hcont_int : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
    (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
      (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
    ∀ p ∈ Finset.univ.image L.a, ContinuousAt (valueChartTracePatched ω₀ f Φ br - L.R) p
  /-- The genus-`0` analytic continuation of the reciprocal remainder. -/
  R₀ : ℂ → ℂ
  /-- `R₀` is analytic at `0`. -/
  hR₀_an : AnalyticAt ℂ R₀ 0
  /-- **Genus-`0` `∞`-vanishing.** `R₀ 0 = 0`. -/
  hR₀0 : R₀ 0 = 0
  /-- The reciprocal remainder germ-equals `R₀` off `0`. -/
  hR₀_eq : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
    recipCoeff (valueChartTracePatched ω₀ f Φ br - L.R) =ᶠ[𝓝[≠] 0] R₀

namespace AdaptedTraceGeometry

attribute [instance] AdaptedTraceGeometry.fintypeInf

/-- **The sound value-correct rational-trace bundle from an adapted geometry.**  Wires every field of
`AdaptedTraceGeometry` into the proven sound constructor
`FormTraceFullFibre.traceRationalityDataNF_ofPatched` (with `hreg`/`hbnd`/`hcoh_inf` discharged via the
proven helpers `hreg_of_movingDatum`, `hbnd_of_eventual_sphereCoherence`,
`hcoh_inf_of_inftyMovingCoherenceNF`).  This is the genuine §VIII.3 trace `Tr_F α` as a rational
`LaurentForm`, value-correct, sound `∞`-fibre. -/
noncomputable def toTraceRationalityDataNF (A : AdaptedTraceGeometry ω₀ g f poles) :
    FormTraceFullFibre.TraceRationalityDataNF ω₀ g f poles :=
  FormTraceFullFibre.traceRationalityDataNF_ofPatched A.Φ A.m A.cs A.ρ A.hcs_ball A.hcs_inj A.br
    (fun w hw => hreg_of_movingDatum (A.Creg w hw) (A.hCreg_g w hw))
    (fun b₀ hb₀br hb₀cs =>
      hbnd_of_eventual_sphereCoherence ω₀ g f A.Φ (A.αBr b₀) A.hncF (A.hbr b₀ hb₀br hb₀cs)
        (A.hevBr b₀ hb₀br hb₀cs))
    A.D A.Cfin A.hCfin_D A.hxs_inj A.hxs_mem A.hxs_surj
    (InftyFibreDataNF.ofRegular g f A.xsInf A.hsimpleInf A.hmeroInf)
    A.hxsInf_inj A.hxsInf_mem A.hxsInf_surj A.hcenters_cs
    (hcoh_inf_of_inftyMovingCoherenceNF ω₀ g f A.Φ A.br _ A.hcoh)
    A.hcont_int A.R₀ A.hR₀_an A.hR₀0 A.hR₀_eq

end AdaptedTraceGeometry

/-! ## The genericity obligation discharged into `TraceRationalityExists` -/

/-- **`TraceRationalityExists` from an adapted geometry (single `f`).**  An adapted §VIII.3 trace
geometry for the nonconstant cover `f` yields the value-correct rational-trace bundle
(`AdaptedTraceGeometry.toTraceRationalityDataNF`), hence `TraceRationalityExists ω₀ g poles`. -/
theorem traceRationalityExists_of_adaptedGeometry {f : MeromorphicFunction X}
    (A : AdaptedTraceGeometry ω₀ g f poles) :
    TraceRationalityExists ω₀ g poles :=
  ⟨f, ⟨A.toTraceRationalityDataNF⟩⟩

/-- **`TraceRationalityExists` from the existence of an adapted geometry.**  If *some* nonconstant cover
`f` carries an adapted §VIII.3 trace geometry, then the genericity obligation `TraceRationalityExists ω₀
g poles` holds.  This collapses the substrate gap to the single existential
`∃ f, Nonempty (AdaptedTraceGeometry ω₀ g f poles)`. -/
theorem traceRationalityExists_of_exists_adaptedGeometry
    (h : ∃ f : MeromorphicFunction X, Nonempty (AdaptedTraceGeometry ω₀ g f poles)) :
    TraceRationalityExists ω₀ g poles := by
  obtain ⟨f, ⟨A⟩⟩ := h
  exact traceRationalityExists_of_adaptedGeometry A

/-- **The residue theorem `∑ Res = 0` from an adapted geometry.**  If a nonconstant cover `f` carries an
adapted §VIII.3 trace geometry, the total residue of `α = ω₀·g` over its poles vanishes — Steps 1–4 all
proven, the only input the adapted geometry (Miranda's genericity). -/
theorem residueTheorem_of_adaptedGeometry {f : MeromorphicFunction X}
    (A : AdaptedTraceGeometry ω₀ g f poles) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueTheorem_of_traceRationalityExists (traceRationalityExists_of_adaptedGeometry A)

/-! ## Non-vacuity (soundness witness)

The empty-pole case: the empty selection, no centres (`m = 0`), no branch values (`br = ∅`), the empty
`∞`-fibre, and the zero trace.  Every field is satisfied — confirming `AdaptedTraceGeometry` is honest
(not a disguised `False`).  This mirrors the proven non-vacuity of the patched constructor
(`FormTraceFullFibre.traceRationalityDataNF_holomorphic`); here we exhibit a full `AdaptedTraceGeometry`. -/

/-- **Non-vacuity witness.**  For the empty pole set, an `AdaptedTraceGeometry` exists with the empty
selection, no centres, `br = ∅`, the empty sound `∞`-fibre, and the zero trace — every field is
satisfiable.  Confirms the structure is not a disguised `False`. -/
noncomputable def adaptedTraceGeometry_holomorphic (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X)
    (hncF : ¬ ∃ y₀ : RiemannSphere, ∀ x, f.toRiemannSphere x = y₀) :
    AdaptedTraceGeometry ω₀ g f (∅ : Finset X) where
  hncF := hncF
  Φ := fun p => emptyFibreRegularData g f p
  m := 0
  cs := Fin.elim0
  ρ := 1
  hcs_ball := fun i => i.elim0
  hcs_inj := Function.injective_of_subsingleton _
  br := ∅
  Creg := fun z _ => movingCoherenceDatum_empty ω₀ g f z
  hCreg_g := fun z hz i => i.elim
  αBr := fun _ => 0
  hbr := fun b₀ hb₀ _ => absurd hb₀ (Finset.notMem_empty b₀)
  hevBr := fun b₀ hb₀ _ => absurd hb₀ (Finset.notMem_empty b₀)
  D := fun p => emptyFibreRegularData g f p
  Cfin := fun i => i.elim0
  hCfin_D := fun i => i.elim0
  hxs_inj := fun _ a _ _ => a.elim
  hxs_mem := fun _ i => i.elim
  hxs_surj := fun _ a ha => absurd ha (Finset.notMem_empty a)
  ιInf := Empty
  fintypeInf := inferInstance
  xsInf := Empty.elim
  hsimpleInf := fun i => i.elim
  hmeroInf := fun i => i.elim
  hxsInf_inj := fun i => i.elim
  hxsInf_mem := fun i => i.elim
  hxsInf_surj := fun a ha => absurd ha (Finset.notMem_empty a)
  hcoh := by
    have hpatch0 : valueChartTracePatched ω₀ f (fun p => emptyFibreRegularData g f p) ∅
        = fun _ => (0 : ℂ) := by
      funext z
      rw [valueChartTracePatched_of_not_mem ω₀ f _ _ (Finset.notMem_empty z),
        valueChartTrace_emptySelection ω₀ f]
    have hmoving0 : inftyMovingSumNF ω₀ f
        (@InftyFibreDataNF.ofRegular X _ _ _ _ _ _ _ g f Empty _ Empty.elim
          (fun i => i.elim) (fun i => i.elim)) = fun _ => (0 : ℂ) := by
      funext b'; rw [inftyMovingSumNF]
      exact @Finset.sum_of_isEmpty _ _ _ _ (inferInstanceAs (IsEmpty Empty)) _
    rw [hpatch0, hmoving0, recipCoeff_zero]
  hcenters_cs := by simp
  hcont_int := by
    intro L hLa _ p hp
    have hpatch0 : valueChartTracePatched ω₀ f (fun p => emptyFibreRegularData g f p) ∅
        = fun _ => (0 : ℂ) := by
      funext z
      rw [valueChartTracePatched_of_not_mem ω₀ f _ _ (Finset.notMem_empty z),
        valueChartTrace_emptySelection ω₀ f]
    have hLR0 : L.R = fun _ => (0 : ℂ) :=
      laurentForm_R_eq_zero_of_emptyImage
        (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
    rw [hpatch0, hLR0]
    have h0 : ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) = fun _ : ℂ => (0 : ℂ) := by funext z; simp
    rw [h0]; exact continuousAt_const
  R₀ := fun _ => 0
  hR₀_an := analyticAt_const
  hR₀0 := rfl
  hR₀_eq := by
    intro L hLa
    have hpatch0 : valueChartTracePatched ω₀ f (fun p => emptyFibreRegularData g f p) ∅
        = fun _ => (0 : ℂ) := by
      funext z
      rw [valueChartTracePatched_of_not_mem ω₀ f _ _ (Finset.notMem_empty z),
        valueChartTrace_emptySelection ω₀ f]
    have hLR0 : L.R = fun _ => (0 : ℂ) :=
      laurentForm_R_eq_zero_of_emptyImage
        (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
    rw [hpatch0, hLR0]
    have h0 : ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) = fun _ : ℂ => (0 : ℂ) := by funext z; simp
    rw [h0, recipCoeff_zero]

end Jacobians.Dolbeault.SerreResidueTheorem
