/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceFullFibreRationalityNF
import Jacobians.Dolbeault.FormTraceCoherenceFromMoving

/-!
# Gate A `∑Res = 0` from the moving-fibre engine, *sound* `∞` fibre (Miranda §VIII.3)

`Jacobians.Dolbeault.FormTraceFullFibre.traceCoherenceData_ofMovingData`
(`FormTraceCoherenceFromMoving`) reduces Gate A to a global selection `Φ` (giving the geometric trace
`T := valueChartTrace ω₀ f Φ`), per-pole moving data discharging the finite coherence, the off-centre
meromorphy, the genus-`0` remainder vanishing, and the `∞`-coherence `hcoh_inf` — *but its `hcoh_inf` is
phrased against the buggy `inftyFibreTrace`* (the `∞`-fibre datum `InftyFibreData` is unsatisfiable for
real `∞`-poles; see `FormTraceInftyFibreNF`).

This file is the **sound** analogue.  It assembles a `TraceRationalityDataNF` (the sound full-fibre
reduction target) directly from:

* the **finite trace rationality** — the geometric trace `T := valueChartTrace ω₀ f Φ` is meromorphic at
  each finite pole-value (`MovingCoherenceDatum`), and after subtracting its finite principal parts the
  remainder is entire + holomorphic across `∞` (genus-`0`), so `T = L.R` (the Liouville agreement,
  `coeff_eq_of_entire_diff_of_recipCoeff_continuousAt`), giving the finite `agree`;
* the **sound `∞`-coherence** `hcoh_inf` — `recipCoeff T =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f Dinf).traceCoeff`
  against the **repaired** `∞`-fibre trace, giving `agree_infty`.

The finite pole-centre coherence and off-centre meromorphy are discharged from the proved moving-fibre
engine (`hcoh_fin_of_movingDatum` / `meromorphicAt_valueChartTrace_of_movingDatum`, reused verbatim).

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `traceRationalityDataNF_ofMovingData` — a `TraceRationalityDataNF` from a global selection `Φ`,
  per-pole moving data, the genus-`0`/`∞`/enumeration inputs (sound `∞`-fibre);
* `residueSum_eq_zero_of_movingTraceRationalityNF` — Gate A `∑Res = 0` from it;
* `traceRationalityDataNF_ofMovingData_holomorphic` — end-to-end non-vacuity (empty-pole).

## The single minimal remaining obligation (precise diagnosis)

After this file, the *sound* `TraceRationalityDataNF` route to Gate A rests — axiom-clean — on exactly:

1. a global fibre selection `Φ` + per-pole `MovingCoherenceDatum`s (wall 2, dischargeable from the
   canonical full-fibre selection, `FormTraceGlobalFibreSelection`);
2. the **genus-`0` remainder vanishing** (`hentire`/`hrecip_cont`: `T − L.R` entire + holomorphic across
   `∞`; the `H⁰(ℂℙ¹, Ω) = 0` content) and the **sound `∞`-coherence** `hcoh_inf`;
3. the discrete fibre enumeration (finite + the sound `∞`-fibre `Dinf : InftyFibreDataNF`, the latter
   from `InftyFibreDataNF.ofRegular` at simple `∞`-poles);
4. an **adapted cover** `f` (Gate-A wall 1, genericity).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3.
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceFullFibre

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormResidueTheorem
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTraceInftyFibre
  Jacobians.Dolbeault.FormTraceInftyRecip Jacobians.Dolbeault.FormTraceLiouville
  Jacobians.Dolbeault.FormTraceMovingFibre

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}

/-! ### The Liouville agreement `T = L.R`, reused

The finite principal-part extraction + the genus-`0` remainder vanishing give `T = L.R` everywhere; this
is independent of the `∞`-fibre datum (it depends only on the finite centres, `hT_mero`, `hentire`,
`hrecip_cont`).  We re-derive it here directly from the proved engine. -/

/-- **A `TraceRationalityDataNF` from a global selection and per-pole moving data (sound `∞`).**  With
`T := valueChartTrace ω₀ f Φ`: the finite principal-part `LaurentForm L` (`exists_laurentForm_principalPart`)
+ the genus-`0` remainder vanishing (`hentire`/`hrecip_cont`) give the Liouville agreement `T = L.R`
(`coeff_eq_of_entire_diff_of_recipCoeff_continuousAt`).  Then:

* `agree p` — `L.R = T =ᶠ (fibreTrace ω₀ f (D p)).traceCoeff` (Liouville + the moving-datum coherence
  `hcoh_fin_of_movingDatum`);
* `agree_infty` — `recipCoeff L.R = recipCoeff T =ᶠ (inftyFibreTraceNF ω₀ f Dinf).traceCoeff` (Liouville +
  the **sound** `∞`-coherence `hcoh_inf`).

The pole-centre coherence and the off-centre meromorphy are the proved moving-fibre facts.  Constructing
one ⇒ Gate A `∑Res = 0` (sound `∞`-fibre). -/
noncomputable def traceRationalityDataNF_ofMovingData
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (D : (p : ℂ) → FibreRegularData g f p)
    (Cfin : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (hCfin_D : ∀ i, (Cfin i).D = D (cs i))
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (D p).xs i = a)
    (Dinf : InftyFibreDataNF g f) (hxsInf_inj : Function.Injective Dinf.xs)
    (hxsInf_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hcoh_inf : recipCoeff (valueChartTrace ω₀ f Φ)
      =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f Dinf).traceCoeff)
    (hentire : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      AnalyticOnNhd ℂ (valueChartTrace ω₀ f Φ - L.R) Set.univ)
    (hrecip_cont : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ContinuousAt (recipCoeff (valueChartTrace ω₀ f Φ - L.R)) 0) :
    TraceRationalityDataNF ω₀ g f poles := by
  classical
  -- The geometric trace and its meromorphy at the centres (from the moving data).
  set T := valueChartTrace ω₀ f Φ with hT
  have hT_mero : ∀ i, MeromorphicAt T (cs i) := fun i =>
    meromorphicAt_valueChartTrace_of_movingDatum (Cfin i) (hCfin_D i)
  -- Finite principal-part `LaurentForm` (via `Classical.choose`, as we are producing data).
  set hPP := exists_laurentForm_principalPart cs ρ hcs_ball hcs_inj hT_mero with hPP_def
  set L := hPP.choose with hL_def
  have hLcenters : Finset.univ.image L.a = Finset.univ.image cs := hPP.choose_spec.1
  have hLrem : ∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧ (T - L.R) =ᶠ[𝓝[≠] (cs j)] R :=
    hPP.choose_spec.2
  -- The Liouville agreement `T = L.R`.
  have hTL : T = L.R :=
    coeff_eq_of_entire_diff_of_recipCoeff_continuousAt
      (hentire L hLcenters hLrem) (hrecip_cont L hLcenters hLrem)
  refine
    { L := L
      D := D
      hxs_inj := hxs_inj
      hxs_mem := hxs_mem
      hxs_surj := hxs_surj
      Dinf := Dinf
      hxsInf_inj := hxsInf_inj
      hxsInf_mem := hxsInf_mem
      hxsInf_surj := hxsInf_surj
      hcenters := by rw [hLcenters]; exact hcenters_cs
      agree := ?_
      agree_infty := ?_ }
  · -- finite agreement: `L.R = T`, and `T =ᶠ[𝓝 (cs i)] (fibreTrace …).traceCoeff` (moving coherence).
    intro p hp
    rw [hLcenters] at hp
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hp
    obtain ⟨i, rfl⟩ := hp
    rw [← hTL]
    exact (hcoh_fin_of_movingDatum (Cfin i) (hCfin_D i)).filter_mono nhdsWithin_le_nhds
  · -- `∞` agreement: `recipCoeff L.R = recipCoeff T`, and the sound `∞`-coherence.
    rw [← hTL]
    exact hcoh_inf

/-- **Gate A `∑Res = 0` from a global selection + per-pole moving data (sound `∞`).**  The sound
`TraceRationalityDataNF` route closed via `residueSum_eq_zero_of_traceRationalityDataNF`. -/
theorem residueSum_eq_zero_of_movingTraceRationalityNF
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (D : (p : ℂ) → FibreRegularData g f p)
    (Cfin : ∀ i, MovingCoherenceDatum ω₀ g f Φ (cs i))
    (hCfin_D : ∀ i, (Cfin i).D = D (cs i))
    (hxs_inj : ∀ p, Function.Injective (D p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (D p).xs i = a)
    (Dinf : InftyFibreDataNF g f) (hxsInf_inj : Function.Injective Dinf.xs)
    (hxsInf_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hcoh_inf : recipCoeff (valueChartTrace ω₀ f Φ)
      =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f Dinf).traceCoeff)
    (hentire : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      AnalyticOnNhd ℂ (valueChartTrace ω₀ f Φ - L.R) Set.univ)
    (hrecip_cont : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ContinuousAt (recipCoeff (valueChartTrace ω₀ f Φ - L.R)) 0) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_traceRationalityDataNF ω₀ g f poles
    (traceRationalityDataNF_ofMovingData Φ m cs ρ hcs_ball hcs_inj D Cfin hCfin_D hxs_inj hxs_mem
      hxs_surj Dinf hxsInf_inj hxsInf_mem hxsInf_surj hcenters_cs hcoh_inf hentire hrecip_cont)

/-! ### The sheet-form constructor (the symmetric lever — no labeling)

Building the per-pole moving data `Cfin i` from continuously-varying smooth **sheet sections** + the
labeling-independent set-form re-selection `MovingCoherenceDatum.ofSheetSectionsSet`, exactly as in
`traceCoherenceData_ofSheetSections` — but targeting the *sound* `TraceRationalityDataNF`.  The fibre
selection `Φ` (enumerating the poles) doubles as the per-centre fibre data `D` (so the pole sub-fibre is
the full fibre — the full-fibre route, no separation `hsep`). -/

/-- **A `TraceRationalityDataNF` from sheet sections (sound `∞`, symmetric lever).**  The per-pole moving
data is built from continuously-varying smooth sheet sections `secFin` + the set-form re-selection
`hsetFin` (`MovingCoherenceDatum.ofSheetSectionsSet`), so the caller supplies only labeling-independent
geometric facts (the sheets enumerate the per-centre fibre as a set).  The pole-centre coherence is
discharged labeling-free; the genus-`0` (`hentire`/`hrecip_cont`) and the **sound `∞`-coherence**
`hcoh_inf` are the precise residual inputs. -/
noncomputable def traceRationalityDataNF_ofSheetSections
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (secFin : ∀ i, (Φ (cs i)).ι → ℂ → X)
    (hsecFin_base : ∀ i j, secFin i j (cs i) = (Φ (cs i)).xs j)
    (hsecFin_smooth : ∀ i j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (secFin i j) (cs i))
    (hsecFin_sec : ∀ i j, ∀ᶠ b' in 𝓝 (cs i), f.holoRepr (secFin i j b') = b')
    (hsetFin : ∀ i, ∀ᶠ b' in 𝓝 (cs i), Function.Injective (Φ b').xs ∧
      Function.Injective (fun j => secFin i j b') ∧
      Set.range (Φ b').xs = Set.range (fun j => secFin i j b') ∧
      (∀ j, secFin i j b' ∈ (chartAt ℂ ((Φ (cs i)).xs j)).source))
    (hxs_inj : ∀ p, Function.Injective (Φ p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (Φ p).xs i ∈ poles ∧ f.toRiemannSphere ((Φ p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (Φ p).xs i = a)
    (Dinf : InftyFibreDataNF g f) (hxsInf_inj : Function.Injective Dinf.xs)
    (hxsInf_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hcoh_inf : recipCoeff (valueChartTrace ω₀ f Φ)
      =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f Dinf).traceCoeff)
    (hentire : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      AnalyticOnNhd ℂ (valueChartTrace ω₀ f Φ - L.R) Set.univ)
    (hrecip_cont : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ContinuousAt (recipCoeff (valueChartTrace ω₀ f Φ - L.R)) 0) :
    TraceRationalityDataNF ω₀ g f poles :=
  traceRationalityDataNF_ofMovingData Φ m cs ρ hcs_ball hcs_inj Φ
    (fun i => MovingCoherenceDatum.ofSheetSectionsSet (Φ (cs i)) (secFin i)
      (hsecFin_base i) (hsecFin_smooth i) (hsecFin_sec i) (hsetFin i))
    (fun _ => rfl)
    hxs_inj hxs_mem hxs_surj Dinf hxsInf_inj hxsInf_mem hxsInf_surj hcenters_cs hcoh_inf
    hentire hrecip_cont

/-- **Gate A `∑Res = 0` from sheet sections (sound `∞`, symmetric lever).** -/
theorem residueSum_eq_zero_of_sheetTraceRationalityNF
    (Φ : (b : ℂ) → FibreRegularData g f b)
    (m : ℕ) (cs : Fin m → ℂ) (ρ : ℝ) (hcs_ball : ∀ i, cs i ∈ ball (0 : ℂ) ρ)
    (hcs_inj : Function.Injective cs)
    (secFin : ∀ i, (Φ (cs i)).ι → ℂ → X)
    (hsecFin_base : ∀ i j, secFin i j (cs i) = (Φ (cs i)).xs j)
    (hsecFin_smooth : ∀ i j, ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (secFin i j) (cs i))
    (hsecFin_sec : ∀ i j, ∀ᶠ b' in 𝓝 (cs i), f.holoRepr (secFin i j b') = b')
    (hsetFin : ∀ i, ∀ᶠ b' in 𝓝 (cs i), Function.Injective (Φ b').xs ∧
      Function.Injective (fun j => secFin i j b') ∧
      Set.range (Φ b').xs = Set.range (fun j => secFin i j b') ∧
      (∀ j, secFin i j b' ∈ (chartAt ℂ ((Φ (cs i)).xs j)).source))
    (hxs_inj : ∀ p, Function.Injective (Φ p).xs)
    (hxs_mem : ∀ p, ∀ i,
      (Φ p).xs i ∈ poles ∧ f.toRiemannSphere ((Φ p).xs i) = ((p : ℂ) : RiemannSphere))
    (hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) →
      ∃ i, (Φ p).xs i = a)
    (Dinf : InftyFibreDataNF g f) (hxsInf_inj : Function.Injective Dinf.xs)
    (hxsInf_mem : ∀ i, Dinf.xs i ∈ poles ∧ f.toRiemannSphere (Dinf.xs i) = OnePoint.infty)
    (hxsInf_surj : ∀ a ∈ poles, f.toRiemannSphere a = OnePoint.infty → ∃ i, Dinf.xs i = a)
    (hcenters_cs : (Finset.univ.image cs).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
      = (poles.image f.toRiemannSphere).erase OnePoint.infty)
    (hcoh_inf : recipCoeff (valueChartTrace ω₀ f Φ)
      =ᶠ[𝓝[≠] 0] (inftyFibreTraceNF ω₀ f Dinf).traceCoeff)
    (hentire : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      AnalyticOnNhd ℂ (valueChartTrace ω₀ f Φ - L.R) Set.univ)
    (hrecip_cont : ∀ (L : LaurentForm), Finset.univ.image L.a = Finset.univ.image cs →
      (∀ j, ∃ R : ℂ → ℂ, AnalyticAt ℂ R (cs j) ∧
        (valueChartTrace ω₀ f Φ - L.R) =ᶠ[𝓝[≠] (cs j)] R) →
      ContinuousAt (recipCoeff (valueChartTrace ω₀ f Φ - L.R)) 0) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_traceRationalityDataNF ω₀ g f poles
    (traceRationalityDataNF_ofSheetSections Φ m cs ρ hcs_ball hcs_inj secFin hsecFin_base
      hsecFin_smooth hsecFin_sec hsetFin hxs_inj hxs_mem hxs_surj Dinf hxsInf_inj hxsInf_mem
      hxsInf_surj hcenters_cs hcoh_inf hentire hrecip_cont)

/-! ### Non-vacuity (end-to-end soundness)

For the empty pole set the empty fibre selection assembles into a `TraceRationalityDataNF` through the
moving constructor: no finite pole-values (the per-pole moving data vacuous), the empty sound `∞`-fibre
data, the zero geometric trace, and the trivially-true genus-`0`/`∞` fields.  Confirms the sound
reduction is honest (not a disguised `False`). -/

/-- **Non-vacuity of the sound moving `TraceRationalityDataNF` reduction.**  For the empty pole set the
reduction is satisfiable via the empty selection, yielding `∑Res = 0`. -/
theorem residueSum_eq_zero_of_movingTraceRationalityNF_holomorphic (ω₀ : HolomorphicOneForms X)
    (g : X → ℂ) (f : MeromorphicFunction X) :
    ∑ a ∈ (∅ : Finset X), formFnResidue ω₀ g a = 0 :=
  residueSum_eq_zero_of_movingTraceRationalityNF (g := g) (poles := (∅ : Finset X))
    (fun p => emptyFibreRegularData g f p)
    0 Fin.elim0 0 (fun i => i.elim0) (fun i => i.elim0)
    (fun p => emptyFibreRegularData g f p)
    (fun i => i.elim0) (fun i => i.elim0)
    (fun _ i => i.elim) (fun _ i => i.elim)
    (fun _ a ha => absurd ha (Finset.notMem_empty a))
    (emptyInftyFibreDataNF g f) (fun i => i.elim) (fun i => i.elim)
    (fun a ha => absurd ha (Finset.notMem_empty a))
    (by simp)
    (by rw [valueChartTrace_emptySelection ω₀ f, recipCoeff_zero,
      traceCoeff_inftyFibreTraceNF_empty ω₀ f])
    (by
      intro L hLa _
      rw [valueChartTrace_emptySelection ω₀ f]
      have hLR0 : L.R = fun _ => (0 : ℂ) :=
        laurentForm_R_eq_zero_of_emptyImage
          (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
      rw [hLR0]
      intro z _
      show AnalyticAt ℂ ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) z
      simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) z))
    (by
      intro L hLa _
      rw [valueChartTrace_emptySelection ω₀ f]
      have hLR0 : L.R = fun _ => (0 : ℂ) :=
        laurentForm_R_eq_zero_of_emptyImage
          (by rw [hLa]; exact Finset.image_eq_empty.mpr (Finset.univ_eq_empty (α := Fin 0)))
      rw [hLR0]
      have h0 : ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) = fun _ : ℂ => (0 : ℂ) := by
        funext z; simp
      rw [h0, recipCoeff_zero]
      exact continuousAt_const)

end Jacobians.Dolbeault.FormTraceFullFibre
