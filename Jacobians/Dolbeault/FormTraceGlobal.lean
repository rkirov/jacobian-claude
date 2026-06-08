/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceFibre

/-!
# The global trace assembly → `FormResidueTrace` (Gate A, node A-ii — bridge (d))

This file assembles the per-fibre trace data (`Jacobians.Dolbeault.FormTraceFibre`) over **all** the
finite fibres into a `Jacobians.Dolbeault.FormResidueTheorem.FormResidueTrace`, which closes Gate A
(the 1-form residue theorem `∑ₐ Resₐ(α) = 0`) for the represented `α = ω₀·g`.

It packages the irreducible remaining content — the **rationality of the trace** `Tr_F α` on `ℂℙ¹`
and the **unramifiedness of `f` over the finite pole values** — into a single honest bundle
`GlobalTraceData`, and proves that *given* such a bundle the full `FormResidueTrace` exists, with the
two aggregate identifications `finite_eq`/`infty_eq` discharged from the per-fibre work
(`resAt_traceCoeff_fibreTrace`, `fibreResidueSum_eq_filter`) plus a `coe`-injective re-indexing of the
finite-center sum.

## The `GlobalTraceData` bundle (what remains)

`GlobalTraceData ω₀ g f poles` carries:
* `L : LaurentForm` — the rational `1`-form representing `Tr_F α` on `ℂℙ¹` (the rationality witness);
* `D : (p : ℂ) → FibreRegularData g f p` — per-center fibre regularity data, with `(D p).xs`
  injectively enumerating exactly the poles in the fibre `F⁻¹(coe p)` (`hxs_inj`/`hxs_mem`/`hxs_surj`);
* `hcenters` — the centers of `L`, mapped to the sphere by `coe`, are exactly the finite pole values
  `(poles.image F).erase ∞` (so the finite-center sum re-indexes to the finite-fibre sum);
* `hL32` — Miranda's Lemma 3.2 at the finite centers (the fibre-residue sum equals `L.R`'s residue);
* `infty_eq` — Lemma 3.2 at `∞` (the residue at infinity of `L.R` is the `∞`-fibre residue sum).

Everything *except* `L`, `D`, `hcenters`, `hL32`, `infty_eq` is discharged here; `finite_eq` is
**proved**.  The remaining obligation is exactly the construction of a `GlobalTraceData` for a general
nonconstant `f` — the trace rationality + the unramified-fibre regular-value data — which is the
last §VIII.3-level analytic content (see the diagnosis at the bottom).

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; rationality
  / partial fractions on `ℂℙ¹`).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.Dolbeault.FormResidueTheorem

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The global trace data bundle** for `α = ω₀·g` through `F = f.toRiemannSphere`, over the pole set
`poles`.  The honest geometric+rational input from which the full `FormResidueTrace` is assembled
(everything downstream proved sorry-free).  Its fields are exactly the §VIII.3 trace output:

* `L` — the rational trace `Tr_F α` as a `LaurentForm` on `ℂℙ¹`;
* `D` — per-center unramified-fibre regularity data, `(D p).xs` enumerating `poles ∩ F⁻¹(coe p)`;
* `hcenters` — the `L`-centers are the finite pole values (so the center sum is the finite-fibre sum);
* `hL32` — Lemma 3.2 at the finite centers (the manifold bookkeeping that `L` *is* the trace);
* `infty_eq` — Lemma 3.2 at `∞`. -/
structure GlobalTraceData (ω₀ : HolomorphicOneForms X) (g : X → ℂ) (f : MeromorphicFunction X)
    (poles : Finset X) where
  /-- The rational `1`-form representing `Tr_F α` on `ℂℙ¹`. -/
  L : LaurentForm
  /-- Per-center unramified-fibre regularity data. -/
  D : (p : ℂ) → FibreRegularData g f p
  /-- `(D p).xs` is injective (each fibre point enumerated once). -/
  hxs_inj : ∀ p, Function.Injective (D p).xs
  /-- `(D p).xs` lands in the poles, in the fibre `F⁻¹(coe p)`. -/
  hxs_mem : ∀ p, ∀ i, (D p).xs i ∈ poles ∧ f.toRiemannSphere ((D p).xs i) = ((p : ℂ) : RiemannSphere)
  /-- `(D p).xs` enumerates *all* the poles in the fibre `F⁻¹(coe p)`. -/
  hxs_surj : ∀ p, ∀ a ∈ poles, f.toRiemannSphere a = ((p : ℂ) : RiemannSphere) → ∃ i, (D p).xs i = a
  /-- The `L`-centers, mapped to the sphere, are exactly the finite pole values. -/
  hcenters : (Finset.univ.image L.a).image (fun p : ℂ => ((p : ℂ) : RiemannSphere))
    = (poles.image f.toRiemannSphere).erase OnePoint.infty
  /-- Lemma 3.2 at the finite centers. -/
  hL32 : ∀ p ∈ (Finset.univ.image L.a),
    (∑ i, resAt ((fibreTrace ω₀ f (D p)).coeff i) ((fibreTrace ω₀ f (D p)).pre i))
      = resAt L.R p
  /-- Lemma 3.2 at `∞`: the residue at infinity is the `∞`-fibre residue sum. -/
  infty_eq : resAtInfty L.R L.ρ
    = ∑ a ∈ poles with f.toRiemannSphere a = OnePoint.infty, formFnResidue ω₀ g a

namespace GlobalTraceData

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X} {poles : Finset X}
  (T : GlobalTraceData ω₀ g f poles)

/-- The per-center fibre datum bundled as a `FibreTrace` (the `fibreTrace` of the regularity data). -/
noncomputable def fibre (p : ℂ) : FibreTrace := fibreTrace ω₀ f (T.D p)

/-- **The finite-center trace-residue total equals the finite-fibre residue sum** (bridge (d), the
`finite_eq` field of `FormResidueTrace`).  Each center's trace residue is the per-fibre residue sum
(`resAt_traceCoeff_fibreTrace`), which is the fibre-restricted pole sum (`fibreResidueSum_eq_filter`);
the centers re-index to the finite pole values by `hcenters` (`coe` injective). -/
theorem finite_eq :
    (∑ p ∈ Finset.univ.image T.L.a, resAt (T.fibre p).traceCoeff (T.fibre p).b)
      = ∑ y ∈ (poles.image f.toRiemannSphere).erase OnePoint.infty,
          ∑ a ∈ poles with f.toRiemannSphere a = y, formFnResidue ω₀ g a := by
  classical
  -- Step 1: rewrite each center's trace residue as the fibre-restricted pole sum.
  have hcenter : ∀ p ∈ Finset.univ.image T.L.a,
      resAt (T.fibre p).traceCoeff (T.fibre p).b
        = ∑ a ∈ poles with f.toRiemannSphere a = ((p : ℂ) : RiemannSphere), formFnResidue ω₀ g a := by
    intro p _
    rw [show (T.fibre p) = fibreTrace ω₀ f (T.D p) from rfl,
      resAt_traceCoeff_fibreTrace ω₀ f (T.D p),
      fibreResidueSum_eq_filter ω₀ f (T.D p) poles (T.hxs_inj p) (T.hxs_mem p) (T.hxs_surj p)]
  rw [Finset.sum_congr rfl hcenter]
  -- Step 2: re-index `∑_{p ∈ centers} = ∑_{y ∈ centers.image coe}` (coe injective), then `hcenters`.
  rw [← T.hcenters,
    Finset.sum_image (fun p _ q _ h => OnePoint.coe_injective h)]

/-- **The full `FormResidueTrace` from a `GlobalTraceData`.**  Given the rationality+regularity bundle
`T`, the represented `α = ω₀·g` has a `FormResidueTrace` — hence `∑ₐ Resₐ(α) = 0` (Gate A) by
`residueSum_eq_zero_of_formResidueTrace`.  `finite_eq` is `T.finite_eq`; `infty_eq`/`hL32` are `T`'s
own fields. -/
noncomputable def toFormResidueTrace (T : GlobalTraceData ω₀ g f poles) :
    FormResidueTrace ω₀ g where
  f := f
  poles := poles
  L := T.L
  fibre := T.fibre
  hL32 := T.hL32
  infty_eq := T.infty_eq
  finite_eq := T.finite_eq

@[simp] theorem toFormResidueTrace_poles (T : GlobalTraceData ω₀ g f poles) :
    (T.toFormResidueTrace).poles = poles := rfl

/-- **Gate A for the represented form, from a `GlobalTraceData`.**  The total residue of `α = ω₀·g`
over its poles vanishes:

> `∑_{a ∈ poles} Res_a(α) = 0`. -/
theorem residueSum_eq_zero (T : GlobalTraceData ω₀ g f poles) :
    ∑ a ∈ poles, formFnResidue ω₀ g a = 0 := by
  have h := residueSum_eq_zero_of_formResidueTrace ω₀ g (T.toFormResidueTrace)
  simpa only [toFormResidueTrace_poles] using h

end GlobalTraceData

/-! ### Non-vacuity of `GlobalTraceData`

The `GlobalTraceData` obligations are genuine (true, satisfiable), not a disguised `False`: in the
**globally-holomorphic** case (`α = ω₀·g` has no poles), we exhibit a `GlobalTraceData` with the
**empty pole set** — the empty `LaurentForm` (no centers, trace `≡ 0`), empty per-center fibre data
(`ι = Empty`), and vacuous `hcenters`/`hL32`/`infty_eq`.  This confirms the structure is honest (it
*is* satisfiable, and the residue theorem does hold in this case with the trivial trace), mirroring
`Jacobians.Dolbeault.FormResidueTheorem.formResidueTrace_of_holomorphic`. -/

/-- The **empty `FibreRegularData`** over any base value `p`: no fibre points (`ι = Empty`), so all
field hypotheses are vacuous.  The fibre datum over a value with no (recorded) preimages. -/
def emptyFibreRegularData (g : X → ℂ) (f : MeromorphicFunction X) (p : ℂ) :
    FibreRegularData g f p where
  ι := Empty
  fintype_ι := inferInstance
  xs := Empty.elim
  hg_an := fun i => i.elim
  hg_deriv := fun i => i.elim
  hval := fun i => i.elim
  hg_mero := fun i => i.elim

/-- **Non-vacuity witness.**  A `GlobalTraceData ω₀ g f ∅` always exists (empty pole set): the empty
`LaurentForm`, empty per-center fibre data, and vacuous identifications.  Hence the `GlobalTraceData`
obligations are *satisfiable* — the structure is not a disguised `False`. -/
noncomputable def globalTraceData_empty (ω₀ : HolomorphicOneForms X) (g : X → ℂ)
    (f : MeromorphicFunction X) : GlobalTraceData ω₀ g f ∅ where
  L := Jacobians.ResidueTheoremX.emptyLaurentForm
  D := fun p => emptyFibreRegularData g f p
  hxs_inj := by intro _ i; exact i.elim
  hxs_mem := fun _ i => i.elim
  hxs_surj := fun _ a ha => absurd ha (Finset.notMem_empty a)
  hcenters := by
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a]
    simp
  hL32 := by
    intro p hp
    rw [Jacobians.ResidueTheoremX.emptyLaurentForm_image_a] at hp
    exact absurd hp (Finset.notMem_empty p)
  infty_eq := by
    rw [resAtInfty, Jacobians.ResidueTheoremX.emptyLaurentForm_R]
    show -(2 * π * I : ℂ)⁻¹ • (∮ _z in C((0 : ℂ),
      Jacobians.ResidueTheoremX.emptyLaurentForm.ρ), (0 : ℂ)) = _
    rw [show Jacobians.ResidueTheoremX.emptyLaurentForm.ρ = 0 from rfl,
      circleIntegral.integral_radius_zero, smul_zero]
    simp

end Jacobians.Dolbeault.FormTraceGlobal
