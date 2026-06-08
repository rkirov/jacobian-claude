/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceGateAAssemble

/-!
# The canonical full-fibre selection `Φ` (Gate A wall 2, Miranda §VIII.3)

`Jacobians.Dolbeault.FormTraceGateAAssemble.residueSum_eq_zero_of_globalCoverData` reduced Gate A's
`∑ₐ Resₐ(α) = 0` to (wall 1) the adapted-cover genericity, (wall 2) the **global coherent selection**
`Φ` with its regular-value canonical-fibre conditions + the per-pole moving sections, and (wall 3) the
`∞`-rationality.

This file discharges the **regular-value part of wall 2** by constructing the *canonical full-fibre
selection* — at each base value `b`, `Φ b` enumerates the **entire** fibre `F⁻¹(coe b)` of the compact
sphere map `F = f.toRiemannSphere` (whose cardinality is the proper-map degree at regular values), via
the proved finiteness of the fibres (`fibre_finite_of_div_ne_zero`).  The construction is
**monodromy-free** (the symmetric-lever, Miranda §VIII.3): there is no continuous sheet labeling, only
the canonical fibre *as a set*.

The genuine analytic inputs are all *intrinsic to being off the branch locus*:

* every point of a finite-value fibre is a **non-pole** (`nonpole_of_toRiemannSphere_eq_coe`), so the
  `hg_an`/`hval` fields of `FibreRegularData` hold;
* off the branch locus every fibre point is a **regular point of `f`**
  (`sheet_holoRepr_deriv_ne_zero`), so `hg_deriv ≠ 0`.

The only datum-dependent field is `hg_mero` — `g`'s chart pullback meromorphic at the fibre points —
which is supplied as the standard regular-value hypothesis on the numerator `g` of `α = ω₀·g`.

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `FibreRegularData.ofFullFibre` — the full-fibre regularity datum at a value `coe b` off the branch
  locus (every fibre point a regular non-pole), with `g`-meromorphy supplied.
* `canonicalFibreSelection` — the global selection `Φ`: the full-fibre datum at "good" values
  (off-branch, `g`-meromorphic at the fibre), the empty datum elsewhere.
* `canonicalFibreSelection_xs_range` / `_injective` — at a good value the canonical selection
  *injectively enumerates the full fibre* `F⁻¹(coe b)`.
* `canonicalFibreSelection_hΦrangeReg` / `_hΦinjReg` — the **canonical-fibre conditions**
  `hΦrangeReg`/`hΦinjReg` of `residueSum_eq_zero_of_globalCoverData`, eventually near every regular
  value, from the regular-value `g`-data.

## References

* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2; single-valued
  **by symmetry**, the full-fibre symmetric sum).
* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22 (local sheet systems), §17.
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open OnePoint

namespace Jacobians.Dolbeault.FormTraceGlobal

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.Dolbeault.FormTraceFibre Jacobians.RiemannSphere Jacobians.ProperMapDegreeSheets

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

variable {ω₀ : HolomorphicOneForms X} {g : X → ℂ} {f : MeromorphicFunction X}

/-! ### The finite enumeration of the full fibre

For a nonconstant `f` (`f.div ≠ 0`) every sphere fibre is finite (`fibre_finite_of_div_ne_zero`).
We enumerate the fibre `F⁻¹(coe b)` over a finite value `coe b` by `Fin N` via the finset
`(hfib).toFinset` and its `equivFin`. -/

/-- The cardinality of the (finite) fibre `F⁻¹(coe b)` over a finite value `coe b`. -/
def fullFibreCard (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (b : ℂ) : ℕ :=
  (fibre_finite_of_div_ne_zero f hdiv (((b : ℂ) : RiemannSphere))).toFinset.card

/-- The `Fin (fullFibreCard …)`-enumeration of the fibre `F⁻¹(coe b)`:
`Subtype.val ∘ (toFinset).equivFin.symm`. -/
noncomputable def fullFibreEnum (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (b : ℂ) : Fin (fullFibreCard f hdiv b) → X :=
  fun i => ((fibre_finite_of_div_ne_zero f hdiv (((b : ℂ) : RiemannSphere))).toFinset.equivFin.symm
    (Fin.cast (by rw [fullFibreCard]) i) : X)

/-- Each enumerated point lies in the fibre: `F (fullFibreEnum f hdiv b i) = coe b`. -/
theorem fullFibreEnum_mem (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (b : ℂ)
    (i : Fin (fullFibreCard f hdiv b)) :
    f.toRiemannSphere (fullFibreEnum f hdiv b i) = (((b : ℂ) : RiemannSphere)) := by
  have hmem := ((fibre_finite_of_div_ne_zero f hdiv (((b : ℂ) : RiemannSphere))).toFinset.equivFin.symm
    (Fin.cast (by rw [fullFibreCard]) i)).2
  rwa [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff] at hmem

/-- The full-fibre enumeration is **injective**. -/
theorem fullFibreEnum_injective (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    (b : ℂ) : Function.Injective (fullFibreEnum f hdiv b) := by
  intro i j h
  have := (fibre_finite_of_div_ne_zero f hdiv (((b : ℂ) : RiemannSphere))).toFinset.equivFin.symm.injective
    (Subtype.ext h)
  exact Fin.cast_injective _ this

/-- The full-fibre enumeration has **range exactly the fibre** `F⁻¹(coe b)`. -/
theorem fullFibreEnum_range (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (b : ℂ) :
    Set.range (fullFibreEnum f hdiv b) = f.toRiemannSphere ⁻¹' {(((b : ℂ) : RiemannSphere))} := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    exact fullFibreEnum_mem f hdiv b i
  · intro hx
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    have hxF : x ∈ (fibre_finite_of_div_ne_zero f hdiv (((b : ℂ) : RiemannSphere))).toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff]; exact hx
    refine ⟨Fin.cast (by rw [fullFibreCard]) (((fibre_finite_of_div_ne_zero f hdiv
      (((b : ℂ) : RiemannSphere))).toFinset.equivFin) ⟨x, hxF⟩), ?_⟩
    show (((fibre_finite_of_div_ne_zero f hdiv (((b : ℂ) : RiemannSphere))).toFinset.equivFin.symm
      (Fin.cast _ (Fin.cast _ (((fibre_finite_of_div_ne_zero f hdiv
        (((b : ℂ) : RiemannSphere))).toFinset.equivFin) ⟨x, hxF⟩)))) : X) = x
    rw [Fin.cast_cast, Fin.cast_eq_self, Equiv.symm_apply_apply]

/-! ### The full-fibre regularity datum at a regular value

At a finite value `coe b` **off the branch locus**, every point of the fibre `F⁻¹(coe b)` is a
*regular non-pole point* of `f`:

* it is a non-pole (its sphere value `coe b` is finite, `nonpole_of_toRiemannSphere_eq_coe`), so
  `f.holoRepr`'s chart pullback is analytic and `f.holoRepr (xs i) = b` (the `hval` field);
* it is regular (off the branch locus the sphere cover is locally injective, hence the chart-pullback
  derivative is nonzero, `sheet_holoRepr_deriv_ne_zero`).

The only datum-dependent field `hg_mero` (`g`'s chart pullback meromorphic at each fibre point) is
supplied.  This packages the *full* fibre into a `FibreRegularData` — the canonical fibre, with no
labeling. -/

/-- **The full-fibre regularity datum.**  At a finite value `coe b` off the branch locus of `F =
f.toRiemannSphere`, the `FibreRegularData g f b` whose `xs` enumerates the **entire** fibre
`F⁻¹(coe b)` (`fullFibreEnum`).  Every fibre point is a regular non-pole (intrinsic to being
off-branch); `hg_mero` is supplied. -/
noncomputable def FibreRegularData.ofFullFibre (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (b : ℂ)
    (hoff : (((b : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hmero : ∀ i, MeromorphicAt
      (fun z => g ((chartAt ℂ (fullFibreEnum f hdiv b i)).symm z))
      ((chartAt ℂ (fullFibreEnum f hdiv b i)) (fullFibreEnum f hdiv b i))) :
    FibreRegularData g f b :=
  FibreRegularData.ofRegular g f b
    (ι := Fin (fullFibreCard f hdiv b))
    (xs := fullFibreEnum f hdiv b)
    (hnp := fun i => (f.nonpole_of_toRiemannSphere_eq_coe (fullFibreEnum_mem f hdiv b i)).1)
    (hderiv := fun i =>
      sheet_holoRepr_deriv_ne_zero f hdiv hoff (fullFibreEnum_mem f hdiv b i))
    (hval := fun i => (f.nonpole_of_toRiemannSphere_eq_coe (fullFibreEnum_mem f hdiv b i)).2)
    (hmero := hmero)

@[simp] theorem FibreRegularData.ofFullFibre_xs (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) (b : ℂ)
    (hoff : (((b : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hmero : ∀ i, MeromorphicAt
      (fun z => g ((chartAt ℂ (fullFibreEnum f hdiv b i)).symm z))
      ((chartAt ℂ (fullFibreEnum f hdiv b i)) (fullFibreEnum f hdiv b i))) (i) :
    (FibreRegularData.ofFullFibre (g := g) f hdiv b hoff hmero).xs i = fullFibreEnum f hdiv b i :=
  rfl

/-! ### The canonical global full-fibre selection `Φ`

`Φ b` is the full-fibre datum at every value where it can be built — the **good values** `b`, where
`coe b` is off the branch locus and `g`'s chart pullback is meromorphic at each fibre point.  At every
other value (branch values, or values with bad `g`-data) `Φ b` is the empty datum.  This is the
*canonical* selection: at regular values it enumerates the **full** fibre with no labeling, exactly the
symmetric-lever input of `MovingCoherenceDatum.ofSphereSheetSystemCanon`.

The empty fallback at branch values is harmless: the branch-value crux of
`residueSum_eq_zero_of_globalCoverData` is handled by the **bundle trace SUM** (`αBr`, the
monodromy-free symmetric extension), not by `Φ` at the branch value; the canonical-fibre conditions
`hΦrangeReg`/`hΦinjReg` are required only *near regular values* (off `cs ∪ branchValues f`), where `Φ`
*is* the full fibre. -/

/-- **The good-value predicate.**  `b` is *good* when `coe b` is off the branch locus of `F =
f.toRiemannSphere` and `g`'s chart pullback is meromorphic at every full-fibre point over `coe b`.  At
good values the canonical selection enumerates the full fibre as a regular non-pole family. -/
def GoodValue (g : X → ℂ) (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0) (b : ℂ) :
    Prop :=
  (((b : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere ∧
  ∀ i, MeromorphicAt (fun z => g ((chartAt ℂ (fullFibreEnum f hdiv b i)).symm z))
    ((chartAt ℂ (fullFibreEnum f hdiv b i)) (fullFibreEnum f hdiv b i))

/-- **The canonical full-fibre selection.**  `Φ b` is the full-fibre datum at good values and the empty
datum elsewhere. -/
noncomputable def canonicalFibreSelection (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) : (b : ℂ) → FibreRegularData g f b :=
  fun b => if h : GoodValue g f hdiv b then FibreRegularData.ofFullFibre f hdiv b h.1 h.2
    else emptyFibreRegularData g f b

/-- At a **good value**, the canonical selection *is* the full-fibre datum. -/
theorem canonicalFibreSelection_eq_ofFullFibre (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {b : ℂ} (h : GoodValue g f hdiv b) :
    canonicalFibreSelection g f hdiv b = FibreRegularData.ofFullFibre f hdiv b h.1 h.2 := by
  rw [canonicalFibreSelection, dif_pos h]

/-- At a **good value**, the canonical selection's fibre points are `fullFibreEnum` — so the underlying
fibre-point map has **range exactly the full fibre** `F⁻¹(coe b)`. -/
theorem canonicalFibreSelection_xs_range (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {b : ℂ} (h : GoodValue g f hdiv b) :
    Set.range (canonicalFibreSelection g f hdiv b).xs
      = f.toRiemannSphere ⁻¹' {(((b : ℂ) : RiemannSphere))} := by
  rw [canonicalFibreSelection_eq_ofFullFibre g f hdiv h]
  -- `(ofFullFibre …).xs = fullFibreEnum …` definitionally; `fullFibreEnum`'s range is the fibre.
  exact fullFibreEnum_range f hdiv b

/-- At a **good value**, the canonical selection's fibre points are **injective**. -/
theorem canonicalFibreSelection_xs_injective (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {b : ℂ} (h : GoodValue g f hdiv b) :
    Function.Injective (canonicalFibreSelection g f hdiv b).xs := by
  rw [canonicalFibreSelection_eq_ofFullFibre g f hdiv h]
  exact fullFibreEnum_injective f hdiv b

/-! ### Off-branch good-value neighbourhoods

A value `z` with `coe z ∉ branchLocus` has a whole neighbourhood of values `b'` with `coe b' ∉
branchLocus`: the branch locus is closed (finite, for a nonconstant `f`), so its complement is open,
and `coe` is continuous.  This is the first half of the good-value condition near a regular value. -/

/-- **Off-branch is an open condition (finite-value side).**  If `coe z ∉ branchLocus
f.toRiemannSphere`, then `coe b' ∉ branchLocus f.toRiemannSphere` for all `b'` near `z`. -/
theorem eventually_notMem_branchLocus (f : MeromorphicFunction X) (hdiv : (f.div : Divisor X) ≠ 0)
    {z : ℂ} (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere) :
    ∀ᶠ b' in 𝓝 z, (((b' : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere := by
  -- The branch locus is closed (finite), so its complement is open and `coe ⁻¹' (branchLocusᶜ)` is a
  -- neighbourhood of `z` (continuity of `coe`, `z` in it).
  have hfin : (branchLocus f.toRiemannSphere).Finite :=
    finite_branchLocus_of_nonconstant f.toRiemannSphere f.contMDiff_toRiemannSphere
      (hncF_of_div_ne_zero f hdiv)
  have hopen : IsOpen ((branchLocus f.toRiemannSphere)ᶜ) := hfin.isClosed.isOpen_compl
  have hmem : ((fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' (branchLocus f.toRiemannSphere)ᶜ)
      ∈ 𝓝 z :=
    (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds (hopen.mem_nhds hz)
  filter_upwards [hmem] with b' hb' using hb'

/-! ### The canonical-fibre conditions `hΦrangeReg` / `hΦinjReg`

At a regular value `z` (off the finite branch values), the canonical selection enumerates the full
fibre `F⁻¹(coe b')` for every `b'` near `z` — *provided* `g`'s chart pullback is meromorphic at the
fibre points there (the standard regular-value `g`-data, the only datum-dependent input).  This gives
both `hΦrangeReg` (the range is the fibre) and `hΦinjReg` (the enumeration is injective) — the two
canonical-fibre conditions of `residueSum_eq_zero_of_globalCoverData`. -/

/-- **`hΦrangeReg` for the canonical selection.**  At a value `z` off the branch values (`coe z ∉
branchLocus`), the canonical full-fibre selection enumerates the **full fibre** `F⁻¹(coe b')` for `b'`
near `z`, given the regular-value `g`-meromorphy `hgmero` (`g`'s chart pullback meromorphic at the
full-fibre points, eventually near `z`).  Off-branch is an open condition (`eventually_notMem_branchLocus`)
so each such `b'` is a *good value*, where the canonical selection is the full-fibre datum. -/
theorem canonicalFibreSelection_hΦrangeReg (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hgmero : ∀ᶠ b' in 𝓝 z, ∀ i,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' i)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' i)) (fullFibreEnum f hdiv b' i))) :
    ∀ᶠ b' in 𝓝 z, Set.range (canonicalFibreSelection g f hdiv b').xs
      = f.toRiemannSphere ⁻¹' {(((b' : ℂ) : RiemannSphere))} := by
  filter_upwards [eventually_notMem_branchLocus f hdiv hz, hgmero] with b' hb'off hb'mero
  exact canonicalFibreSelection_xs_range g f hdiv ⟨hb'off, hb'mero⟩

/-- **`hΦinjReg` for the canonical selection.**  At a value `z` off the branch values, the canonical
full-fibre selection's fibre points are **injective** for `b'` near `z`, given the regular-value
`g`-meromorphy `hgmero`.  (Same good-value neighbourhood as `hΦrangeReg`.) -/
theorem canonicalFibreSelection_hΦinjReg (g : X → ℂ) (f : MeromorphicFunction X)
    (hdiv : (f.div : Divisor X) ≠ 0) {z : ℂ}
    (hz : (((z : ℂ) : RiemannSphere)) ∉ branchLocus f.toRiemannSphere)
    (hgmero : ∀ᶠ b' in 𝓝 z, ∀ i,
      MeromorphicAt (fun w => g ((chartAt ℂ (fullFibreEnum f hdiv b' i)).symm w))
        ((chartAt ℂ (fullFibreEnum f hdiv b' i)) (fullFibreEnum f hdiv b' i))) :
    ∀ᶠ b' in 𝓝 z, Function.Injective (canonicalFibreSelection g f hdiv b').xs := by
  filter_upwards [eventually_notMem_branchLocus f hdiv hz, hgmero] with b' hb'off hb'mero
  exact canonicalFibreSelection_xs_injective g f hdiv ⟨hb'off, hb'mero⟩

end Jacobians.Dolbeault.FormTraceGlobal
