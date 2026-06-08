/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.FormTraceMovingFibreSheet
import Jacobians.ToSphereGeneral

/-!
# Translating sphere-sheets to `holoRepr`-sections (Gate A, §VIII.3 — part (A))

`Jacobians.Dolbeault.FormTraceMovingFibreSheet` reduced Gate A's `∑Res = 0` to a single
`MovingSheetSelection`, whose per-value moving data is itself reduced (via
`MovingCoherenceDatum.ofSheetSections`) to **continuously-varying manifold sections of `f.holoRepr`**
plus the §VIII.3 re-selection bijection.  *All* germ / `dz`-Jacobian / differentiability content is
discharged there.

The branched-cover sheets that supply those sections exist by `Jacobians.exists_localSheetSystem`
(Forster §4.22) — but only for the **compact** sphere map `f.toRiemannSphere : X → RiemannSphere`,
since `exists_localSheetSystem` requires a `CompactSpace` codomain and `f.holoRepr`'s codomain `ℂ`
is non-compact.  This file builds the **translation** that the status doc identifies as the precise
concrete residual of part (A):

> a `LocalSheetSystem f.toRiemannSphere (coe b₀)` over a finite-value region, restricted to finite
> values via `coe : ℂ → RiemannSphere`, yields sections of `f.holoRepr`:
> `f.holoRepr (sheet (coe b')) = b'`.

The construction is purely from the proved `MeromorphicFunction.toRiemannSphere_of_nonneg`
(`toRiemannSphere y = coe (holoRepr y)` at non-poles) + `OnePoint.coe` injectivity + the fact that
a point whose sphere value `coe c` is *finite* is a non-pole (`toRiemannSphere_preimage_infty`).

## What this file proves (axiom-clean `[propext, Classical.choice, Quot.sound]`)

* `MeromorphicFunction.nonpole_of_toRiemannSphere_eq_coe` — a point with finite sphere value `coe c`
  is a non-pole (`0 ≤ orderAtPoint`) and has `holoRepr = c`.
* `MeromorphicFunction.contMDiffAt_coe` — the coercion `coe : ℂ → RiemannSphere` is `C^ω` at every
  finite point (read in the affine chart `chartCoe`, it is the identity).
* `holoReprSection` — from a sphere-sheet `s : RiemannSphere → X` over `coe b₀`, the planar section
  `b' ↦ s (coe b')` of `f.holoRepr`, with the section property, base value, and `C^ω`-smoothness near
  `b₀` all proved.
* `LocalSheetSystem.holoReprSection_section` / `_base` / `_smooth` — the same packaged from a
  `LocalSheetSystem f.toRiemannSphere (coe b₀)`.

## References

* Forster, *Lectures on Riemann Surfaces* (GTM 81), §4.22 (local sheet systems).
* Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3 (the trace `Tr`, Lemma 3.2).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real
open OnePoint

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### A point with a finite sphere value is a non-pole -/

/-- **A finite sphere value forces a non-pole + identifies `holoRepr`.**  If `f.toRiemannSphere x =
coe c` (a *finite* sphere value), then `x` is a non-pole (`0 ≤ orderAtPoint x`) and `f.holoRepr x =
c`.  The sphere value is `≠ ∞`, so by `toRiemannSphere_preimage_infty` the order is `≥ 0`; then
`toRiemannSphere x = coe (holoRepr x)` (`toRiemannSphere_of_nonneg`) and `coe` injectivity give
`holoRepr x = c`.  This is the value-side translation `sphere-value ↦ holoRepr-value`. -/
theorem MeromorphicFunction.nonpole_of_toRiemannSphere_eq_coe (f : MeromorphicFunction X) {x : X}
    {c : ℂ} (hx : f.toRiemannSphere x = ((c : ℂ) : RiemannSphere)) :
    0 ≤ f.orderAtPoint x ∧ f.holoRepr x = c := by
  have hne : f.toRiemannSphere x ≠ OnePoint.infty := by
    rw [hx]; exact OnePoint.coe_ne_infty c
  have hnp : 0 ≤ f.orderAtPoint x := by
    by_contra hlt
    exact hne (f.toRiemannSphere_of_pole (not_le.mp hlt))
  refine ⟨hnp, ?_⟩
  rw [f.toRiemannSphere_of_nonneg hnp] at hx
  exact OnePoint.coe_injective hx

/-! ### Smoothness of the coercion `ℂ → RiemannSphere`

The coercion `coe : ℂ → RiemannSphere` is `C^ω` at every finite point: read in the affine chart
`chartCoe` (which is the canonical chart at any finite point), the chart pullback `chartCoe ∘ coe` is
the identity `ℂ → ℂ`, which is analytic.  This is what lets us compose a sphere-sheet with `coe` to
get a *smooth* planar section of `f.holoRepr`. -/

/-- **The coercion `coe : ℂ → RiemannSphere` is `C^ω` at every point.**  The canonical chart at the
finite point `coe c` is the affine chart `chartCoe`, whose inverse `chartCoe.symm` *is* the coercion
`coe` (`chartCoe_symm_apply`).  The inverse chart is `C^ω` on its target (`contMDiffOn_chart_symm`),
and `chartCoe.target = univ`, so `coe` is `ContMDiffAt` everywhere. -/
theorem MeromorphicFunction.contMDiffAt_coe (c : ℂ) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℂ => ((z : ℂ) : RiemannSphere)) c := by
  -- `coe = (chartAt ℂ (coe c)).symm` and the inverse chart is `C^ω` on its target `= univ`.
  have hsymm : (chartAt ℂ (((c : ℂ) : RiemannSphere))).symm = (fun z : ℂ => ((z : ℂ) : RiemannSphere)) := by
    rw [RiemannSphere.chartAt_coe]
    funext z; exact RiemannSphere.chartCoe_symm_apply z
  have hc_target : c ∈ (chartAt ℂ (((c : ℂ) : RiemannSphere))).target := by
    rw [RiemannSphere.chartAt_coe, RiemannSphere.chartCoe_target]; trivial
  have hsmoothOn : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (chartAt ℂ (((c : ℂ) : RiemannSphere))).symm
      (chartAt ℂ (((c : ℂ) : RiemannSphere))).target :=
    contMDiffOn_chart_symm (I := 𝓘(ℂ)) (n := ω) (x := (((c : ℂ) : RiemannSphere)))
  have := hsmoothOn.contMDiffAt
    ((chartAt ℂ (((c : ℂ) : RiemannSphere))).open_target.mem_nhds hc_target)
  rwa [hsymm] at this

/-! ### The `holoRepr`-section from a sphere-sheet

Given a sphere-sheet `s : RiemannSphere → X` that is a section of `f.toRiemannSphere` over a
neighbourhood `V` of `coe b₀` (i.e. `f.toRiemannSphere (s w) = w` for `w ∈ V`) and `C^ω` there, the
planar function `b' ↦ s (coe b')` is a section of `f.holoRepr` near `b₀`:

* `f.toRiemannSphere (s (coe b')) = coe b'` (section), a *finite* value, so `s (coe b')` is a non-pole
  with `f.holoRepr (s (coe b')) = b'` (`nonpole_of_toRiemannSphere_eq_coe`);
* smoothness is `s ∘ coe`, the composite of the `C^ω` coercion (`contMDiffAt_coe`) and the `C^ω`
  sheet. -/

/-- **The planar `holoRepr`-section from a sphere-sheet.**  `holoReprSection s b' := s (coe b')`. -/
def holoReprSection (s : RiemannSphere → X) (b' : ℂ) : X := s (((b' : ℂ) : RiemannSphere))

@[simp] theorem holoReprSection_apply (s : RiemannSphere → X) (b' : ℂ) :
    holoReprSection s b' = s (((b' : ℂ) : RiemannSphere)) := rfl

/-- **The translated section is a section of `f.holoRepr`.**  If `s` is a section of
`f.toRiemannSphere` over an open `V ∋ coe b'` (`f.toRiemannSphere (s w) = w` on `V`), then
`f.holoRepr (holoReprSection s b') = b'`: the sphere value `coe b'` is finite, so the sheet point is
a non-pole identified by `nonpole_of_toRiemannSphere_eq_coe`. -/
theorem holoReprSection_section (f : MeromorphicFunction X) {s : RiemannSphere → X} {V : Set ℂ}
    {b' : ℂ} (hb'V : b' ∈ V)
    (hsec : ∀ w ∈ V, f.toRiemannSphere (s (((w : ℂ) : RiemannSphere))) = ((w : ℂ) : RiemannSphere)) :
    f.holoRepr (holoReprSection s b') = b' :=
  (f.nonpole_of_toRiemannSphere_eq_coe (hsec b' hb'V)).2

/-- **The translated section is `C^ω` at the base.**  If the sphere-sheet `s` is `ContMDiffOn 𝓘(ℂ)
𝓘(ℂ) ω` on an open sphere neighbourhood `W ∋ coe b₀`, then `holoReprSection s = s ∘ coe` is
`ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` at `b₀`: it is the composite of the `C^ω` coercion (`contMDiffAt_coe`)
and the `C^ω` sheet (restricted to the neighbourhood `coe b₀ ∈ W`). -/
theorem holoReprSection_contMDiffAt {s : RiemannSphere → X} {W : Set RiemannSphere}
    (hW : IsOpen W) {b₀ : ℂ} (hb₀W : (((b₀ : ℂ) : RiemannSphere)) ∈ W)
    (hs : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω s W) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (holoReprSection s) b₀ := by
  have hsAt : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω s (((b₀ : ℂ) : RiemannSphere)) :=
    hs.contMDiffAt (hW.mem_nhds hb₀W)
  exact hsAt.comp b₀ (MeromorphicFunction.contMDiffAt_coe b₀)

/-! ### Packaging from a `LocalSheetSystem` for the sphere map

A `LocalSheetSystem f.toRiemannSphere (coe b₀)` (which exists by `exists_localSheetSystem` off the
branch locus of the *compact* sphere map) gives, for each sheet `i`, a `holoReprSection (S.sheet i)`
of `f.holoRepr` near `b₀` — smooth, with the section property and the base value read off the sheet
fields.  These are exactly the per-sheet section data `MovingCoherenceDatum.ofSheetSections` consumes
once the §VIII.3 re-selection bijection is supplied. -/

namespace LocalSheetSystem

variable {f : MeromorphicFunction X} {b₀ : ℂ} (S : LocalSheetSystem f.toRiemannSphere (((b₀ : ℂ) : RiemannSphere)))

/-- The `holoRepr`-section read off sheet `i` of a sphere sheet system: `b' ↦ S.sheet i (coe b')`. -/
def holoReprSheet (i : Fin S.n) : ℂ → X := holoReprSection (S.sheet i)

/-- `b₀` lies in the *finite-value* preimage `coe ⁻¹' S.V` of the sphere base neighbourhood. -/
theorem mem_coe_preimage_V : b₀ ∈ ((fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' S.V) := S.mem_V

/-- `coe ⁻¹' S.V` is a neighbourhood of `b₀` (continuity of `coe`, openness of `S.V`). -/
theorem coe_preimage_V_mem_nhds :
    ((fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' S.V) ∈ 𝓝 b₀ :=
  (OnePoint.continuous_coe.continuousAt).preimage_mem_nhds (S.isOpen_V.mem_nhds S.mem_V)

/-- **Each `holoReprSheet` passes through the fibre point at the base.**  `holoReprSheet S i b₀ =
S.sheet i (coe b₀)` by definition. -/
@[simp] theorem holoReprSheet_base (i : Fin S.n) :
    S.holoReprSheet i b₀ = S.sheet i (((b₀ : ℂ) : RiemannSphere)) := rfl

/-- **Each `holoReprSheet` is `C^ω` at `b₀`.**  The sheet `S.sheet i` is `C^ω` on the open `S.V ∋
coe b₀`; compose with the `C^ω` coercion. -/
theorem holoReprSheet_contMDiffAt (i : Fin S.n) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω (S.holoReprSheet i) b₀ :=
  holoReprSection_contMDiffAt S.isOpen_V S.mem_V (S.sheet_smooth i)

/-- **Each `holoReprSheet` is a section of `f.holoRepr` near `b₀`.**  On the neighbourhood `coe ⁻¹'
S.V` of `b₀`, `S.sheet i (coe b')` is a section of `f.toRiemannSphere` (sphere value `coe b'`,
finite), hence `f.holoRepr (holoReprSheet S i b') = b'`. -/
theorem holoReprSheet_section (i : Fin S.n) :
    ∀ᶠ b' in 𝓝 b₀, f.holoRepr (S.holoReprSheet i b') = b' := by
  filter_upwards [S.coe_preimage_V_mem_nhds] with b' hb'
  -- `hb' : coe b' ∈ S.V`; the sheet is a section of the sphere map there.
  exact holoReprSection_section f (V := (fun w : ℂ => ((w : ℂ) : RiemannSphere)) ⁻¹' S.V) hb'
    (fun w hw => S.sheet_section i (((w : ℂ) : RiemannSphere)) hw)

end LocalSheetSystem

end Jacobians
