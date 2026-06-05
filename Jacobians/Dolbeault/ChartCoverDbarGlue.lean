/-
  Čech finiteness — the genuine-cover ∂̄-globalization FOUNDATION (Forster §13–§14, Dolbeault).

  This file banks the verified, axiom-clean foundation for discharging the (corrected) disk-acyclicity
  `leray` field of the chart-cover model — the cross-chart analogue of the single-chart prototype in
  `GluedDbarDatum.lean`.

  ## Why a fresh file (and why the SharedChartCover prototype does not directly apply)

  `GluedDbarDatum.lean` globalises a cocycle on a `SharedChartCover` — a finite family of opens living
  in ONE chart `φ = chartAt center`.  Its partition of unity sums to `1` only on a CLOSED CORE
  `C ⊊ ⋃ Uᵢ` (a subordinate PoU cannot sum to `1` on the open `⋃ Uᵢ` of a non-covering family on a
  connected `X`); that is precisely the obstruction `dbarDatum_agrees_on_interiorCore` documents — the
  glued datum agrees with `∂̄(chartPrim)` only on `interior C`, so it does NOT give a full
  `HasGluedDbarDatum`.  A single chart cannot cover a compact connected Riemann surface, so the
  `SharedChartCover` route is fundamentally partial.

  The GENUINE chart cover (`Montel`'s `chartCover`, the geometry of `CechModelGeometry.lean`) is a
  different beast: the OUTER opens `chartOpen a` (indexed by the cover charts `coverCenter a`) genuinely
  COVER `X` (`iUnion_chartOpen_eq`).  Therefore a smooth partition of unity subordinate to
  `(chartOpen a)` summing to `1` on ALL of `X` exists (`exists_genuineCoverPoU`, below) — exactly what
  `SharedChartCover` lacked.  This unblocks the PoU-globalization OVER THE COVERED REGION (here all of
  `X`), the right tool for the cross-chart Forster argument once the model's shrinking-side cochains are
  in the holomorphic (`BddHol`) representation (see the `⚠ SOUNDNESS NOTE` in `CechModelDifferential.lean`
  — the current continuous `Cshr` makes the literal `ChartCoverLeray` unprovable, so the telescoping is
  intentionally NOT plugged into that unsound field here).

  ## What is delivered (all sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)

  * `exists_genuineCoverPoU` — a smooth PoU over `𝓘(ℝ,ℂ)`, subordinate to `(chartOpen (coverCenter a))`,
    summing to `1` on ALL of `X` (the genuine-cover globalization foundation).
  * `genuineCoverPoU` / `genuineCoverPoU_subordinate` / `sum_genuineCoverPoU_eq_one` — the chosen PoU and
    its sum-to-one-everywhere value form (no closed-core restriction needed — the cover covers).
  * `genuineCoverPoU_tsupport_subset` — the subordination `tsupport ρ_a ⊆ chartOpen (coverCenter a)`.

  ## What remains (the genuine analytic gap, documented — NOT a sorry here)

  The cross-chart telescoping of the Bott–Tu glued datum `ω̂ = ∑_{a,b}(ρ_b·h_{ab})·∂̄ρ_a` read across
  DIFFERENT charts (the `h_{ab}` live in chart-`a`, `chart-`b transitions enter), plus the holomorphic
  re-splitting `dbar_solvable_ball` per chart-disk, and the assembly into the holomorphic cover cocycle.
  This is Forster *Lectures on Riemann Surfaces* Thm 14.x / the Dolbeault lemma globalised by a PoU; it
  consumes `DbarDiskCohomology.dbar_solvable_ball` (proven) and the chart-transition Wirtinger chain rule
  (`dbarDisk_comp_holo`, proven in `CechDiskAcyclic`).  It is left for the corrected (holomorphic-`Cshr`)
  model; the single-chart telescoping in `GluedDbarDatum.dbarDatum_apply` is the prototype.
-/
import Jacobians.Dolbeault.CechModelGeometry
import Jacobians.Dolbeault.DiskAcyclicCore

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Jacobians.Montel

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

/-! ## The genuine-cover partition of unity (sum-to-one on ALL of `X`)

The outer opens `chartOpen (coverCenter a)` of `Montel`'s chart cover genuinely cover `X`, so — unlike a
`SharedChartCover` family — a subordinate smooth PoU summing to `1` on all of `X` exists.  We take the
closed sum-to-one locus `C := univ` (compact `X` is closed), so the closed-core PoU
`exists_smoothPartitionOfUnity_core` yields a genuine partition of unity over the whole surface. -/

/-- **The genuine chart cover covers `X`.**  `⋃ a, chartOpen (coverCenter a) = univ` — the inner
shrinkings already cover (`iUnion_innerShrunkChart_coverCenter_eq`) and `innerShrunkChart ⊆ chartOpen`. -/
theorem iUnion_chartOpen_coverCenter_eq :
    (⋃ a : Fin ((chartCover : Finset X).card), chartOpen (X := X) (coverCenter a)) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← iUnion_innerShrunkChart_coverCenter_eq (X := X)]
  exact Set.iUnion_mono (fun a => innerShrunkChart_subset_chartOpen (coverCenter a))

/-- **The genuine-cover smooth PoU exists (sum-to-one on all of `X`).**  A smooth partition of unity over
`𝓘(ℝ,ℂ)`, subordinate to the genuine cover `(chartOpen (coverCenter a))`, summing to `1` on ALL of `X`
(the closed sum-to-one locus is `univ`).  This is the genuine-cover globalization foundation the
single-chart `SharedChartCover` could not supply: there the family does not cover `X`, so a subordinate
PoU can only sum to `1` on a closed core `C ⊊ ⋃ Uᵢ`; here the cover covers, so `C = univ`. -/
theorem exists_genuineCoverPoU :
    ∃ ρ : SmoothPartitionOfUnity (Fin ((chartCover : Finset X).card)) 𝓘(ℝ, ℂ) X Set.univ,
      ρ.IsSubordinate (fun a => chartOpen (X := X) (coverCenter a)) := by
  apply exists_smoothPartitionOfUnity_core
    (fun a => ⟨chartOpen (X := X) (coverCenter a), chartOpen_isOpen (coverCenter a)⟩)
    isClosed_univ
  rw [Set.univ_subset_iff]
  exact iUnion_chartOpen_coverCenter_eq

/-- A fixed genuine-cover smooth PoU subordinate to `(chartOpen (coverCenter a))`, summing to `1` on all
of `X`. -/
noncomputable def genuineCoverPoU :
    SmoothPartitionOfUnity (Fin ((chartCover : Finset X).card)) 𝓘(ℝ, ℂ) X Set.univ :=
  (exists_genuineCoverPoU (X := X)).choose

/-- The genuine-cover PoU is subordinate to the cover `(chartOpen (coverCenter a))`
(`tsupport ρ_a ⊆ chartOpen (coverCenter a)`). -/
theorem genuineCoverPoU_subordinate :
    (genuineCoverPoU (X := X)).IsSubordinate (fun a => chartOpen (X := X) (coverCenter a)) :=
  (exists_genuineCoverPoU (X := X)).choose_spec

/-- **Sum-to-one EVERYWHERE.**  `∑ a, ρ_a x = 1` for every `x : X` (the genuine cover covers `X`, so the
sum-to-one locus is all of `X` — no closed-core restriction, unlike `SharedChartCover`). -/
theorem sum_genuineCoverPoU_eq_one (x : X) :
    ∑ a, (genuineCoverPoU (X := X)) a x = 1 :=
  smoothPartitionOfUnity_sum_eq_one_of_mem (genuineCoverPoU (X := X)) (Set.mem_univ x)

/-- The subordination, as a `tsupport` containment: `tsupport (ρ_a) ⊆ chartOpen (coverCenter a)`. -/
theorem genuineCoverPoU_tsupport_subset (a : Fin ((chartCover : Finset X).card)) :
    tsupport (genuineCoverPoU (X := X) a) ⊆ chartOpen (X := X) (coverCenter a) :=
  genuineCoverPoU_subordinate a

/-- Each PoU function `ρ_a` (real-valued, `X → ℝ`) is globally `C^∞` on `X` over `𝓘(ℝ,ℂ) → 𝓘(ℝ,ℝ)` —
the regularity the chart-read ∂̄ telescoping needs (`ρ_a` read in any chart is `ContDiffAt`, hence so is
its planar `∂̄(ofReal ∘ ρ_a)`).  Composing with `Complex.ofReal` gives the chart-read complex factor. -/
theorem contMDiff_genuineCoverPoU (a : Fin ((chartCover : Finset X).card)) :
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (⊤ : ℕ∞) (genuineCoverPoU (X := X) a) :=
  (genuineCoverPoU (X := X) a).contMDiff

end Jacobians.Dolbeault
