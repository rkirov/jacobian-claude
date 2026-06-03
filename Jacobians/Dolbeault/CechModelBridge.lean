/-
  Čech finiteness — the germ ↔ sup-norm comparison ("K-bridge"), upstream atoms.

  Part of discharging the single remaining finiteness sorry `exists_cechModel` (Forster 14.9); see the
  decomposition in `docs/cech_finiteness_research.md`. The comparison `cechH1 𝔘 D ≃ supH1` translates
  germ-class `𝒪_D` cochains (the `cechH1` representation) into `BddHol` cochains on chart-images (the
  `supH1`/Montel representation). Its most upstream atom is the **codomain constructor**: every analytic
  bounded function on an open `U ⊆ ℂ` is a `BddHol U` element.

  This file is pure one-variable complex analysis on the `BddHol` side — sorry-free, depends on no
  sorry-backed lemma. The manifold side (chart-pullback of an `𝒪_D` section is analytic) reuses the
  axiom-clean `CechH0.analyticAt_chart_change`.
-/
import Jacobians.Dolbeault.BddHol

open Metric Topology

namespace Jacobians.Dolbeault

namespace BddHol

variable {U : Set ℂ}

/-- **The `BddHol` codomain constructor (most-upstream K-bridge atom).**  An analytic, bounded function
on an open `U ⊆ ℂ` gives a `BddHol U` element, via the canonical extend-by-zero normal form off `U`
(which `BddHolCarrier` requires and which changes nothing on `U`). -/
noncomputable def ofAnalyticOn (g : ℂ → ℂ) (ha : AnalyticOn ℂ g U)
    (hb : ∃ C, ∀ z ∈ U, ‖g z‖ ≤ C) : BddHol U :=
  ⟨Set.indicator U g, by
    refine ⟨?_, ?_, ?_⟩
    · exact ha.congr (fun z hz => Set.indicator_of_mem hz g)
    · intro z hz
      exact Set.indicator_of_notMem hz g
    · obtain ⟨C, hC⟩ := hb
      refine ⟨C, fun z hz => ?_⟩
      rw [Set.indicator_of_mem hz g]
      exact hC z hz⟩

@[simp] theorem ofAnalyticOn_toFun_of_mem (g : ℂ → ℂ) (ha : AnalyticOn ℂ g U)
    (hb : ∃ C, ∀ z ∈ U, ‖g z‖ ≤ C) {z : ℂ} (hz : z ∈ U) :
    (ofAnalyticOn g ha hb).toFun z = g z :=
  Set.indicator_of_mem hz g

theorem ofAnalyticOn_toFun_eqOn (g : ℂ → ℂ) (ha : AnalyticOn ℂ g U)
    (hb : ∃ C, ∀ z ∈ U, ‖g z‖ ≤ C) :
    Set.EqOn (ofAnalyticOn g ha hb).toFun g U :=
  fun _ hz => ofAnalyticOn_toFun_of_mem g ha hb hz

/-- **Boundedness on a relatively-compact piece.**  An analytic function on `U` is bounded on any
compact `K ⊆ U` (it is continuous, hence bounded on the compact).  This supplies the `BddHol`
boundedness hypothesis: a cochain holomorphic on a cover-open is bounded on the (relatively-compact)
shrinking. -/
theorem bddOn_of_analyticOn_subset_compact {g : ℂ → ℂ} {U K : Set ℂ}
    (hg : AnalyticOn ℂ g U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, ∀ z ∈ K, ‖g z‖ ≤ C :=
  hK.exists_bound_of_continuousOn (hg.continuousOn.mono hKU)

/-- **The practical K-bridge constructor.**  A function analytic on an open `U`, restricted to an
open `U'` whose closure is a compact subset of `U` (`U' ⋐ U`), is a `BddHol U'` element — the
boundedness is automatic on the relatively-compact piece.  This is the shape the germ→`BddHol` cochain
map uses: cover-cochains are holomorphic on the cover-open `U`, the model lives on the shrinking
`U' ⋐ U`. -/
noncomputable def ofAnalyticOnOfRelCompact {g : ℂ → ℂ} {U U' : Set ℂ} (hg : AnalyticOn ℂ g U)
    (hsub : closure U' ⊆ U) (hcpt : IsCompact (closure U')) : BddHol U' :=
  ofAnalyticOn g (hg.mono (subset_closure.trans hsub))
    (by
      obtain ⟨C, hC⟩ := bddOn_of_analyticOn_subset_compact hg hcpt hsub
      exact ⟨C, fun z hz => hC z (subset_closure hz)⟩)

@[simp] theorem ofAnalyticOnOfRelCompact_toFun_of_mem {g : ℂ → ℂ} {U U' : Set ℂ}
    (hg : AnalyticOn ℂ g U) (hsub : closure U' ⊆ U) (hcpt : IsCompact (closure U'))
    {z : ℂ} (hz : z ∈ U') :
    (ofAnalyticOnOfRelCompact hg hsub hcpt).toFun z = g z :=
  ofAnalyticOn_toFun_of_mem g _ _ hz

end BddHol

/-! ### Non-convex restriction compactness — Step 1: finite convex-disk cover

Toward generalizing `BddHol.isCompactOperator_restrictCLM` to a non-convex compact `K` (needed so a
`DiskOverlapData` can use chart-images of overlaps, which are not convex across charts).  Step 1: any
compact `K ⊆ U` (open) is covered by finitely many *closed balls* (convex compact) each `⊆ U`. -/

/-- **Finite convex-disk cover.**  For `K` compact inside an open `U ⊆ ℂ`, there is a finite family of
closed balls — centred on `K`, each contained in `U` (hence convex compact `⊆ U`) — whose open cores
cover `K`. -/
theorem exists_finite_closedBall_cover {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ (t : Finset K) (r : K → ℝ), (∀ z : K, 0 < r z) ∧
      (∀ z : K, Metric.closedBall (z : ℂ) (r z) ⊆ U) ∧
      K ⊆ ⋃ z ∈ t, Metric.ball (z : ℂ) (r z) := by
  have hr : ∀ z : K, ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (z : ℂ) ρ ⊆ U := by
    intro z
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU z.2))
    exact ⟨ε / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hball⟩
  choose r hr_pos hr_sub using hr
  have hcover : K ⊆ ⋃ z : K, Metric.ball (z : ℂ) (r z) := fun x hx =>
    Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr_pos ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => Metric.ball (z : ℂ) (r z))
    (fun _ => Metric.isOpen_ball) hcover
  exact ⟨t, r, hr_pos, hr_sub, ht⟩

end Jacobians.Dolbeault
