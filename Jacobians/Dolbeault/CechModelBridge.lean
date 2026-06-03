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

end BddHol

end Jacobians.Dolbeault
