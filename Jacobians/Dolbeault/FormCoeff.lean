/-
  The canonical-chart coefficient of a holomorphic 1-form, and the local residue of `ω·g`
  (Forster §17 building block, on the EASY-half / injectivity path of the D=0 Serre pairing).

  A holomorphic 1-form `α`, in the canonical chart `chartAt ℂ a`, reads `α = coeffAt α a (z) · dz`
  with `coeffAt α a` **analytic** — this is exactly `Montel.localRep` + its analyticity bridge
  `localRep_analyticOn_chartTarget` (already proven sorry-free in the Montel development, so we reuse
  it rather than re-deriving the ω-smoothness ⟹ ℂ-analyticity manifold argument).

  On top of it we define the **local residue** `formFnResidue α g a` = the residue at `a` of the
  meromorphic 1-form `α·g` (holomorphic form times a function `g`), computed in the canonical chart,
  and prove it vanishes when `g`'s chart-pullback is holomorphic at `a` (so `α·g` has no pole there).
  Computing in the canonical chart is the trick (see `docs/hodge_bridge_research.md` build log) that
  makes Forster's cover-independence of `Res_a` follow from `Res(holo)=0` alone, sidestepping the
  chart-independence change-of-variables lemma.

  Everything here is sorry-free and depends on no sorry-backed lemma.
-/
import Jacobians.Montel.Compactness
import Jacobians.Genus
import Jacobians.Dolbeault.Residue

open scoped Manifold ContDiff Topology
open Complex Metric

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The coefficient of a holomorphic 1-form `α` read in the **canonical chart** at `a`: near `a`,
`α = coeffAt α a (z) · dz` in the coordinate `z = chartAt ℂ a`.  It is `Montel.localRep α a`
transported to the chart target; analytic by `coeffAt_analyticOn`. -/
noncomputable def coeffAt (α : HolomorphicOneForms X) (a : X) : ℂ → ℂ :=
  fun z => Jacobians.Montel.localRep α a ((chartAt ℂ a).symm z)

/-- `coeffAt α a` is analytic on the chart target (reuse of the Montel analyticity bridge). -/
theorem coeffAt_analyticOn (α : HolomorphicOneForms X) (a : X) :
    AnalyticOn ℂ (coeffAt α a) (chartAt ℂ a).target :=
  Jacobians.Montel.localRep_analyticOn_chartTarget α a

/-- `coeffAt α a` is analytic at the chart image of any point of the chart source. -/
theorem coeffAt_analyticAt (α : HolomorphicOneForms X) (a : X) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    AnalyticAt ℂ (coeffAt α a) z :=
  (coeffAt_analyticOn α a).analyticAt ((chartAt ℂ a).open_target.mem_nhds hz)

/-- The residue at `a` of the meromorphic 1-form `α·g` (a holomorphic form `α` times a function
`g : X → ℂ`), computed in the canonical chart: there `α·g = (coeffAt α a · (g ∘ chart.symm)) · dz`,
so the residue is `resAt` of that coefficient at the chart image of `a`. -/
noncomputable def formFnResidue (α : HolomorphicOneForms X) (g : X → ℂ) (a : X) : ℂ :=
  resAt (fun z => coeffAt α a z * g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)

/-- **`Res(holo) = 0`.**  If `g`'s chart-pullback is holomorphic at `a` (so `α·g` is holomorphic at
`a`, no pole), the local residue vanishes. -/
theorem formFnResidue_eq_zero_of_analyticAt (α : HolomorphicOneForms X) (g : X → ℂ) (a : X)
    (hg : AnalyticAt ℂ (fun z => g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a)) :
    formFnResidue α g a = 0 := by
  have hmem : (chartAt ℂ a) a ∈ (chartAt ℂ a).target := (chartAt ℂ a).map_source (mem_chart_source ℂ a)
  -- the integrand is analytic at the chart image of `a`
  have hprod : AnalyticAt ℂ (fun z => coeffAt α a z * g ((chartAt ℂ a).symm z)) ((chartAt ℂ a) a) :=
    (coeffAt_analyticAt α a hmem).mul hg
  -- analytic at a point ⟹ holomorphic on a small ball ⟹ residue 0
  obtain ⟨ρ, hρ, hball⟩ : ∃ ρ > 0, ∀ z ∈ ball ((chartAt ℂ a) a) ρ,
      DifferentiableAt ℂ (fun z => coeffAt α a z * g ((chartAt ℂ a).symm z)) z := by
    have hev := hprod.eventually_analyticAt
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hball⟩ := hev
    exact ⟨ε, hε, fun z hz => (hball (mem_ball.mp hz)).differentiableAt⟩
  exact resAt_eq_zero_of_differentiableOn_ball hρ hball

end Jacobians.Dolbeault
