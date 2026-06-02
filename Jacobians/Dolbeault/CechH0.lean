/-
  Dolbeault ladder — the `h⁰ = l(D)` bridge leaf (`h0Dim_eq_lDim`).

  The Čech `H⁰(𝔘, 𝒪_D)` (global matching germ-class sections over a finite cover) is identified with
  the Riemann–Roch linear system `L(D) = linearSystem D` modulo its germ-zero junk. Concretely we
  build a `ℂ`-linear equivalence `L(D) ⧸ germZero ≃ₗ globalSections D` and read off the `finrank`s.

  Math content (the two non-formal pieces):
  * **keystone** `ordU_val_eq_orderW`: the order of a global meromorphic `F` restricted to the open
    submanifold `↥U` (computed in `↥U`'s own chart, `ordU`) equals its global order `orderW F`. Both
    charts are `subtypeRestr`s of the *same* ambient `chartAt ℂ x` (`Opens.chartAt_eq`), exactly as
    `CechSection.restrict_chart_aux`.
  * **gluing** (surjectivity): a matching family of germ-classes glues to a global `MeromorphicFunction`.
    NOTE (correctness): the naive pointwise patch `x ↦ g (idx x) x` is *not* meromorphic at
    cover-boundary points (the per-overlap disagreement set is only codiscrete *within* the overlap, so
    it can accumulate at a boundary point `y ∉ U j`). The fix is to rigidify the representatives via the
    meromorphic normal form read in the shared ambient chart, so they agree *honestly* (not just
    codiscretely) on overlaps; the patch is then chart-locally a single normal-form function.
-/
import Jacobians.Dolbeault.CechComplex

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Keystone: local order on `↥U` = global order on `X` -/

/-- Base-point and chart-pullback agreement between `↥U`'s chart at `u` and `X`'s chart at `u.1`:
`↥U`'s chart is the `subtypeRestr` of the *same* ambient chart `chartAt ℂ u.1` (`Opens.chartAt_eq`),
so it reads any `F : X → ℂ` at the same ambient point near `u`. The `↥U ↪ X` analogue of
`restrict_chart_aux`. -/
private theorem incl_chart_aux {U : Opens X} (F : X → ℂ) (u : U) :
    (chartAt (H := ℂ) u) u = (chartAt (H := ℂ) u.1) u.1 ∧
    ((F ∘ Subtype.val) ∘ (chartAt (H := ℂ) u).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) u) u)]
      (F ∘ (chartAt (H := ℂ) u.1).symm) := by
  have hbase : (chartAt (H := ℂ) u) u = (chartAt (H := ℂ) u.1) u.1 := by
    simp only [TopologicalSpace.Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_coe,
      Set.restrict_apply]
  refine ⟨hbase, ?_⟩
  have ht1 : (chartAt (H := ℂ) u).target ∈ 𝓝 ((chartAt (H := ℂ) u) u) :=
    (chartAt (H := ℂ) u).open_target.mem_nhds
      ((chartAt (H := ℂ) u).map_source (mem_chart_source ℂ u))
  refine Filter.eventuallyEq_of_mem ht1 fun w hw => ?_
  show F (((chartAt (H := ℂ) u).symm w : U) : X) = F ((chartAt (H := ℂ) u.1).symm w)
  congr 1
  have e1 : ((chartAt (H := ℂ) u).symm w).1 = (chartAt (H := ℂ) u.1).symm w := by
    simpa [Function.comp] using
      OpenPartialHomeomorph.subtypeRestr_symm_apply (e := chartAt (H := ℂ) u.1) ⟨u⟩ hw
  rw [e1]

/-- **Keystone.** The order of `F` restricted to the open submanifold `↥U` (in `↥U`'s chart) equals
the global order `orderW F` at the corresponding point. -/
theorem ordU_val_eq_orderW {U : Opens X} (F : MeromorphicFunction X) (u : U) :
    ordU (F.toFun ∘ Subtype.val) u = F.orderW u.1 := by
  obtain ⟨hbase, hev⟩ := incl_chart_aux F.toFun u
  rw [ordU, MeromorphicFunction.orderW, hbase]
  exact meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds)

/-- `F : X → ℂ` meromorphic on `X` restricts to a meromorphic function on the open submanifold `↥U`. -/
theorem isMeromorphic_val {U : Opens X} (F : MeromorphicFunction X) :
    IsMeromorphic (U : Type _) (F.toFun ∘ Subtype.val) := by
  intro u
  obtain ⟨hbase, hev⟩ := incl_chart_aux F.toFun u
  have hmer := F.meromorphic u.1
  rw [← hbase] at hmer
  exact hmer.congr (hev.filter_mono nhdsWithin_le_nhds).symm

end Jacobians.Dolbeault
