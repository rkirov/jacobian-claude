import Jacobians.Finiteness.SkyscraperLESBase
import Mathlib.Analysis.CStarAlgebra.Classes

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)


namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace FiniteCover

open FiniteFamily

/-- **The skyscraper long exact sequence from the explicit chart-disk hypotheses.** Given a
cover-set `U i ∋ P` whose `↥(U i)`-chart source covers all of `U i` (`hWsrc`), with `D` supported on
`U i` only at `P` (`hDsupp`) and a singleton star at `P` (`hstar`), the skyscraper LES
`SkyscraperLES 𝔘 D P` exists.

This is `CohomologicalRR.exists_skyscraperLES` with its genuine geometric prerequisites made
explicit: it runs `SkyscraperAssembly.skyscraperLES_of_chartDisk` (the snake/connecting map,
exactness, surjectivity, `H⁰(Q) ≅ ℂ`, `H¹(Q) = 0`). The two finiteness inputs are now discharged
with **no** hypothesis: `H¹` by `finiteDimensional_cechH1_general` and `H⁰(𝒪_{D+P})` by the
`finiteDimensional_globalSections` instance (Gap 1). -/
theorem exists_skyscraperLES_of_chartDisk (𝔘 : FiniteCover X) (D : Divisor X) (P : X) {i : 𝔘.ι}
    (hP : P ∈ 𝔘.U i)
    (hWsrc : ∀ Q : 𝔘.U i, Q ∈ (chartAt (H := ℂ) (⟨P, hP⟩ : 𝔘.U i)).source)
    (hDsupp : ∀ Q : 𝔘.U i, Q ≠ ⟨P, hP⟩ → D Q.1 = 0)
    (hstar : ∀ j, P ∈ 𝔘.U j → j = i) :
    Nonempty (SkyscraperLES 𝔘 D P) :=
  ⟨𝔘.skyscraperLES_of_chartDisk D P hP hWsrc hDsupp hstar⟩

end FiniteCover

end Jacobians.Dolbeault
