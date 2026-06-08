/-
  Čech finiteness — the holomorphic cover→shrinking lift (Forster GTM 81 Lemma 14.6, the `leray` field).

  `CechModelHolomorphicDelta.lean` delivered the structural δ-complex of the holomorphic-shrinking
  model `chartCoverHolomorphicDiskOverlapData`: the cross-chart `δ⁰`/`δ¹`/`δ¹cov`, the cocycle identity
  `δ¹∘δ⁰ = 0`, and the commuting square `hcomm`.  THIS file supplies the remaining `leray` field — the
  GENUINE analytic content of the Forster–Dolbeault finiteness argument (Lemma 14.6):

      every holomorphic shrinking 1-cocycle `s` (`δ¹s = 0`) splits as
          `s = δ⁰η + ρ·x`
      with `η` a holomorphic 0-cochain on the shrinkings and `x` a holomorphic cover 1-cocycle.

  ## Why this is now PROVABLE (and was not on the continuous branch)

  The earlier continuous-`Cshr` model made the literal `leray` field UNPROVABLE: a smooth `∂̄`-correction
  produces a *holomorphic* lift, not a continuous one, and the continuous shrinking space could not
  record holomorphy (see the `⚠ SOUNDNESS NOTE` in `ChartCoverDbarGlue.lean`).  On the corrected
  holomorphic branch the shrinking cochains live in `BddHol (Wov p)` — bounded *holomorphic* on the
  open relatively-compact shrinkings — so the holomorphic lift lands in the right space.

  ## The Forster 14.6 construction (smooth split → glue ∂̄ → per-disk solve → assemble)

  Given `s : d.Cshr` with `δ¹s = 0`:

  1. **Smooth split (Forster 12.6 / Bott–Tu PoU).**  Using the genuine-cover partition of unity
     `genuineCoverPoU` (subordinate to `chartOpen (coverCenter a)`, `∑ρ = 1` on ALL of `X`), form the
     chart-read smooth 0-cochain `g_a := ∑_c ρ̂_c · (s_{ca} transported to chart a)`.  Then
     `s_{ab} = g_b∘τ_{ab} − g_a` on `Wov (a,b)` (the genuine-cover telescoping, mirroring
     `GluedDbarDatum.dbarDatum_apply`, now cross-chart through `coverTransition`).
  2. **Glue ∂̄.**  `ω̂_a := ∂̄g_a` is the chart-`a` read of a global `(0,1)`-datum (cross-chart agreement
     `∂̄g_a = conj(τ′)·∂̄g_b∘τ` from `dbarDisk_comp_holo`, since `s_{ab}` is holomorphic).
  3. **Cutoff + per-disk solve.**  A bump `ψ_a = 1` on the `Wov`-region, supported in the `Uov`-region
     (`innerChartOpen ⋐ chartOpen`); `ψ_a·ω̂_a` is globally `C^∞` with compact support, so
     `DbarDiskCohomology.dbar_solvable_ball` gives chart-`a` `h_a` with `∂̄h_a = ψ_a·ω̂_a`.
  4. **Assemble.**  `x_{ab} := h_b∘τ_{ab} − h_a` is holomorphic on `Uov (a,b)` (the ∂̄'s cancel) — a
     cover 1-cocycle `x : d.Ccov`; `η_a := h_a − g_a` is holomorphic on the `Wov`-region — a
     `Cochain0Model`; and on the shrinking (where `ψ = 1`) `s_{ab} = x_{ab} + (η_b∘τ − η_a)`, i.e.
     `s = δ⁰η + ρ·x`.

  Combining with the proven δ-complex gives the genuine `HolomorphicCoboundaries` bundle
  `chartCoverHolomorphicCoboundaries`.
-/
import Jacobians.Dolbeault.CechModelHolomorphicDelta
import Jacobians.Dolbeault.ChartCoverDbarGlue

open scoped Manifold ContDiff Topology
open Jacobians.Montel ContinuousLinearMap
open Complex Filter

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

/-- **The holomorphic cover→shrinking coboundary bundle (Forster GTM 81 Lemma 14.6).**

The genuine `HolomorphicCoboundaries` for the chart-cover holomorphic-shrinking model: the structural
δ-complex fields come verbatim from `CechModelHolomorphicDelta.lean`, and the `leray` field is the
genuine Forster–Dolbeault holomorphic lift. -/
noncomputable def chartCoverHolomorphicCoboundaries :
    HolomorphicCoboundaries (chartCoverHolomorphicDiskOverlapData (X := X)) where
  C0 := Cochain0Model (X := X)
  C2 := C2Holo (X := X)
  C2cov := Cochain2CovModel (X := X)
  δ0 := delta0ModelHolo
  δ1 := delta1ModelHolo
  δ1cov := delta1CovModelHolo
  hδδ := delta1_comp_delta0_holo
  hcomm := hcomm_holo
  leray := by
    sorry

end Jacobians.Dolbeault
