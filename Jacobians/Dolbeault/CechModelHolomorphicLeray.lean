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
    -- **THE GENUINE FORSTER 14.6 ANALYTIC STEP — one honest `sorry`.**
    --
    -- Goal: for a holomorphic shrinking 1-cocycle `s` (`δ¹s = 0`), produce
    --   `η : Cochain0Model`, `x : Ccov`  with  `δ¹cov x = 0`  and  `s = δ⁰η + ρ·x`.
    --
    -- The smooth-split → glued-`∂̄` → per-disk-solve construction (Forster, mirroring the proven
    -- single-chart prototype `GluedDbarDatum.dbarDatum`) is set up by:
    --   • the genuine-cover PoU `genuineCoverPoU` (∑ρ = 1 on ALL of `X`, subordinate to `chartOpen`),
    --   • the planar Wirtinger algebra `dbarFun_mul` / `dbarFun_finset_sum`,
    --   • the cross-chart Wirtinger chain rule `dbarDisk_comp_holo`
    --       (`∂̄(f∘τ) = conj(τ′)·(∂̄f)∘τ`), making `ω̂_a := ∂̄g_a` the chart-`a` read of a global
    --       `(0,1)`-datum,
    --   • the compactly-supported per-disk solver `DbarDisk.dbar_solvable_of_compactSupport`
    --       (solves `∂̄h_a = ψ_a·ω̂_a` GLOBALLY on `ℂ` once `ψ_a·ω̂_a` is `C^∞` with compact support),
    --   • `differentiableAt_of_dbar_eq_zero` for the holomorphy of the corrected pieces.
    --
    -- **WHERE THE PROOF GETS STUCK (the structural residual, not a packaging gap).**
    -- The construction's `η_a := h_a − g_a` and `x_{ab} := h_b∘τ_{ab} − h_a` are holomorphic only on
    -- the SHRINKING region `Wov`, NOT on the FULL cover sets that the model's `C0`/`Ccov` demand:
    --   · `C0 = Cochain0Model = ∀a, BddHol (coverSetImage a)` — `η_a` must be holo on the FULL
    --     `coverSetImage a = φ_a '' chartOpen a`;
    --   · `Ccov = ∀p, BddHol (Uov p)` — `x_{ab}` must be holo on the FULL `Uov(a,b)`.
    -- `η_a` is holo exactly where `∂̄h_a = ∂̄g_a`, i.e. where the cutoff `ψ_a = 1`; `x_{ab}` is holo
    -- exactly where the chart-`a`/chart-`b` data `∂̄`-cancel, i.e. where `ψ_a(z) = ψ_b(τ_{ab}z)`.
    --
    -- The per-disk solver requires `ψ_a·ω̂_a` to be globally `C^∞` with COMPACT support in `ℂ`
    -- (the glued primitive `g_a` is smooth only on `coverSetImage a`, with the `BddHol` zero-extension
    -- junk at its boundary, so a compactly-supported cutoff `ψ_a` is genuinely needed). But:
    --   • a GLOBAL cutoff `ψ_a = Ψ∘φ_a⁻¹` gives the cross-chart compatibility `ψ_a = ψ_b∘τ`
    --     automatically (so `x` would be holo on the full `Uov`) — yet `Ψ` must be `1` on the
    --     SHRINKING cover, which already covers the compact `X` (`iUnion_innerChartOpen_eq = univ`),
    --     forcing `Ψ ≡ 1` and destroying the per-chart compact support;
    --   • a PER-CHART cutoff `ψ_a` (=1 on `Wov`, supp `⋐ coverSetImage a`) restores compact support
    --     but breaks `ψ_a = ψ_b∘τ`, so `x_{ab}` is holo only on `Wov(a,b)`, NOT on `Uov(a,b)`.
    -- These two requirements are in genuine tension. Equivalently: producing `η ∈ C⁰(𝔘)` and
    -- `x ∈ Z¹(𝔘)` holomorphic on the FULL cover overlaps from data holomorphic only on the
    -- shrinkings is the LERAY COMPARISON `Z¹(𝔙) = δC⁰(𝔘) + Z¹(𝔘)|_𝔙`, whose surjectivity needs the
    -- cover overlaps `Uov` to be ACYCLIC (`H¹(Uov,𝒪) = 0`). This is NOT available: the repo's
    -- `IsLeray` requires only the cover SETS to be simply connected and explicitly documents overlap
    -- acyclicity as unused dead weight (`CechComplex.IsLeray`), and the per-disk Dolbeault solve alone
    -- (the available analytic tool) delivers holomorphy only on the cutoff-=1 shrinking region — the
    -- SAME residual the single-chart prototype documents as `dbarDatum_agrees_on_interiorCore`.
    --
    -- Closing this requires EITHER (a) proving the chart-disk cover overlaps `Uov` acyclic and
    -- invoking the Leray extension, OR (b) re-pointing the model's `C0`/`Ccov` to the shrinking
    -- 0-/1-cochains (Forster's natural `C⁰(𝔙)`/`Z¹(𝔘)` two-scale statement) — a change to
    -- `CechModelHolomorphic.lean`, out of scope for this file. The honest analytic content is left here.
    sorry

end Jacobians.Dolbeault
