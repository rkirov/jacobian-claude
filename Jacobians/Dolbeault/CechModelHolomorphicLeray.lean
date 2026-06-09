/-
  Čech finiteness — the holomorphic cover→shrinking lift (Forster GTM 81 Lemma 14.6, the `leray` field).

  `CechModelHolomorphicDelta.lean` delivered the structural δ-complex of the holomorphic-shrinking
  model `chartCoverHolomorphicDiskOverlapData` (the cross-chart `δ⁰`/`δ¹`/`δ¹cov`, `δ²=0`, `hcomm`).
  `CechModelHolomorphicLerayShrink.lean` then RE-POINTED the 0-cochain scale from the cover scale
  (`coverSetImage`) down to the SHRINKING scale (`innerChartImage`) — Forster's natural two-scale
  `C⁰(𝔙)` / `Z¹(𝔘)` statement — and re-proved `δ²=0` there (`delta1_comp_delta0_holoShrink`).  THIS
  file assembles the genuine `HolomorphicCoboundaries` bundle `chartCoverHolomorphicCoboundaries` with
  the corrected `C0 := Cochain0ModelHolo` / `δ0 := delta0ModelHoloShrink`, and supplies the SHRINKING-
  level partition of unity `shrinkCoverPoU` (sum-to-one on ALL of `X`, subordinate to `innerChartOpen`)
  that the Forster 14.6 lift consumes.

  ## The Forster 14.6 construction and the residual analytic obstruction

  Given a holomorphic SHRINKING 1-cocycle `s` (`δ¹s = 0`):

  1. **Smooth split** via `shrinkCoverPoU`: chart-read `g_a := ∑_c ρ̂_c · (s_{ca} transported to chart
     a)` on `innerChartImage a`; the genuine-cover telescoping (`∑ρ = 1` on `X`, the cocycle relation)
     gives `g_b∘τ_{ab} − g_a = s_{ab}` on `Wov (a,b)`.
  2. **Glue ∂̄**: `ω̂_a := ∂̄g_a` on `innerChartImage a`.  Since `g_b∘τ − g_a = s_{ab}` is HOLOMORPHIC,
     the cross-chart Wirtinger chain rule `dbarDisk_comp_holo` gives `ω̂_a = conj(τ_{ab}′)·ω̂_b∘τ_{ab}`
     — i.e. `(ω̂_a)` is the chart-`a` read of a global `(0,1)`-FORM on `X` (NOT a global scalar
     function on `ℂ`: the `conj(τ′)` frame factor is the obstruction to gluing into one `ℂ→ℂ` map).
  3. **Per-chart `∂̄`-solve**: solve `∂̄h_a = ω̂_a` on `innerChartImage a`.
  4. **Assemble**: `x_{ab} := h_b∘τ_{ab} − h_a` is holomorphic where `∂̄h_a = ω̂_a = conj(τ′)·ω̂_b∘τ =
     ∂̄(h_b∘τ)`; `η_a := h_a − g_a` is holomorphic where `∂̄h_a = ∂̄g_a`.  On the shrinking `Wov`,
     `s = δ⁰η + ρ·x`.

  ## ⚠ Where step 3 fails with the available engines (the HONEST residual)

  The model demands `η ∈ Cochain0ModelHolo` holomorphic on the SHRINKING image `innerChartImage a` and
  `x ∈ d.Ccov` holomorphic on the FULL cover overlap `Uov (a,b)`.  The only planar `∂̄`-solver in the
  repo, `DbarDiskCohomology.dbar_solvable_ball`, solves on a BALL for a GLOBALLY-smooth datum.  Two
  routes, both blocked:

  * **Per-chart cutoff route** (the route the attack plan flags for 14.6).  Take `ψ_a = 1` on
    `innerChartImage a`, compactly supported in `coverSetImage a` (exists: `innerChartImage a ⋐
    coverSetImage a`).  Then `ψ_a·ω̂_a` is globally smooth with COMPACT support, hence inside some
    ball, so `dbar_solvable_ball` gives `h_a` with `∂̄h_a = ψ_a·ω̂_a`.  This makes `η_a = h_a − g_a`
    holomorphic on ALL of `innerChartImage a` (where `ψ_a = 1`) — `η ∈ Cochain0ModelHolo` ✓.  BUT
    `x_{ab} = h_b∘τ − h_a` is then holomorphic only where `ψ_a = 1` AND `ψ_b∘τ = 1`, i.e. on
    `innerChartImage a ∩ τ⁻¹(innerChartImage b) = Wov (a,b)` — NOT on the larger `Uov (a,b)` that
    `d.Ccov = ∀p, BddHol (Uov p)` requires.  A GLOBAL cutoff `Ψ` (giving `ψ_a = ψ_b∘τ`, hence `x` holo
    on `Uov`) cannot be compactly supported: the shrinkings already cover compact `X`
    (`iUnion_innerChartOpen_chartCover_eq`), forcing `Ψ ≡ 1`.  Genuine tension.

  * **No-cutoff route** (the naive "global ω" construction).  It would need `∂̄h_a = ω̂_a` solved on
    the whole open `innerChartImage a` (an ARBITRARY open subset of `ℂ`, NOT a ball — the Montel
    `chartCover` charts are generic chart sources, never coordinate disks).  That is `∂̄`-solvability
    on an arbitrary planar open set (Behnke–Stein / every planar domain is Stein), strictly stronger
    than the ball-solver `dbar_solvable_ball` and than the disk exhaustion
    `DbarOpenDisk.dbar_solvable_open_disk` — NOT available in the repo.  And the per-chart `ω̂_a` do
    NOT glue to a single `ℂ→ℂ` datum (the `conj(τ′)` frame factor), so a single global ball-solve does
    not apply.

  Equivalently: producing `x ∈ Z¹(𝔘)` holomorphic on the FULL cover overlaps from data holomorphic
  only on the shrinkings is the LERAY COMPARISON `Z¹(𝔙) = δC⁰(𝔙) + Z¹(𝔘)|_𝔙`, whose surjectivity
  needs the cover overlaps `Uov` to be `𝒪`-ACYCLIC — false for the Montel cover (its overlaps are
  arbitrary planar opens, e.g. annuli with `H¹(𝒪) ≠ 0`).  Closing it requires EITHER planar
  `∂̄`-solvability on arbitrary opens, OR overlap acyclicity — neither available.  The honest analytic
  content (the scale-corrected δ-complex + the shrinking PoU) is delivered; the lift is left as ONE
  honest remaining gap.

  NOTE.  `chartCoverHolomorphicCoboundaries` is currently consumed by nothing on the critical path;
  the bundled `exists_cechModel` existential is dischargeable via the artificial single-point model
  (`CechModelArtificial`).  This file is the genuine-mathematics route to the same finiteness.
-/
import Jacobians.Dolbeault.CechModelHolomorphicLerayShrink
import Jacobians.Dolbeault.ChartCoverDbarGlue

open scoped Manifold ContDiff Topology
open Jacobians.Montel ContinuousLinearMap
open Complex Filter

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] [Nonempty X]

/-! ## The shrinking-level partition of unity (sum-to-one on ALL of `X`)

The INNER shrinkings `innerChartOpen (coverCenter a)` of `Montel`'s chart cover genuinely cover `X`
(`iUnion_innerChartOpen_chartCover_eq`), so a subordinate smooth PoU summing to `1` on all of `X`
exists — the shrinking-level analogue of `genuineCoverPoU`, and exactly the PoU the Forster 14.6 lift's
smooth split needs (subordinate to the SHRINKING cover, where the cocycle `s` is defined). -/

/-- **The inner shrinkings cover `X`.**  `⋃ a, innerChartOpen (coverCenter a) = univ` — the
`coverCenter`-indexed form of `Montel.iUnion_innerChartOpen_chartCover_eq` (through the `Fin`
enumeration `coverCenter`). -/
theorem iUnion_innerChartOpen_coverCenter_eq :
    (⋃ a : Fin ((chartCover : Finset X).card), innerChartOpen (X := X) (coverCenter a)) = Set.univ := by
  apply Set.eq_univ_of_univ_subset
  rw [← iUnion_innerChartOpen_chartCover_eq (X := X)]
  intro y hy
  simp only [Set.mem_iUnion, exists_prop] at hy ⊢
  obtain ⟨x, hxmem, hxy⟩ := hy
  refine ⟨(chartCover : Finset X).equivFin ⟨x, hxmem⟩, ?_⟩
  rwa [coverCenter, Equiv.symm_apply_apply]

/-- **The shrinking-level smooth PoU exists (sum-to-one on all of `X`).**  A smooth partition of unity
over `𝓘(ℝ,ℂ)`, subordinate to the inner shrinking cover `(innerChartOpen (coverCenter a))`, summing to
`1` on ALL of `X`.  Mirrors `exists_genuineCoverPoU` but with `innerChartOpen` in place of `chartOpen`
— this is THE shrinking-level fix the Forster 14.6 smooth split needs. -/
theorem exists_shrinkCoverPoU :
    ∃ ρ : SmoothPartitionOfUnity (Fin ((chartCover : Finset X).card)) 𝓘(ℝ, ℂ) X Set.univ,
      ρ.IsSubordinate (fun a => innerChartOpen (X := X) (coverCenter a)) := by
  apply exists_smoothPartitionOfUnity_core
    (fun a => ⟨innerChartOpen (X := X) (coverCenter a), innerChartOpen_isOpen (coverCenter a)⟩)
    isClosed_univ
  rw [Set.univ_subset_iff]
  exact iUnion_innerChartOpen_coverCenter_eq

/-- A fixed shrinking-level smooth PoU subordinate to `(innerChartOpen (coverCenter a))`, summing to
`1` on all of `X`. -/
noncomputable def shrinkCoverPoU :
    SmoothPartitionOfUnity (Fin ((chartCover : Finset X).card)) 𝓘(ℝ, ℂ) X Set.univ :=
  (exists_shrinkCoverPoU (X := X)).choose

/-- The shrinking-level PoU is subordinate to `(innerChartOpen (coverCenter a))`
(`tsupport ρ_a ⊆ innerChartOpen (coverCenter a)`). -/
theorem shrinkCoverPoU_subordinate :
    (shrinkCoverPoU (X := X)).IsSubordinate (fun a => innerChartOpen (X := X) (coverCenter a)) :=
  (exists_shrinkCoverPoU (X := X)).choose_spec

/-- **Sum-to-one EVERYWHERE.**  `∑ a, ρ_a x = 1` for every `x : X` (the inner shrinkings cover `X`, so
the sum-to-one locus is all of `X`). -/
theorem sum_shrinkCoverPoU_eq_one (x : X) :
    ∑ a, (shrinkCoverPoU (X := X)) a x = 1 :=
  smoothPartitionOfUnity_sum_eq_one_of_mem (shrinkCoverPoU (X := X)) (Set.mem_univ x)

/-- The subordination as a `tsupport` containment: `tsupport (ρ_a) ⊆ innerChartOpen (coverCenter a)`. -/
theorem shrinkCoverPoU_tsupport_subset (a : Fin ((chartCover : Finset X).card)) :
    tsupport (shrinkCoverPoU (X := X) a) ⊆ innerChartOpen (X := X) (coverCenter a) :=
  shrinkCoverPoU_subordinate a

/-! ## The holomorphic cover→shrinking coboundary bundle (corrected `C0`/`δ0`) -/

/-- **The holomorphic cover→shrinking coboundary bundle (Forster GTM 81 Lemma 14.6).**

The genuine `HolomorphicCoboundaries` for the chart-cover holomorphic-shrinking model, with the
0-cochains RE-POINTED to the shrinking scale (`C0 := Cochain0ModelHolo`, `δ0 :=
delta0ModelHoloShrink`).  The structural δ-complex fields come from `CechModelHolomorphicDelta` /
`CechModelHolomorphicLerayShrink`; the `leray` field is the genuine Forster–Dolbeault holomorphic lift.

⚠ The `leray` field is ONE remaining gap: see the module docstring for the precise residual analytic
obstruction (it needs `∂̄`-solvability on arbitrary planar opens, or `𝒪`-acyclicity of the Montel
cover overlaps — neither available with the repo's ball-only `∂̄`-solver). -/
noncomputable def chartCoverHolomorphicCoboundaries :
    HolomorphicCoboundaries (chartCoverHolomorphicDiskOverlapData (X := X)) where
  C0 := Cochain0ModelHolo (X := X)
  C2 := C2Holo (X := X)
  C2cov := Cochain2CovModel (X := X)
  δ0 := delta0ModelHoloShrink
  δ1 := delta1ModelHolo
  δ1cov := delta1CovModelHolo
  hδδ := delta1_comp_delta0_holoShrink
  hcomm := hcomm_holo
  leray := by
    -- **THE GENUINE FORSTER 14.6 ANALYTIC STEP — one remaining gap.**
    --
    -- Goal: for a holomorphic shrinking 1-cocycle `s` (`δ¹s = 0`), produce
    --   `η : Cochain0ModelHolo`, `x : Ccov`  with  `δ¹cov x = 0`  and  `s = δ⁰η + ρ·x`.
    --
    -- The smooth-split → glued-`∂̄` → per-chart-solve construction is set up by the shrinking-level
    -- PoU `shrinkCoverPoU` (∑ρ = 1 on ALL of X, subordinate to `innerChartOpen`), the planar Wirtinger
    -- algebra (`dbarFun_mul` / `dbarFun_finset_sum`), the cross-chart chain rule `dbarDisk_comp_holo`
    -- (`∂̄(f∘τ) = conj(τ′)·(∂̄f)∘τ`), and the ball solver `DbarDiskCohomology.dbar_solvable_ball`.
    --
    -- RESIDUAL OBSTRUCTION (documented in the module docstring, NOT a packaging gap).  The construction
    -- delivers `η_a` holomorphic on the SHRINKING image `innerChartImage a` (✓ now that `C0` is at the
    -- shrinking scale), but `x_{ab} = h_b∘τ − h_a` holomorphic only on `Wov (a,b)` — NOT on the FULL
    -- `Uov (a,b)` that `Ccov = ∀p, BddHol (Uov p)` demands.  Closing this needs EITHER `∂̄`-solvability
    -- on arbitrary planar opens (Behnke–Stein; the Montel chart images are NOT balls), OR `𝒪`-acyclic
    -- cover overlaps (false for the Montel cover) — neither available with the ball-only solver.
    sorry

end Jacobians.Dolbeault
