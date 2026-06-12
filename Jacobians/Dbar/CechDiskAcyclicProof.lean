import Jacobians.Dbar.HoloRep
import Jacobians.Dbar.DbarDisk

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)
open Complex Metric Filter

namespace Jacobians.Dolbeault

/-! ### §B.0 — the `∂̄` finite-sum crank (the engine of the PoU split)

`DbarDisk.dbar` is built from `fderiv ℝ`, so it distributes over a finite sum of real-differentiable
functions, by `HasFDerivAt.fun_sum`. This is the load-bearing bookkeeping for the partition-of-unity
assembly of the multi-set ball Čech split (it generalises the inline `add`/`sub` cases of `§1` to an
arbitrary `Finset`). -/

/-- `DbarDisk.dbar f` is `C^∞` when `f` is.  Proven WITHOUT stating `ContDiff (fderiv ℝ f)` — that
form needs `NormedAddCommGroup (ℂ →L[ℝ] ℂ)`, an instance broken by a diamond surfacing under
`CechDiskAcyclic`'s combined import (each constituent import resolves it; the combination does not).
We route through `ContDiff.contDiff_fderiv_apply`, whose statement codomain is `ℂ` (the evaluated
derivative), so the broken CLM-norm instance never appears in the goal. -/
theorem contDiff_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (DbarDisk.dbar f) := by
  have key : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℂ × ℂ => (fderiv ℝ f p.1) p.2) :=
    hf.contDiff_fderiv_apply (le_refl _)
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (fderiv ℝ f z) 1) :=
    key.comp (contDiff_id.prodMk contDiff_const)
  have hI : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => (fderiv ℝ f z) I) :=
    key.comp (contDiff_id.prodMk contDiff_const)
  have : DbarDisk.dbar f
      = fun z : ℂ => (2 : ℂ)⁻¹ * ((fderiv ℝ f z) 1 + I * (fderiv ℝ f z) I) := rfl
  rw [this]
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

/-- `∂̄` distributes over a finite sum, at a point where each summand is real-differentiable. -/
theorem dbar_fun_sum {ι : Type*} (t : Finset ι) (f : ι → ℂ → ℂ) {z : ℂ}
    (hf : ∀ i ∈ t, DifferentiableAt ℝ (f i) z) :
    DbarDisk.dbar (fun x => ∑ i ∈ t, f i x) z = ∑ i ∈ t, DbarDisk.dbar (f i) z := by
  -- Finset induction via the `add` case (avoids CLM-sum machinery, which trips the broken
  -- `ℂ →L[ℝ] ℂ`-norm instance under `CechDiskAcyclic`'s combined import).
  classical
  induction t using Finset.induction with
  | empty => simp [DbarDisk.dbar]
  | insert a s ha ih =>
    have hfa : DifferentiableAt ℝ (f a) z := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, DifferentiableAt ℝ (f i) z :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum : DifferentiableAt ℝ (fun x => ∑ i ∈ s, f i x) z :=
      (HasFDerivAt.fun_sum fun i hi => (hfs i hi).hasFDerivAt).differentiableAt
    have hsplit : (fun x => ∑ i ∈ insert a s, f i x)
        = (fun x => f a x + ∑ i ∈ s, f i x) := by funext x; rw [Finset.sum_insert ha]
    have hadd : DbarDisk.dbar (fun x => f a x + ∑ i ∈ s, f i x) z
        = DbarDisk.dbar (f a) z + DbarDisk.dbar (fun x => ∑ i ∈ s, f i x) z :=
      dbarFun_add hfa hsum
    rw [hsplit, hadd, ih hfs, Finset.sum_insert ha]

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §B.1 — the analytic representative `holoFn` toolkit (now canonical in `HoloRep`)

The `holoRep`/`holoFn`/`gextLimRep_chart_analyticAt`/`toGerm_holoFn` limit-repair toolkit (a
holomorphic representative of an `OmegaDGerm 0` class, with the removable-singularity junk of `Gext`
discarded by a `limUnder`) was formerly RE-DERIVED here, duplicating `DolbeaultComparisonInverse`'s
copy. It now lives in the single canonical `Jacobians.Dolbeault.HoloRep` (imported above; built on
the light, comparison- free `CechH0`), shared by both files. §B.2 below
builds the chart-transport bridge on top of it. -/


/-! ### §B.2 — the chart-transport bridge proper (holomorphy ↔ chart-image ∂̄ = 0)

The holomorphy/∂̄ direction of the `↥W ↔ ℂ`-chart dictionary the repo lacked (it had ORDER only). -/

/-- The **chart-image holomorphic representative** of `g ∈ OmegaDGerm 0 W`, read in `X`'s chart at
`y`: the chart-pullback of the analytic representative `holoFn hg`.  An honest analytic `ℂ → ℂ`. -/
noncomputable def chartHoloRep {W : Opens X} {g : MGerm W}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) W) (y : X) : ℂ → ℂ :=
  holoFn hg ∘ (chartAt (H := ℂ) y).symm

/-- **Chart-transport bridge, holomorphy direction.**  The chart-image representative is
`AnalyticAt` (hence
`DifferentiableAt ℂ`) at the chart centre, for `y ∈ W`. -/
theorem chartHoloRep_analyticAt {W : Opens X} {g : MGerm W}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) W) {y : X} (hy : y ∈ W) :
    AnalyticAt ℂ (chartHoloRep hg y) ((chartAt (H := ℂ) y) y) :=
  holoFn_chart_analyticAt hg hy

/-- **Chart-transport bridge, ∂̄ direction.** The chart-image representative
satisfies `DbarDisk.dbar (chartHoloRep) = 0` at the chart centre (chart-read `ℂ`-analytic ⟹
`ℂ`-differentiable ⟹ Wirtinger `∂̄ = 0`). This is the holomorphy/∂̄ extension of `CechH0`'s
order-only chart bridge. -/
theorem chartHoloRep_dbar_eq_zero {W : Opens X} {g : MGerm W}
    (hg : g ∈ OmegaDGerm (0 : Divisor X) W) {y : X} (hy : y ∈ W) :
    DbarDisk.dbar (chartHoloRep hg y) ((chartAt (H := ℂ) y) y) = 0 :=
  DbarDisk.dbar_eq_zero_of_differentiableAt (chartHoloRep_analyticAt hg hy).differentiableAt

/-! ### §C — the function-level finite-cover ball Čech split (`H¹(ball, 𝒪) = 0` on functions)

The genuine analytic core: a Čech `1`-cocycle on a finite cover of a Euclidean ball `B ⊆ ℂ`,
presented as a family of *smooth* functions `h_i : ℂ → ℂ` whose pairwise differences `h_j − h_i` are
holomorphic on `B` (equivalently their `∂̄` agree there — the output of the partition-of-unity
globalization of the cocycle), splits *holomorphically*: there are holomorphic `η_i` on `B` with
`η_j − η_i = h_j − h_i`.

This is the `n`-set generalisation of `CechDiskAcyclic.ballSplit_two`
(`= dbar_holo_splitting_ball`). The genuine engine is the committed
`DbarDiskCohomology.dbar_solvable_ball`: solve `∂̄u = ∂̄h_{i₀}` on `B` for ONE index `i₀`, set
`η_i := h_i − u`; then `∂̄η_i = ∂̄h_i − ∂̄h_{i₀} = 0` (the agreeing-`∂̄` hypothesis), so each `η_i`
is holomorphic (`differentiableAt_of_dbar_eq_zero`), and the corrected differences are unchanged.
Sorry-free; the `dbar`-algebra (`§1 dbar_sub`) does the bookkeeping. -/

/-- **Function-level finite-cover ball Čech split (the `n`-set `H¹(ball, 𝒪) = 0`).**  Smooth
`h : ι → ℂ → ℂ` whose `∂̄`s all agree on `ball c r` (so all pairwise differences `h_j − h_i` are
holomorphic there — the Čech `1`-cocycle condition after PoU globalization) admit holomorphic
correctors `η : ι → ℂ → ℂ` on the ball with `η_j − η_i = h_j − h_i`. Generalises `ballSplit_two`
from `2` to `n` sets via a single `∂̄`-solve (`dbar_solvable_ball`). -/
theorem ballSplit_pou {ι : Type*} [Nonempty ι] (c : ℂ) {r : ℝ} (hr : 0 < r)
    (h : ι → ℂ → ℂ) (hsmooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i))
    (hdbar : ∀ i j, ∀ z ∈ ball c r, DbarDisk.dbar (h i) z = DbarDisk.dbar (h j) z) :
    ∃ η : ι → ℂ → ℂ, (∀ i, DifferentiableOn ℂ (η i) (ball c r)) ∧
      ∀ i j, ∀ z ∈ ball c r, h j z - h i z = η j z - η i z := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  -- Solve `∂̄u = ∂̄h_{i₀}` on the ball (`∂̄h_{i₀}` smooth ⟹ solvable, `dbar_solvable_ball`).
  obtain ⟨u, hu_smooth, hu_dbar⟩ :=
    DbarDiskCohomology.dbar_solvable_ball (contDiff_dbar (hsmooth i₀)) c hr
  refine ⟨fun i => h i - u, fun i z hz => ?_, fun i j z hz => ?_⟩
  · -- `η_i = h_i − u` holomorphic on the ball: `∂̄(h_i − u) = ∂̄h_i − ∂̄u = ∂̄h_i − ∂̄h_{i₀} = 0`.
    refine (DbarDiskCohomology.differentiableAt_of_dbar_eq_zero
      ((hsmooth i).sub hu_smooth) ?_).differentiableWithinAt
    have hsub : DbarDisk.dbar (fun x => h i x - u x) z
        = DbarDisk.dbar (h i) z - DbarDisk.dbar u z :=
      dbarFun_sub ((hsmooth i).differentiable (by norm_num) z)
        (hu_smooth.differentiable (by norm_num) z)
    rw [hsub, hu_dbar z hz, ← hdbar i i₀ z hz]; ring
  · -- The corrected difference is unchanged: `(h_j − u) − (h_i − u) = h_j − h_i`.
    show h j z - h i z = (h j z - u z) - (h i z - u z)
    ring

/-- **Function-level ball Čech split with a glued `∂̄`-datum** (the form the partition-of-unity
assembly actually produces). Smooth primitives `h_i` whose `∂̄` agrees on `ball ∩ Ω_i` with a SINGLE
global smooth function `ω` (the glued `∂̄`-datum `∂̄h_i`-on-`Ω_i`, well-defined because the `∂̄h_i`
agree on overlaps) admit holomorphic correctors `η_i = h_i − u` on `ball ∩ Ω_i`, where `∂̄u = ω`
(`dbar_solvable_ball`), with `η_j − η_i = h_j − h_i`. This is the directly-assembly-usable shape:
the remaining obligation is to BUILD `h_i` and the glued `ω` from the cocycle via PoU (OBSTRUCTION
3); the `∂̄`-solve and holomorphic correction are then exactly this lemma. -/
theorem ballSplit_glued {ι : Type*} (c : ℂ) {r : ℝ} (hr : 0 < r)
    (Ω : ι → Set ℂ) (h : ι → ℂ → ℂ) (hsmooth : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (h i))
    (dbarDatum : ℂ → ℂ) (hdatum : ContDiff ℝ (⊤ : ℕ∞) dbarDatum)
    (hagree : ∀ i, ∀ z ∈ ball c r ∩ Ω i, DbarDisk.dbar (h i) z = dbarDatum z) :
    ∃ η : ι → ℂ → ℂ, (∀ i, DifferentiableOn ℂ (η i) (ball c r ∩ Ω i)) ∧
      ∀ i j, ∀ z ∈ ball c r, h j z - h i z = η j z - η i z := by
  obtain ⟨u, hu_smooth, hu_dbar⟩ := DbarDiskCohomology.dbar_solvable_ball hdatum c hr
  refine ⟨fun i => h i - u, fun i z hz => ?_, fun i j z hz => ?_⟩
  · refine (DbarDiskCohomology.differentiableAt_of_dbar_eq_zero
      ((hsmooth i).sub hu_smooth) ?_).differentiableWithinAt
    have hsub : DbarDisk.dbar (fun x => h i x - u x) z
        = DbarDisk.dbar (h i) z - DbarDisk.dbar u z :=
      dbarFun_sub ((hsmooth i).differentiable (by norm_num) z)
        (hu_smooth.differentiable (by norm_num) z)
    rw [hsub, hu_dbar z hz.1, hagree i z hz]; ring
  · show h j z - h i z = (h j z - u z) - (h i z - u z)
    ring

end Jacobians.Dolbeault

/-! ## Toward `FunctionDiskAcyclic 𝔙 0`

Main results above:

  * **The chart-transport bridge.**  `chartHoloRep` / `chartHoloRep_analyticAt` /
    `chartHoloRep_dbar_eq_zero`: for `g ∈ OmegaDGerm 0 W`, the chart-image analytic representative
    is `AnalyticAt` and has `DbarDisk.dbar = 0` at the chart centre — the holomorphy/∂̄ direction
    of the `↥W ↔ ℂ`-chart dictionary previously available only for *order*
    (`CechH0.ordU_val_eq_orderW`).
  * **The function-level finite-cover ball Čech split** (`H¹(ball,𝒪)=0` on functions, `n`-set).
    `ballSplit_pou` and `ballSplit_glued`: an `n`-set smooth Čech splitting whose differences are
    holomorphic (resp. whose `∂̄` matches a glued datum `ω` on overlaps) is corrected to a
    holomorphic splitting by a single `∂̄`-solve (`DbarDiskCohomology.dbar_solvable_ball`).
  * `dbar_fun_sum` — `∂̄` distributes over a finite sum (the PoU `∂̄`-of-`∑` crank).
  * `contDiff_dbar` — `∂̄` preserves `C^∞`, routed through `ContDiff.contDiff_fderiv_apply` to
    dodge the `NormedAddCommGroup (ℂ →L[ℝ] ℂ)` instance that this file's combined import breaks (a
    diamond: each constituent import — `CechH0`, `DbarDiskCohomology`, `ChartDiskCover` — resolves
    the instance alone; only their union does not).

The remaining step — the partition-of-unity `C^∞`-globalization of the cocycle (the standard
Forster §15 argument: lift each overlap germ to `holoFn`, push through the shared chart, glue the
smooth primitives `h_i := ∑ᶠ q, ρ_q · g_{qi}`, and feed `ballSplit_glued`) — is carried out in
`CechDiskAcyclicAssembly`, yielding `FunctionDiskAcyclic 𝔙 0` and, via
`isDiskAcyclic_of_funcLevel` + `cechH1_subsingleton_of_isDiskAcyclic`, the germ-level
`H¹(disk, 𝒪) = 0`. -/
