/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Jacobians.PeriodLattice
import Jacobians.Discharge.Manifold.ContMDiffOmegaAnalytic
import Jacobians.Montel.Compactness
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Analyticity skeleton for `ofCurve_contMDiff`

This file lays out the proof skeleton for `Jacobians.ofCurve_contMDiff`
(Forster §21: the Abel–Jacobi map is holomorphic, in the quotient
sense — see `Jacobians.exists_smoothPath_family` for why the
unquotiented version is mathematically false).

**Mathlib API used**
* `Mathlib.Analysis.Complex.HasPrimitives.DifferentiableOn.isExactOn_ball` —
  a holomorphic function on a ball has a primitive (Morera).
* `Mathlib.Analysis.Complex.CauchyIntegral.DifferentiableOn.analyticOn` —
  on an open set, `DifferentiableOn ℂ ⇒ AnalyticOn ℂ`.
* `Mathlib.Analysis.Calculus.ContDiff.Defs.AnalyticAt.contDiffAt` —
  in a complete codomain, `AnalyticAt ℂ ⇒ ContDiffAt ℂ n` for any `n`.

**Construction strategy**

For each `Q₀ : X`, in the chart `e := chartAt ℂ Q₀`, on the chart-ball
`B := e.target ∩ ball (e Q₀) r` for some `r > 0`, define the **local
lift**

```
Φ_{Q₀} : X → ℂ^g
Φ_{Q₀}(Q) := constant(Q₀) + ∫_{e Q₀}^{e Q} ω̃_i(w) dw    -- in chart coords
```

where `ω̃_i = (periodBasisForm i)` pulled back via `e.symm`, and the
integral is along the straight line in chart coordinates.

By Morera + Cauchy, this is locally analytic in `(e Q)`, hence
analytic-on-the-chart-pullback, hence `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ^g) ω`
at `Q₀`.

The local lifts agree with `ofCurve P` modulo the period lattice
(path-difference-is-closed-loop ⇒ lattice element). Local-to-global
smoothness in the **quotient** follows from `contMDiff_iff_forall_*`.

**Status of this file (2026-05-28)**

All theorems are sorry-bodied with detailed proof plans. The
architecture is sound — each sorry maps to one cleanly-statable
classical-content claim.
-/

open scoped Manifold ContDiff
open Complex Set
open MeasureTheory

namespace Jacobians.OfCurveSkeleton

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **Chart-pulled-back periodBasisForm at a chart-coord point.**

Given `Q₀ : X` with chart `e := chartAt ℂ Q₀`, and a chart-coordinate
`z ∈ e.target`, the chart-pulled-back periodBasisForm is the value of
the form's **local representative** (from `Jacobians.Montel.LocalRep`)
at the point `e.symm z`.

The local representative `localRep α x₀ y` evaluates `α.toFun y` at
the canonical tangent vector at `y` induced by the trivialization of
the tangent bundle at `x₀` (applied to the unit `1 : ℂ`). It is the
coefficient of `dz` in the chart-coord expression of `α`. -/
noncomputable def chartFormCoeff (Q₀ : X) (i : Fin (genus X)) (z : ℂ) : ℂ :=
  Jacobians.Montel.localRep (periodBasisForm X i) Q₀
    ((chartAt (H := ℂ) Q₀).symm z)

/-- **The chart-form coefficient is holomorphic on the chart target.**

PROVEN: direct corollary of `Jacobians.Montel.localRep_analyticOn_chartTarget`
(the existing chart-coord analyticity of `localRep`, proven via
`localRep_contMDiffOn` + `contDiffOn_omega_iff_analyticOn`). -/
theorem chartFormCoeff_differentiableOn (Q₀ : X) (i : Fin (genus X)) :
    DifferentiableOn ℂ (chartFormCoeff (X := X) Q₀ i)
      ((chartAt (H := ℂ) Q₀).target) :=
  (Jacobians.Montel.localRep_analyticOn_chartTarget
    (periodBasisForm X i) Q₀).differentiableOn

/-- **A holomorphic function on an open ball has an analytic primitive.**

Direct application of Mathlib's `DifferentiableOn.isExactOn_ball` +
`DifferentiableOn.analyticOn`. Mathlib defines `IsExactOn` as
existence of `g` with `HasDerivAt g (f z) z` for all `z` in the ball;
extracting `g` and showing its analyticity is the content here. -/
theorem exists_analytic_primitive_on_ball
    {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∃ g : ℂ → ℂ,
      (∀ z ∈ Metric.ball c r, HasDerivAt g (f z) z) ∧
      AnalyticOn ℂ g (Metric.ball c r) := by
  obtain ⟨g, hg⟩ := hf.isExactOn_ball
  refine ⟨g, hg, ?_⟩
  -- `g` is differentiable on the ball (each point has `HasDerivAt`).
  have hgdiff : DifferentiableOn ℂ g (Metric.ball c r) := by
    intro z hz
    exact (hg z hz).differentiableAt.differentiableWithinAt
  -- On an open set, `DifferentiableOn ℂ ⇒ AnalyticOn ℂ`.
  exact hgdiff.analyticOn Metric.isOpen_ball

/-- **FTC for a primitive along a straight-line segment in ℂ.**

If `g` is a primitive of `f` on a ball containing both `a` and `b`
(and the segment between them), then `∫_0^1 f(a + t(b-a)) (b-a) dt =
g(b) - g(a)`.

This is just the fundamental theorem of calculus applied to `s ↦
g(a + s(b - a))` whose derivative is `f(a + s(b - a)) (b - a)`. -/
theorem segmentIntegral_eq_primitive_diff
    {f g : ℂ → ℂ} {c : ℂ} {r : ℝ} {a b : ℂ}
    (_ha : a ∈ Metric.ball c r) (_hb : b ∈ Metric.ball c r)
    (hseg : Set.Icc (0 : ℝ) 1 ⊆ {t | a + (t : ℂ) * (b - a) ∈ Metric.ball c r})
    (hf_cont : ContinuousOn f (Metric.ball c r))
    (hg : ∀ z ∈ Metric.ball c r, HasDerivAt g (f z) z) :
    ∫ t in (0 : ℝ)..1, f (a + (t : ℂ) * (b - a)) * (b - a) =
      g b - g a := by
  -- The composed path `φ : ℝ → ℂ`, `φ t := a + t • (b - a)`,
  -- has `HasDerivAt φ (b - a) t` (real-linear, derivative = `b - a`).
  -- Then by complex chain rule (a `HasDerivAt` composition where the
  -- inner derivative is real and the outer is complex),
  -- `t ↦ g(φ t)` has derivative `f(φ t) * (b - a)` at each `t ∈ [0,1]`.
  set φ : ℝ → ℂ := fun t => a + (t : ℂ) * (b - a) with hφ_def
  have hφ : ∀ t : ℝ, HasDerivAt φ (b - a) t := by
    intro t
    -- Express φ in terms of `smul`, take derivative via `HasDerivAt.smul_const`,
    -- then rewrite back to the `(·) * (b - a)` form.
    have h_id : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h_smul : HasDerivAt (fun s : ℝ => s • (b - a)) ((1 : ℝ) • (b - a)) t :=
      h_id.smul_const (b - a)
    have h_eq : (fun s : ℝ => s • (b - a)) = (fun s : ℝ => (s : ℂ) * (b - a)) := by
      funext s; exact Complex.real_smul
    rw [h_eq] at h_smul
    -- Simplify `1 • (b - a)` to `b - a`.
    have h_one : ((1 : ℝ) • (b - a) : ℂ) = b - a := by
      rw [Complex.real_smul]; simp
    rw [h_one] at h_smul
    -- h_smul : HasDerivAt (fun s : ℝ => (s : ℂ) * (b - a)) (b - a) t
    have h_const : HasDerivAt (fun _ : ℝ => a) 0 t := hasDerivAt_const t a
    have h_add : HasDerivAt (fun s : ℝ => a + (s : ℂ) * (b - a)) (0 + (b - a)) t :=
      h_const.add h_smul
    rw [zero_add] at h_add
    exact h_add
  -- Composed derivative: `(g ∘ φ)' t = (b - a) * f (φ t)`.
  have h_comp : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s => g (φ s)) (f (φ t) * (b - a)) t := by
    intro t ht
    have hzt : φ t ∈ Metric.ball c r := hseg ht
    have hg_at : HasDerivAt g (f (φ t)) (φ t) := hg (φ t) hzt
    have := hg_at.comp t (hφ t)
    simpa [mul_comm] using this
  -- FTC: `∫ t in 0..1, (g ∘ φ)' t = g (φ 1) - g (φ 0)`.
  have h_endpoints : φ 0 = a ∧ φ 1 = b := by
    refine ⟨?_, ?_⟩ <;> simp [φ]
  -- The integrand `f (φ t) * (b - a)` is continuous on `[0, 1]`,
  -- hence integrable on it.
  have hφ_cont : Continuous φ := by
    have : Continuous (fun t : ℝ => (t : ℂ) * (b - a)) :=
      (Complex.continuous_ofReal).mul continuous_const
    exact continuous_const.add this
  have h_int_cont : ContinuousOn (fun t : ℝ => f (φ t) * (b - a))
      (Set.Icc (0 : ℝ) 1) := by
    refine (ContinuousOn.mul ?_ continuousOn_const)
    exact (hf_cont.comp hφ_cont.continuousOn (fun t ht => hseg ht))
  have h_int : IntervalIntegrable (fun t : ℝ => f (φ t) * (b - a))
      MeasureTheory.volume 0 1 :=
    (h_int_cont.intervalIntegrable_of_Icc (by norm_num : (0:ℝ) ≤ 1))
  -- Convert `Set.Icc` HasDerivAt statement to `uIcc` form.
  have h_comp' : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => g (φ s)) (f (φ t) * (b - a)) t := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact h_comp t ht
  -- Apply FTC.
  have h_FTC := intervalIntegral.integral_eq_sub_of_hasDerivAt h_comp' h_int
  rw [h_endpoints.1, h_endpoints.2] at h_FTC
  exact h_FTC

/-- **Local lift `Φ_{Q₀}` in chart coordinates.**

For chart coord `z ∈ e.target` (where `e = chartAt ℂ Q₀`), the local
lift of `ofCurve P` at `Q₀` is

```
Φ̃_{Q₀, i}(z) := constant_i + ∫_0^1 chartFormCoeff Q₀ i (z₀ + t (z - z₀)) * (z - z₀) dt
```

where `z₀ = e Q₀` and `constant_i := periodVec(some-fixed-path P → Q₀) i`.

For now, we only need that `Φ̃_{Q₀, i}` is `AnalyticAt ℂ` at `z₀`. -/
noncomputable def localLiftChart (Q₀ : X) (constants : Fin (genus X) → ℂ)
    (i : Fin (genus X)) (z : ℂ) : ℂ :=
  constants i +
    ∫ t in (0 : ℝ)..1,
      (chartFormCoeff (X := X) Q₀ i
        ((chartAt (H := ℂ) Q₀) Q₀ + (t : ℂ) * (z - (chartAt (H := ℂ) Q₀) Q₀))
       * (z - (chartAt (H := ℂ) Q₀) Q₀))

/-- **Local lift is analytic on a chart ball.**

Combines `exists_analytic_primitive_on_ball` (from `chartFormCoeff`'s
holomorphy) with `segmentIntegral_eq_primitive_diff` (rewriting the
straight-line integral as `g(z) - g(z₀)`).

The result `localLiftChart Q₀ constants i z = constants i + g(z) -
g(z₀)` is analytic in `z` because `g` is analytic.

Locally on the chart-ball `Metric.ball ((chartAt ℂ Q₀) Q₀) r`
contained in `e.target`. -/
theorem localLiftChart_analyticAt (Q₀ : X) (constants : Fin (genus X) → ℂ)
    (i : Fin (genus X)) :
    AnalyticAt ℂ (localLiftChart (X := X) Q₀ constants i)
      ((chartAt (H := ℂ) Q₀) Q₀) := by
  -- Step 1: pick a chart ball `Metric.ball z₀ r ⊆ chart.target`.
  set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀_def
  have h_open := (chartAt (H := ℂ) Q₀).open_target
  have h_src : Q₀ ∈ (chartAt (H := ℂ) Q₀).source := mem_chart_source ℂ Q₀
  have h_mem : z₀ ∈ (chartAt (H := ℂ) Q₀).target :=
    (chartAt (H := ℂ) Q₀).map_source h_src
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp h_open _ h_mem
  -- Step 2: `chartFormCoeff` is `DifferentiableOn` on this ball.
  have hdiff : DifferentiableOn ℂ (chartFormCoeff (X := X) Q₀ i)
      (Metric.ball z₀ r) :=
    (chartFormCoeff_differentiableOn Q₀ i).mono hr_subset
  -- Step 3: analytic primitive on the ball.
  obtain ⟨g, hg_deriv, hg_ana⟩ := exists_analytic_primitive_on_ball hdiff
  -- Step 4: continuity of `chartFormCoeff` on the ball (from
  -- `DifferentiableOn`).
  have hf_cont : ContinuousOn (chartFormCoeff (X := X) Q₀ i)
      (Metric.ball z₀ r) := hdiff.continuousOn
  -- Step 5: On `Metric.ball z₀ r`, the local lift equals
  -- `constants i + g z - g z₀`.
  have h_eq : Set.EqOn (localLiftChart (X := X) Q₀ constants i)
      (fun z => constants i + g z - g z₀) (Metric.ball z₀ r) := by
    intro z hz
    -- Apply `segmentIntegral_eq_primitive_diff` with `a = z₀`, `b = z`.
    -- Segment is contained in the ball (convexity).
    have hz₀_mem : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr_pos
    have hseg : Set.Icc (0 : ℝ) 1 ⊆
        {t | z₀ + (t : ℂ) * (z - z₀) ∈ Metric.ball z₀ r} := by
      intro t ht
      show z₀ + (t : ℂ) * (z - z₀) ∈ Metric.ball z₀ r
      have h_rewrite : z₀ + (t : ℂ) * (z - z₀) = z₀ + t • (z - z₀) := by
        rw [Complex.real_smul]
      rw [h_rewrite]
      exact (convex_ball z₀ r).add_smul_sub_mem hz₀_mem hz ht
    have := segmentIntegral_eq_primitive_diff (c := z₀) (r := r)
      (a := z₀) (b := z) (f := chartFormCoeff (X := X) Q₀ i) (g := g)
      hz₀_mem hz hseg hf_cont hg_deriv
    simp only [localLiftChart]
    rw [this]
    ring
  -- Step 6: `(fun z => constants i + g z - g z₀)` is `AnalyticAt` at z₀.
  -- It's `constants i - g z₀` (constant) plus `g` (analytic at z₀
  -- since z₀ is in the open ball).
  have hg_at : AnalyticAt ℂ g z₀ :=
    hg_ana.analyticAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))
  have h_target : AnalyticAt ℂ (fun z => constants i + g z - g z₀) z₀ := by
    have h1 : AnalyticAt ℂ (fun _ : ℂ => constants i) z₀ := analyticAt_const
    have h2 : AnalyticAt ℂ (fun _ : ℂ => g z₀) z₀ := analyticAt_const
    exact (h1.add hg_at).sub h2
  -- Step 7: AnalyticAt is local; conclude via `EventuallyEq`.
  have h_nhds : (fun z => constants i + g z - g z₀) =ᶠ[nhds z₀]
      localLiftChart (X := X) Q₀ constants i := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos)]
      with z hz using (h_eq hz).symm
  exact h_target.congr h_nhds

/-! ### Bridge: analyticAt of chart-coord lift ⇒ `ContMDiffAt` on the manifold

The vector-valued local lift, expressed as a function `X → (Fin (genus
X) → ℂ)`, is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω` at `Q₀`.

This is the analytic→ContMDiffAt bridge: from `AnalyticAt` of each
chart-coord component, we get `ContDiffAt ℂ ω` (Mathlib's
`AnalyticAt.contDiffAt`), bundle via `contDiffAt_pi`, then convert to
`ContMDiffAt` via the chart-pullback characterization. -/

/-- **Vector-valued local lift** at `Q₀`. -/
noncomputable def localLift (Q₀ : X) (constants : Fin (genus X) → ℂ)
    (Q : X) : Fin (genus X) → ℂ :=
  fun i => localLiftChart (X := X) Q₀ constants i ((chartAt (H := ℂ) Q₀) Q)

/-- **The chart-coord function** of the local lift, as a vector-valued
map `ℂ → (Fin (genus X) → ℂ)`. -/
noncomputable def localLiftChartVec (Q₀ : X) (constants : Fin (genus X) → ℂ)
    (z : ℂ) : Fin (genus X) → ℂ :=
  fun i => localLiftChart (X := X) Q₀ constants i z

/-- **The chart-coord vector lift is `AnalyticAt`** at the chart point. -/
theorem localLiftChartVec_analyticAt (Q₀ : X) (constants : Fin (genus X) → ℂ) :
    AnalyticAt ℂ (localLiftChartVec (X := X) Q₀ constants)
      ((chartAt (H := ℂ) Q₀) Q₀) := by
  -- Bundle the per-component analyticAt into a `Pi`-valued analyticAt.
  -- Mathlib: `analyticAt_pi` or similar — each component analytic implies
  -- the pi-bundled function is analytic.
  rw [show localLiftChartVec (X := X) Q₀ constants
      = (fun z i => localLiftChart (X := X) Q₀ constants i z) from rfl]
  exact AnalyticAt.pi fun i => localLiftChart_analyticAt Q₀ constants i

/-- **The chart-coord vector lift is `ContDiffAt`** at the chart point. -/
theorem localLiftChartVec_contDiffAt (Q₀ : X) (constants : Fin (genus X) → ℂ) :
    ContDiffAt ℂ ω (localLiftChartVec (X := X) Q₀ constants)
      ((chartAt (H := ℂ) Q₀) Q₀) :=
  (localLiftChartVec_analyticAt Q₀ constants).contDiffAt

/-- **The vector-valued local lift is `ContMDiffAt`** at `Q₀`.

`localLift Q₀ constants = localLiftChartVec Q₀ constants ∘ chartAt ℂ Q₀`.
The chart map `chartAt ℂ Q₀` is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` at `Q₀`
(Mathlib's `contMDiffAt_extChartAt`), and the chart-coord function is
`ContDiffAt ℂ ω` at `(chartAt ℂ Q₀) Q₀` (above). Mathlib's
`ContDiffAt.comp_contMDiffAt` glues these into `ContMDiffAt 𝓘(ℂ)
𝓘(ℂ, Fin (genus X) → ℂ) ω` of the composition. -/
theorem localLift_contMDiffAt (Q₀ : X) (constants : Fin (genus X) → ℂ) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω
      (localLift (X := X) Q₀ constants) Q₀ := by
  -- Step 1: `chartAt ℂ Q₀` is `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω` at `Q₀`.
  -- Use `contMDiffAt_extChartAt` and the fact that `extChartAt 𝓘(ℂ)` agrees
  -- with `chartAt ℂ` as a function (boundaryless model).
  have h_chart : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω
      (chartAt (H := ℂ) Q₀ : X → ℂ) Q₀ := by
    have h_ext : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ) ω
        (extChartAt 𝓘(ℂ) Q₀ : X → ℂ) Q₀ := contMDiffAt_extChartAt
    -- `extChartAt 𝓘(ℂ) Q₀` = `chartAt ℂ Q₀` as functions on the chart source.
    -- Their values agree pointwise (model is identity).
    have h_eq : (extChartAt 𝓘(ℂ) Q₀ : X → ℂ) = (chartAt (H := ℂ) Q₀ : X → ℂ) := by
      funext y
      simp [extChartAt_coe]
    rw [h_eq] at h_ext
    exact h_ext
  -- Step 2: chart-coord vector function is `ContDiffAt ℂ ω` at chart-image.
  have h_chartVec : ContDiffAt ℂ ω
      (localLiftChartVec (X := X) Q₀ constants) ((chartAt (H := ℂ) Q₀) Q₀) :=
    localLiftChartVec_contDiffAt Q₀ constants
  -- Step 3: compose via `ContDiffAt.comp_contMDiffAt`. The result is
  -- `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, V) ω (localLiftChartVec ∘ chartAt) Q₀`, which
  -- equals `ContMDiffAt ... (localLift ...) Q₀` by definition unfolding.
  have h_comp := h_chartVec.comp_contMDiffAt (x := Q₀) h_chart
  -- `localLift Q₀ constants = localLiftChartVec Q₀ constants ∘ chartAt ℂ Q₀`.
  change ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω
    (localLiftChartVec (X := X) Q₀ constants ∘ (chartAt (H := ℂ) Q₀)) Q₀
  exact h_comp

/-! ### Identification with `ofCurve P` in the quotient

The local lift centered at `Q₀` with `constants := periodVec(smoothPath
P Q₀)` agrees, on a chart neighborhood of `Q₀`, with `ofCurve P` in
the lattice quotient.

**Mathematical proof.** For `Q` in a chart-ball around `Q₀`, the
chart-segment `ChartBallPath Q₀ Q₀ Q : ℝ → X` is a smooth path from
`Q₀` to `Q` (`Jacobians.ChartBallPath.start` + `.finish` +
chart-transition smoothness — built up in `Jacobians/SmoothPath.lean`).

Then:

```
localLift Q₀ constants Q
  = constants + ∫_0^1 chartFormCoeff(z₀ + t(z-z₀)) (z-z₀) dt    -- def
  = constants + periodVec(ChartBallPath Q₀ Q₀ Q)                -- chart-frame line integral
  = periodVec(smoothPath P Q₀) + periodVec(ChartBallPath Q₀ Q₀ Q) -- choice of constants
  = periodVec(smoothPath P Q₀ ∗ ChartBallPath Q₀ Q₀ Q)           -- periodVec_concat
```

The concatenation `smoothPath P Q₀ ∗ ChartBallPath Q₀ Q₀ Q` is a
smooth path from `P` to `Q`. The difference `(smoothPath P Q₀ ∗
ChartBallPath Q₀ Q₀ Q) ∗ reverse(smoothPath P Q)` is a smooth closed
loop at `P`. By `periodVec_concat` + `periodVec_reverse`:

```
periodVec((smoothPath P Q₀ ∗ ChartBallPath Q₀ Q₀ Q) ∗ reverse(smoothPath P Q))
  = periodVec(smoothPath P Q₀ ∗ ChartBallPath ...) - periodVec(smoothPath P Q)
```

This closed loop's periodVec is in `truePeriodLattice X` by
`periodVec_mem_truePeriodLattice_of_closed`. Hence in the quotient:

```
[localLift Q₀ constants Q] = [periodVec(smoothPath P Q)]
```

**Status.** The Lean proof needs three sub-pieces, each ~50-150 LOC:

(a) `localLift_eq_constants_add_periodVec_ChartBallPath`: chart-coord
    integral equals path-integral.

    **Mathematical resolution (chart-frame cancellation by 1-form
    covariance).** For `γ := ChartBallPath Q₀ Q₀ Q` and `α :=
    periodBasisForm X i`, the path-integral integrand is
    `α.toFun (γ t) (pathSpeed γ t)`. This uses `chartAt (γ t)`-frame
    in `pathSpeed`, but the value is intrinsic (1-form against
    tangent vector).

    Compute in chart-Q₀ frame: let `h := chartAt (γ t) ∘ chartAt Q₀.
    symm` (the transition map). Then:
    * `pathSpeed γ t = h'(z(γt)) * (z - z₀)` (chain rule on
      `chartAt(γt) ∘ γ = h ∘ (chartAt(Q₀) ∘ γ)` evaluated at the
      chart-Q₀-frame derivative `(z - z₀)`).
    * The 1-form transforms covariantly: `α_γt(w) = α_Q₀(h⁻¹(w)) /
      h'(h⁻¹(w))`.
    * Hence `α.toFun (γt) v = α_γt(chartAt(γt)(γt)) · v` (in
      chart-γt frame) `= α_Q₀(z(γt))/h'(z(γt)) · v`.

    Plugging in `v = pathSpeed γ t = h'(z(γt)) · (z - z₀)`:
    `α.toFun (γt) (pathSpeed γt) = α_Q₀(z(γt)) · (z - z₀)`. The
    transition `h'` cancels exactly.

    And `α_Q₀(z(γt)) = localRep α Q₀ (γt) = chartFormCoeff Q₀ i
    (z₀ + t(z - z₀))`. So pointwise, the path-integral integrand
    equals the chart-coord integrand. `intervalIntegral.integral_congr`
    then gives equality of integrals.

    **Lean formalization cost.** ~150-300 LOC: requires manipulating
    `Trivialization.symmL`, `ContinuousLinearMap.smul_apply`, chain
    rule via `pathSpeed_comp_eq_mfderiv`-style decomposition. The
    chart `(chartAt Q₀).symm` isn't a global manifold map, so direct
    use of `pathSpeed_comp_eq_mfderiv` doesn't apply — we'd need a
    chart-restricted variant.

(b) `periodVec_concat` (PROVEN) + integrability bookkeeping on the
    concatenation of `smoothPath P Q₀` and `ChartBallPath Q₀ Q₀ Q`.
    The integrability of basis-form integrands on each piece needs
    `IsSmoothPath.integrable` for `smoothPath`, plus a separate
    integrability lemma for `ChartBallPath` (continuous integrand on
    `[0,1]` × compact chart-ball).

(c) `periodVec_smoothPath_eq_periodVec_concat_mod_lattice`: the
    closed-loop argument via `periodVec_mem_truePeriodLattice_of_closed`.
    The non-trivial step is showing `(smoothPath P Q₀ ∗ ChartBallPath
    Q₀ Q₀ Q) ∗ reverse(smoothPath P Q)` is a `IsClosedSmoothLoop`,
    which requires concat-smoothness + reverse-smoothness (both with
    proven infrastructure in `Jacobians/LineIntegral.lean` and
    `PeriodLattice.lean`). -/
/-! ### Chart-frame cancellation: pathSpeed of `ChartBallPath` and `localRep`

To prove the main identification (`localLift_quotient_eq_ofCurve_eventually`),
the structural content is the chart-frame cancellation lemma: for `γ :=
ChartBallPath Q₀ Q₀ Q t` and `α := periodBasisForm X i`,

```
α.toFun (γ t) (pathSpeed γ t) = chartFormCoeff Q₀ i (z₀ + t(z-z₀)) · (z - z₀)
```

The proof uses Mathlib's `TangentBundle.symmL_trivializationAt_eq_core`,
which identifies `(trivAt b₀).symmL ℂ b 1` with the chart-transition
derivative. The chain-rule on `(chartAt γt) ∘ (chartAt Q₀).symm ∘ affine`
gives the matching `pathSpeed γ t = fderiv (chart transition)((z-z₀))`.

We do NOT attempt to formalize this here in full generality. Instead, we
take a different route: we identify both sides at the single point
`Q = Q₀` and use that on the chart source, the **difference** is a
locally analytic ℂ^g-valued function that vanishes at Q₀ AND lands in
the period lattice (mod which the quotient is defined), so it's a
constant equal to zero in the quotient.

Specifically, the strategy uses:

* `localLift_contMDiffAt` (PROVEN) — the LHS is `ContMDiffAt` at Q₀.
* `ofCurve_contMDiff` would tell us the RHS is `ContMDiffAt` at Q₀,
  except we're proving that exact thing! So we use:
* `smoothPath_basepoint_change` (PROVEN) — algebraic reduction of RHS.
* Concrete closed-loop argument via `periodVec_concat`,
  `periodVec_reverse`, `periodVec_mem_truePeriodLattice_of_closed`.
-/

/-- **Chart-Q₀ tangent vector via the trivialization**: at any point
`y` in the chart source of `Q₀`, `(trivAt Q₀).symmL ℂ y 1` equals the
fderiv (over ℂ) of the chart-transition map. This is a specialization
of Mathlib's `TangentBundle.symmL_trivializationAt_eq_core`.

Note: with `I = 𝓘(ℂ)`, `range I = univ`, so `fderivWithin _ _ univ = fderiv`.
We state the lemma in the `fderivWithin` form to match what `tangentBundleCore`
gives directly; downstream we rewrite to `fderiv ℂ`. -/
lemma trivAt_symmL_one_eq_fderiv (Q₀ y : X)
    (hy : y ∈ (chartAt (H := ℂ) Q₀).source) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ y (1 : ℂ) =
      fderivWithin ℂ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) Q₀).symm)
        Set.univ ((chartAt (H := ℂ) Q₀) y) (1 : ℂ) := by
  have h_symmL := TangentBundle.symmL_trivializationAt_eq_core
    (I := 𝓘(ℂ, ℂ)) (M := X) (E := ℂ) (b₀ := Q₀) (b := y) hy
  -- Apply the equality at 1 ∈ ℂ.
  rw [show ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ y (1 : ℂ))
        = ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ y) (1 : ℂ) from rfl]
  rw [h_symmL]
  -- The coord change is `fderivWithin ℂ (extChartAt 𝓘(ℂ) y ∘ (extChartAt 𝓘(ℂ) Q₀).symm)
  --   (range 𝓘(ℂ)) (extChartAt 𝓘(ℂ) Q₀ y)`.
  -- For 𝓘(ℂ), extChartAt = chartAt and range = univ.
  show (tangentBundleCore 𝓘(ℂ, ℂ) X).coordChange (achart ℂ Q₀) (achart ℂ y) y (1 : ℂ) =
    fderivWithin ℂ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) Q₀).symm) Set.univ
      ((chartAt (H := ℂ) Q₀) y) (1 : ℂ)
  rw [tangentBundleCore_coordChange_achart]
  -- Goal: fderivWithin ℂ (extChartAt 𝓘(ℂ) y ∘ (extChartAt 𝓘(ℂ) Q₀).symm) (range 𝓘(ℂ))
  --        (extChartAt 𝓘(ℂ) Q₀ y) 1 = fderivWithin ℂ ((chartAt y) ∘ (chartAt Q₀).symm)
  --        univ ((chartAt Q₀) y) 1
  have hrange : (Set.range (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ)) = Set.univ := by
    exact ModelWithCorners.range_eq_univ _
  have hext_chart : ∀ (z : ℂ) (b : X),
      ((extChartAt (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) b) : X → ℂ) = (chartAt (H := ℂ) b) := by
    intro z b; funext w
    simp [extChartAt]
  have hext_chart_pt : ∀ (b : X) (w : X),
      (extChartAt (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) b) w =
        (chartAt (H := ℂ) b) w := by
    intros; simp [extChartAt]
  have hext_symm : ∀ (b : X) (z : ℂ),
      ((extChartAt (𝓘(ℂ, ℂ) : ModelWithCorners ℂ ℂ ℂ) b).symm) z =
        (chartAt (H := ℂ) b).symm z := by
    intros; simp [extChartAt]
  -- Now rewrite all extChartAt's to chartAt's.
  rw [hrange]
  rw [hext_chart_pt Q₀ y]
  -- After unfolding extChartAt to chartAt, the two functions are definitionally
  -- equal (extChartAt 𝓘(ℂ) b = chartAt b, extChartAt symm = chartAt symm).
  rfl

/-- **ℂ-version of the chart-Q₀-frame tangent identity**. Since
`fderivWithin ℂ _ univ = fderiv ℂ _`, we can express `(trivAt Q₀).symmL ℂ y 1`
as the plain `fderiv ℂ` of the chart transition. -/
lemma trivAt_symmL_one_eq_fderiv_C (Q₀ y : X)
    (hy : y ∈ (chartAt (H := ℂ) Q₀).source) :
    (trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ y (1 : ℂ) =
      fderiv ℂ ((chartAt (H := ℂ) y) ∘ (chartAt (H := ℂ) Q₀).symm)
        ((chartAt (H := ℂ) Q₀) y) (1 : ℂ) := by
  rw [trivAt_symmL_one_eq_fderiv Q₀ y hy, fderivWithin_univ]

/-- **Chart-source membership: ChartBallPath Q₀ Q₀ Q t is in `(chartAt Q₀).source`
when the affine point is in `target`.** Trivial consequence of `ChartBallPath_mem_source`. -/
lemma chartBallPath_mem_source_of_affine (Q₀ Q : X) (t : ℝ)
    (h_target : ((1 - (t : ℂ)) * (chartAt ℂ Q₀) Q₀ + (t : ℂ) * (chartAt ℂ Q₀) Q)
        ∈ (chartAt ℂ Q₀).target) :
    Jacobians.ChartBallPath Q₀ Q₀ Q t ∈ (chartAt (H := ℂ) Q₀).source := by
  exact Jacobians.ChartBallPath_mem_source Q₀ Q₀ Q t h_target

/-- **Key chart-frame cancellation lemma (pointwise).** For `γ := ChartBallPath
Q₀ Q₀ Q` and `α := periodBasisForm X i`, the integrand of `lineIntegral α γ`
equals the chart-coord straight-line integrand. Specifically:

```
α.toFun (γ t) (pathSpeed γ t) = chartFormCoeff Q₀ i (z₀ + t(z-z₀)) · (z - z₀)
```

where `z = (chartAt Q₀) Q`, `z₀ = (chartAt Q₀) Q₀`.

This is the heart of sub-lemma (a) in the docstring above. The proof
uses the chain rule for `pathSpeed`, `trivAt_symmL_one_eq_fderiv_C`,
and ℂ-linearity of `α.toFun`. -/
lemma chartFrame_cancel (Q₀ Q : X) (i : Fin (genus X)) (t : ℝ)
    (h_target_nbhd : ∀ᶠ s : ℝ in nhds t,
      ((1 - (s : ℂ)) * (chartAt ℂ Q₀) Q₀ + (s : ℂ) * (chartAt ℂ Q₀) Q)
        ∈ (chartAt (H := ℂ) Q₀).target) :
    (periodBasisForm X i).toFun (Jacobians.ChartBallPath Q₀ Q₀ Q t)
        (pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q) t) =
      chartFormCoeff (X := X) Q₀ i
        ((1 - (t : ℂ)) * (chartAt ℂ Q₀) Q₀ + (t : ℂ) * (chartAt ℂ Q₀) Q)
      * ((chartAt ℂ Q₀) Q - (chartAt ℂ Q₀) Q₀) := by
  -- Set up.
  set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀
  set z : ℂ := (chartAt (H := ℂ) Q₀) Q with hz
  set affine : ℝ → ℂ := fun s => (1 - (s : ℂ)) * z₀ + (s : ℂ) * z with haffine
  set γ : ℝ → X := Jacobians.ChartBallPath Q₀ Q₀ Q with hγ
  -- The current-time target membership.
  have h_target_t : affine t ∈ (chartAt (H := ℂ) Q₀).target := h_target_nbhd.self_of_nhds
  -- γ t ∈ chartAt Q₀ source.
  have hγt_source : γ t ∈ (chartAt (H := ℂ) Q₀).source :=
    chartBallPath_mem_source_of_affine Q₀ Q t h_target_t
  -- γ t ∈ chartAt (γ t).source.
  have hγt_self_source : γ t ∈ (chartAt (H := ℂ) (γ t)).source :=
    mem_chart_source ℂ (γ t)
  -- chart Q₀ at γ t = affine t.
  have h_chart_γt : (chartAt (H := ℂ) Q₀) (γ t) = affine t := by
    rw [hγ]
    have h_in_target_at_t : (1 - (t : ℂ)) * (chartAt ℂ Q₀) Q₀ + (t : ℂ) * (chartAt ℂ Q₀) Q
        ∈ (chartAt (H := ℂ) Q₀).target := h_target_t
    -- chart_ChartBallPath_eq: when affine in target, chart of ChartBallPath = affine.
    exact Jacobians.chart_ChartBallPath_eq Q₀ Q₀ Q t h_in_target_at_t
  -- Differentiability of affine at t (always).
  have h_affine_diff : DifferentiableAt ℝ affine t :=
    Jacobians.differentiable_chart_image_formula Q₀ Q₀ Q t
  -- Fderiv of affine at t in direction 1 is `z - z₀`.
  have h_affine_fderiv : fderiv ℝ affine t (1 : ℝ) = z - z₀ := by
    rw [haffine]
    -- affine s = (1 - s) * z₀ + s * z = z₀ + s * (z - z₀)
    have h_eq : (fun s : ℝ => (1 - (s : ℂ)) * z₀ + (s : ℂ) * z) =
        (fun s : ℝ => z₀ + (s : ℂ) * (z - z₀)) := by funext s; ring
    rw [h_eq]
    -- fderiv of (z₀ + s * (z - z₀)) at t in direction 1:
    -- = fderiv (z₀) + fderiv (s * (z-z₀))
    -- = 0 + (z - z₀) * fderiv (s ↦ s)
    -- = (z - z₀) * 1 = (z - z₀).
    have h_id : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
    have h_smul : HasDerivAt (fun s : ℝ => s • (z - z₀)) ((1 : ℝ) • (z - z₀)) t :=
      h_id.smul_const (z - z₀)
    have h_eq2 : (fun s : ℝ => s • (z - z₀)) = (fun s : ℝ => (s : ℂ) * (z - z₀)) := by
      funext s; exact Complex.real_smul
    rw [h_eq2] at h_smul
    have h_one : ((1 : ℝ) • (z - z₀) : ℂ) = z - z₀ := by
      rw [Complex.real_smul]; simp
    rw [h_one] at h_smul
    -- h_smul : HasDerivAt (fun s : ℝ => (s : ℂ) * (z - z₀)) (z - z₀) t
    have h_const : HasDerivAt (fun _ : ℝ => z₀) 0 t := hasDerivAt_const t z₀
    have h_add : HasDerivAt (fun s : ℝ => z₀ + (s : ℂ) * (z - z₀)) (0 + (z - z₀)) t :=
      h_const.add h_smul
    rw [zero_add] at h_add
    -- h_add : HasDerivAt (...) (z - z₀) t.
    -- Convert to HasFDerivAt then take .fderiv.
    have h_fd : HasFDerivAt (fun s : ℝ => z₀ + (s : ℂ) * (z - z₀))
        (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (z - z₀)) t :=
      h_add.hasFDerivAt
    have h_fderiv_eq := h_fd.fderiv
    rw [h_fderiv_eq]
    -- ContinuousLinearMap.smulRight 1 (z - z₀) applied to 1 = 1 • (z - z₀) = z - z₀
    show ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (z - z₀) (1 : ℝ) = z - z₀
    simp
  -- Chart transition h := (chartAt γt) ∘ (chartAt Q₀).symm.
  set h_trans : ℂ → ℂ := fun w => (chartAt (H := ℂ) (γ t)) ((chartAt (H := ℂ) Q₀).symm w)
    with hh_trans
  -- h_trans is differentiable at (affine t) over ℂ.
  have h_trans_diff_C : DifferentiableAt ℂ h_trans (affine t) := by
    have h_src : (chartAt (H := ℂ) Q₀).symm (affine t) ∈ (chartAt (H := ℂ) (γ t)).source := by
      rw [show (chartAt (H := ℂ) Q₀).symm (affine t) = γ t from ?_]
      · exact hγt_self_source
      · -- γ t = (chartAt Q₀).symm (affine t)
        rw [hγ]
        show Jacobians.ChartBallPath Q₀ Q₀ Q t = _
        rfl
    have h_dC := Jacobians.chart_transition_differentiableAt_C (X := X) Q₀ (γ t) (affine t)
      h_target_t h_src
    -- h_dC : DifferentiableAt ℂ ((chartAt Q₀).symm ≫ₕ (chartAt (γ t))) (affine t)
    -- Express ≫ₕ as plain composition.
    have h_eq_comp : (fun v : ℂ =>
        ((((chartAt (H := ℂ) Q₀).symm ≫ₕ (chartAt (H := ℂ) (γ t))) : ℂ → ℂ)) v) =ᶠ[nhds (affine t)]
        h_trans := by
      have h_open : IsOpen ((chartAt (H := ℂ) Q₀).symm ≫ₕ (chartAt (H := ℂ) (γ t))).source :=
        ((chartAt (H := ℂ) Q₀).symm ≫ₕ (chartAt (H := ℂ) (γ t))).open_source
      have h_mem : affine t ∈ ((chartAt (H := ℂ) Q₀).symm ≫ₕ (chartAt (H := ℂ) (γ t))).source :=
        (Jacobians.chart_trans_source_iff (X := X) Q₀ (γ t) (affine t)).mpr
          ⟨h_target_t, h_src⟩
      filter_upwards [h_open.mem_nhds h_mem] with v _hv
      rfl
    exact h_dC.congr_of_eventuallyEq h_eq_comp
  -- h_trans is differentiable at (affine t) over ℝ (restrict scalars).
  have h_trans_diff_R : DifferentiableAt ℝ h_trans (affine t) :=
    @DifferentiableAt.restrictScalars ℝ _ ℂ _ _ ℂ _ _ _
      Jacobians.instIsScalarTower_R_C_C
      ℂ _ _ _ Jacobians.instIsScalarTower_R_C_C _ _ h_trans_diff_C
  -- fderiv ℝ h_trans = (fderiv ℂ h_trans).restrictScalars ℝ.
  have h_trans_fderiv_RC : fderiv ℝ h_trans (affine t) =
      (fderiv ℂ h_trans (affine t)).restrictScalars ℝ := by
    have hFD_C : HasFDerivAt h_trans (fderiv ℂ h_trans (affine t)) (affine t) :=
      h_trans_diff_C.hasFDerivAt
    have hFD_R : HasFDerivAt h_trans
        ((fderiv ℂ h_trans (affine t)).restrictScalars ℝ) (affine t) := by
      rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hFD_C ⊢
      simp only [ContinuousLinearMap.coe_restrictScalars']
      exact hFD_C
    exact hFD_R.fderiv
  -- Now compute pathSpeed γ t.
  -- pathSpeed γ t = fderiv ℝ (chart γt ∘ γ) t 1.
  -- chart γt ∘ γ is locally (near t) equal to h_trans ∘ affine.
  -- Use h_target_nbhd to get the local equality.
  have h_local_eq : (chartAt (H := ℂ) (γ t)).toFun ∘ γ =ᶠ[nhds t]
      h_trans ∘ affine := by
    filter_upwards [h_target_nbhd] with s hs_target
    -- chart_γt (γ s) = chart_γt ((chartAt Q₀).symm (affine s)) = h_trans (affine s)
    show (chartAt (H := ℂ) (γ t)) (γ s) = h_trans (affine s)
    have h_γs_eq : γ s = (chartAt (H := ℂ) Q₀).symm (affine s) := rfl
    rw [h_γs_eq]
  -- pathSpeed γ t via fderiv.
  have h_pathSpeed : pathSpeed γ t = fderiv ℝ (h_trans ∘ affine) t 1 := by
    show fderiv ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t 1 = _
    rw [Filter.EventuallyEq.fderiv_eq h_local_eq]
  -- Apply chain rule.
  have h_chain : fderiv ℝ (h_trans ∘ affine) t =
      (fderiv ℝ h_trans (affine t)).comp (fderiv ℝ affine t) :=
    fderiv_comp t h_trans_diff_R h_affine_diff
  -- pathSpeed γ t = (fderiv ℝ h_trans (affine t)) (z - z₀).
  have h_pathSpeed_eq : pathSpeed γ t = (fderiv ℝ h_trans (affine t)) (z - z₀) := by
    rw [h_pathSpeed, h_chain, ContinuousLinearMap.comp_apply, h_affine_fderiv]
  -- Replace fderiv ℝ with fderiv ℂ via restrictScalars.
  have h_pathSpeed_C : pathSpeed γ t = (fderiv ℂ h_trans (affine t)) (z - z₀) := by
    rw [h_pathSpeed_eq, h_trans_fderiv_RC, ContinuousLinearMap.coe_restrictScalars']
  -- For a ℂ-linear map ℂ →L[ℂ] ℂ, applying to (z - z₀) = (z - z₀) * applied-to-1.
  have h_fderiv_apply : (fderiv ℂ h_trans (affine t)) (z - z₀) =
      (z - z₀) * (fderiv ℂ h_trans (affine t)) 1 := by
    have := (fderiv ℂ h_trans (affine t)).map_smul (z - z₀) (1 : ℂ)
    -- this : (fderiv ℂ h_trans (affine t)) ((z - z₀) • 1) = (z - z₀) • (fderiv ℂ h_trans (affine t)) 1
    rw [smul_eq_mul, mul_one] at this
    rw [this, smul_eq_mul]
  -- pathSpeed γ t = (z - z₀) * (fderiv ℂ h_trans (affine t) 1).
  have h_pathSpeed_final : pathSpeed γ t = (z - z₀) * (fderiv ℂ h_trans (affine t)) 1 := by
    rw [h_pathSpeed_C, h_fderiv_apply]
  -- chartFormCoeff Q₀ i (affine t) = α.toFun(γt)((trivAt Q₀).symmL ℂ (γt) 1)
  --                                = α.toFun(γt)(fderiv ℂ h_trans (affine t) 1)
  have h_chartFormCoeff : chartFormCoeff (X := X) Q₀ i (affine t) =
      (periodBasisForm X i).toFun (γ t) ((fderiv ℂ h_trans (affine t)) 1) := by
    unfold chartFormCoeff
    show Jacobians.Montel.localRep (periodBasisForm X i) Q₀
        ((chartAt (H := ℂ) Q₀).symm (affine t)) = _
    have h_eq : (chartAt (H := ℂ) Q₀).symm (affine t) = γ t := by
      rw [hγ]
      show _ = Jacobians.ChartBallPath Q₀ Q₀ Q t
      rfl
    rw [h_eq]
    show (periodBasisForm X i).toFun (γ t)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) Q₀).symmL ℂ (γ t) 1) = _
    rw [trivAt_symmL_one_eq_fderiv_C Q₀ (γ t) hγt_source]
    congr 1
    -- Need: fderiv ℂ ((chartAt γt) ∘ (chartAt Q₀).symm) ((chartAt Q₀) (γt)) 1 =
    --       fderiv ℂ h_trans (affine t) 1
    -- (chartAt Q₀)(γt) = affine t (by h_chart_γt).
    -- h_trans = (chartAt γt) ∘ (chartAt Q₀).symm.
    rw [h_chart_γt]
    rfl
  -- Assemble.
  rw [h_chartFormCoeff, h_pathSpeed_final]
  -- Goal: α.toFun(γt) ((z - z₀) * fderiv ℂ h_trans (affine t) 1) =
  --       α.toFun(γt) (fderiv ℂ h_trans (affine t) 1) * (z - z₀)
  -- Use ℂ-linearity of the CLM α.toFun(γt):
  have h_lin : ((periodBasisForm X i).toFun (γ t))
      ((z - z₀) * (fderiv ℂ h_trans (affine t)) 1) =
        (z - z₀) * ((periodBasisForm X i).toFun (γ t))
          ((fderiv ℂ h_trans (affine t)) 1) := by
    have := (periodBasisForm X i).toFun (γ t) |>.map_smul (z - z₀)
      ((fderiv ℂ h_trans (affine t)) 1)
    simp only [smul_eq_mul] at this
    exact this
  rw [h_lin]
  ring

/-- **`Q ∈ (chartAt Q₀).source` eventually in `nhds Q₀`.**

Chart source is open and contains `Q₀`. -/
lemma Q_in_chart_source_eventually (Q₀ : X) :
    ∀ᶠ Q in nhds Q₀, Q ∈ (chartAt (H := ℂ) Q₀).source := by
  exact (chartAt (H := ℂ) Q₀).open_source.mem_nhds (mem_chart_source ℂ Q₀)

/-- **Affine path stays in chart target near Q₀.** Trivially, near Q₀
(where `Q = Q₀`), `affine s = z₀` is in the chart target. We need the
target-membership uniform in `s ∈ Icc 0 1`, for a chart-ball
neighborhood of Q₀. -/
lemma affine_in_target_eventually (Q₀ : X) :
    ∀ᶠ Q in nhds Q₀, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target := by
  -- Pick a chart ball `Metric.ball z₀ r ⊆ (chartAt Q₀).target`.
  set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀
  have h_open := (chartAt (H := ℂ) Q₀).open_target
  have h_src : Q₀ ∈ (chartAt (H := ℂ) Q₀).source := mem_chart_source ℂ Q₀
  have h_mem : z₀ ∈ (chartAt (H := ℂ) Q₀).target :=
    (chartAt (H := ℂ) Q₀).map_source h_src
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp h_open _ h_mem
  -- The set V := {Q | (chartAt Q₀) Q ∈ Metric.ball z₀ r} ∩ (chartAt Q₀).source
  -- is open and contains Q₀.
  -- For Q ∈ V, the convex hull of {z₀, (chartAt Q₀) Q} ⊆ Metric.ball z₀ r ⊆ target.
  have h_chart_cont : ContinuousAt (chartAt (H := ℂ) Q₀) Q₀ :=
    (chartAt (H := ℂ) Q₀).continuousAt h_src
  -- The preimage of `Metric.ball z₀ r` under chartAt Q₀ is open in X at Q₀.
  have h_preimage : ∀ᶠ Q in nhds Q₀, (chartAt (H := ℂ) Q₀) Q ∈ Metric.ball z₀ r :=
    h_chart_cont.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos))
  filter_upwards [h_preimage] with Q hQ_in_ball s hs
  -- Convex combination of z₀ (= chart Q₀) and (chart Q) lies in ball z₀ r.
  have hz₀_mem : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr_pos
  have hz_mem : (chartAt (H := ℂ) Q₀) Q ∈ Metric.ball z₀ r := hQ_in_ball
  have hconv : Convex ℝ (Metric.ball z₀ r) := convex_ball _ _
  have h_combine := hconv hz₀_mem hz_mem (a := 1 - s) (b := s)
    (by linarith [hs.1, hs.2]) (by linarith [hs.1, hs.2]) (by linarith)
  -- Convert real-smul to complex-mul.
  have h_eq : ((1 - s : ℝ) • z₀ + s • (chartAt (H := ℂ) Q₀) Q : ℂ) =
      (1 - (s : ℂ)) * z₀ + (s : ℂ) * (chartAt (H := ℂ) Q₀) Q := by
    rw [Complex.real_smul, Complex.real_smul]; push_cast; ring
  rw [h_eq] at h_combine
  exact hr_subset h_combine

/-- **localLift via lineIntegral(ChartBallPath).** Using `chartFrame_cancel`,
we identify `localLift Q₀ c Q` with `c + periodVec(ChartBallPath Q₀ Q₀ Q)`
componentwise, provided the affine path stays in chart target on `[0,1]`.

This is sub-lemma (a) in the docstring above. -/
lemma localLift_eq_const_add_periodVec_ChartBallPath
    (Q₀ Q : X) (c : Fin (genus X) → ℂ)
    (h_target_Icc : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    localLift (X := X) Q₀ c Q =
      c + Jacobians.periodVec (Jacobians.ChartBallPath Q₀ Q₀ Q) := by
  funext i
  show localLiftChart (X := X) Q₀ c i ((chartAt (H := ℂ) Q₀) Q) = _
  unfold localLiftChart
  set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀
  set z : ℂ := (chartAt (H := ℂ) Q₀) Q with hz
  -- Apply chartFrame_cancel pointwise on [0, 1].
  -- The affine path stays in target on Icc 0 1; extend to nbhd by openness.
  have h_target_nbhd_at : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ᶠ (s : ℝ) in nhds t,
        ((1 - (s : ℂ)) * z₀ + (s : ℂ) * z) ∈ (chartAt (H := ℂ) Q₀).target := by
    intro t ht
    -- The set `{s | affine s ∈ target}` is open (preimage of open under continuous).
    have h_cont : Continuous (fun s : ℝ => (1 - (s : ℂ)) * z₀ + (s : ℂ) * z) := by
      refine Continuous.add ?_ ?_
      · exact (continuous_const.sub Complex.continuous_ofReal).mul continuous_const
      · exact Complex.continuous_ofReal.mul continuous_const
    have h_open_set : IsOpen
        {s : ℝ | (1 - (s : ℂ)) * z₀ + (s : ℂ) * z ∈ (chartAt (H := ℂ) Q₀).target} := by
      have := (chartAt (H := ℂ) Q₀).open_target.preimage h_cont
      exact this
    have h_t_mem : t ∈ {s : ℝ | (1 - (s : ℂ)) * z₀ + (s : ℂ) * z ∈
        (chartAt (H := ℂ) Q₀).target} := h_target_Icc t ht
    exact h_open_set.mem_nhds h_t_mem
  -- Pointwise: chart-coord integrand = path integrand on Icc 0 1.
  have h_pointwise : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      chartFormCoeff (X := X) Q₀ i ((1 - (t : ℂ)) * z₀ + (t : ℂ) * z) * (z - z₀) =
        (periodBasisForm X i).toFun (Jacobians.ChartBallPath Q₀ Q₀ Q t)
          (pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q) t) := by
    intro t ht
    exact (chartFrame_cancel (X := X) Q₀ Q i t (h_target_nbhd_at t ht)).symm
  -- Use intervalIntegral.integral_congr to lift pointwise eq to integral eq.
  have h_int_eq : ∫ t in (0 : ℝ)..1,
        chartFormCoeff (X := X) Q₀ i ((1 - (t : ℂ)) * z₀ + (t : ℂ) * z) * (z - z₀) =
      ∫ t in (0 : ℝ)..1,
        (periodBasisForm X i).toFun (Jacobians.ChartBallPath Q₀ Q₀ Q t)
          (pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q) t) := by
    refine intervalIntegral.integral_congr ?_
    -- uIcc 0 1 = Icc 0 1 since 0 ≤ 1.
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    exact h_pointwise
  -- Conclude.
  show c i + ∫ t in (0 : ℝ)..1,
      chartFormCoeff (X := X) Q₀ i (z₀ + (t : ℂ) * (z - z₀)) * (z - z₀) =
    c i + Jacobians.periodVec (Jacobians.ChartBallPath Q₀ Q₀ Q) i
  -- Step 1: rewrite (z₀ + t(z - z₀)) = (1 - t)·z₀ + t·z
  have h_rewrite : (fun t : ℝ =>
      chartFormCoeff (X := X) Q₀ i (z₀ + (t : ℂ) * (z - z₀)) * (z - z₀)) =
      fun t : ℝ =>
        chartFormCoeff (X := X) Q₀ i ((1 - (t : ℂ)) * z₀ + (t : ℂ) * z) * (z - z₀) := by
    funext t
    have : z₀ + (t : ℂ) * (z - z₀) = (1 - (t : ℂ)) * z₀ + (t : ℂ) * z := by ring
    rw [this]
  rw [h_rewrite, h_int_eq]
  -- Step 2: periodVec γ i = lineIntegral (periodBasisForm X i) γ.
  rfl

/-! ### IsSmoothPath for ChartBallPath

Given the chart-ball constraint (`affine in chart.target on Icc 0 1`)
and `Q ∈ chart.source`, `ChartBallPath Q₀ Q₀ Q` is a smooth path from
`Q₀` to `Q` ON `[0, 1]`. The `IsSmoothPath` structure as currently
defined in `Jacobians/PeriodLattice.lean` requires `cont : Continuous
γ` (i.e. globally on ℝ). But `ChartBallPath` is only `ContinuousOn
[0, 1]` (outside, the affine in chart coords escapes `target`,
making `(chartAt Q₀).symm` return junk). To bridge:

**Required (not yet built):** a smoothstep-clamped variant
`ChartBallPathClamped Q₀ Q := ChartBallPath Q₀ Q₀ Q ∘ smoothStep01`
that is constant outside `[0, 1]`, agrees with `ChartBallPath` on
`[0, 1]`, and has matching boundary derivatives via `smoothStep01`'s
zero-derivative endpoints. Then the periodVec of the clamped variant
equals that of `ChartBallPath` (integral only sees `[0, 1]`) and all
`IsSmoothPath` fields hold.

**Status (2026-05-28):** Field-by-field, `start`/`finish`/`diff` are
proven (via existing infrastructure). `cont` (global) and `integrable`
require the clamping-and-smoothstep machinery, ~200-300 LOC. -/
lemma isSmoothPath_ChartBallPath (Q₀ Q : X)
    (hQ_src : Q ∈ (chartAt (H := ℂ) Q₀).source)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.IsSmoothPath Q₀ Q (Jacobians.ChartBallPath Q₀ Q₀ Q) := by
  have hQ₀_src : Q₀ ∈ (chartAt (H := ℂ) Q₀).source := mem_chart_source ℂ Q₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- start: ChartBallPath Q₀ Q₀ Q 0 = Q₀
    exact Jacobians.ChartBallPath.start Q₀ Q₀ Q hQ₀_src
  · -- finish: ChartBallPath Q₀ Q₀ Q 1 = Q
    exact Jacobians.ChartBallPath.finish Q₀ Q₀ Q hQ_src
  · -- continuity globally on ℝ (sorry; needs extension argument)
    sorry
  · -- diff: from ChartBallPath_chart_at_self_differentiableAt
    intro t ht
    have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht; exact ht
    exact Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q t
      (h_chart_ball t ht_Icc)
  · -- integrable (sorry; via chartFrame_cancel + bounded continuity)
    sorry

/-! ### IsSmoothPath for ChartBallPathSmooth (smoothstep-reparameterized)

This variant uses `smoothStep01` reparameterization so that derivatives
at boundary points are zero — which is what's needed for the eventual
concat-smoothness argument. The `start`, `finish`, `cont`, `diff`
fields are PROVEN via the building blocks in `Jacobians/SmoothPath.lean`;
the `integrable` field remains a focused sub-sorry (continuity of the
basis-form integrand on `[0, 1]`). -/
lemma isSmoothPath_ChartBallPathSmooth (Q₀ Q : X)
    (hQ_src : Q ∈ (chartAt (H := ℂ) Q₀).source)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.IsSmoothPath Q₀ Q (Jacobians.ChartBallPathSmooth Q₀ Q) := by
  have hQ₀_src : Q₀ ∈ (chartAt (H := ℂ) Q₀).source := mem_chart_source ℂ Q₀
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Jacobians.ChartBallPathSmooth.start Q₀ Q hQ₀_src
  · exact Jacobians.ChartBallPathSmooth.finish Q₀ Q hQ_src
  · exact Jacobians.ChartBallPathSmooth.continuous Q₀ Q h_chart_ball
  · intro t _
    exact Jacobians.ChartBallPathSmooth_chart_at_self_differentiableAt Q₀ Q t h_chart_ball
  · sorry  -- integrable: needs pathSpeed_smoothStep01_comp_eq moved up + ContinuousOn argument

/-! ### Reparameterization invariance of periodVec under smoothStep01

By substitution-of-variables (`intervalIntegral.integral_comp_mul_deriv`),
`periodVec (γ ∘ smoothStep01) = periodVec γ` for any smooth path γ
(with appropriate regularity hypotheses). Applied to ChartBallPath
gives `periodVec (ChartBallPathSmooth Q₀ Q) = periodVec (ChartBallPath
Q₀ Q₀ Q)`. -/

/-- **PathSpeed chain rule for smoothStep01 reparameterization.**

For a smooth path `γ : ℝ → X` and `σ := smoothStep01`, the pathSpeed
of `γ ∘ σ` at `t` equals `σ'(t) • pathSpeed γ (σ t)` via the chain
rule applied to `(chartAt (γ(σ t))).toFun ∘ γ ∘ σ`.

Requires:
* `γ` chart-pullback differentiable at `σ t` (i.e., the existing
  `pathSpeed γ (σ t)` is computed from a `HasDerivAt`).
-/
lemma pathSpeed_smoothStep01_comp_eq (γ : ℝ → X) (t : ℝ)
    (hγ_diff : DifferentiableAt ℝ
      ((chartAt (H := ℂ) (γ (Jacobians.smoothStep01 t))).toFun ∘ γ)
      (Jacobians.smoothStep01 t)) :
    Jacobians.pathSpeed (γ ∘ Jacobians.smoothStep01) t =
      (Jacobians.smoothStep01_deriv t : ℂ) *
        Jacobians.pathSpeed γ (Jacobians.smoothStep01 t) := by
  -- pathSpeed is defined as `fderiv ℝ ((chartAt ℂ (γ t)).toFun ∘ γ) t 1`.
  -- For `γ ∘ σ`, the chart point is `γ(σ t)`, same as in the inner expression.
  unfold Jacobians.pathSpeed
  -- Rewrite the composition: `(chartAt ℂ ((γ ∘ σ) t)).toFun ∘ (γ ∘ σ)` =
  -- `((chartAt ℂ (γ(σ t))).toFun ∘ γ) ∘ σ` (associativity).
  have h_assoc : (chartAt (H := ℂ) ((γ ∘ Jacobians.smoothStep01) t)).toFun ∘
        (γ ∘ Jacobians.smoothStep01) =
      ((chartAt (H := ℂ) (γ (Jacobians.smoothStep01 t))).toFun ∘ γ) ∘
        Jacobians.smoothStep01 := by
    funext s; rfl
  rw [h_assoc]
  -- Chain rule for HasDerivAt: φ ∘ σ at t has derivative σ'(t) • φ'(σ(t)).
  have hσ : HasDerivAt Jacobians.smoothStep01 (Jacobians.smoothStep01_deriv t) t :=
    Jacobians.smoothStep01_hasDerivAt_explicit t
  have hφ : HasDerivAt
      ((chartAt (H := ℂ) (γ (Jacobians.smoothStep01 t))).toFun ∘ γ)
      (Jacobians.pathSpeed γ (Jacobians.smoothStep01 t))
      (Jacobians.smoothStep01 t) := by
    -- pathSpeed γ (σ t) = fderiv ℝ (...) (σ t) 1, so HasDerivAt at σ t with that value.
    exact hγ_diff.hasDerivAt
  -- Apply scomp: HasDerivAt (φ ∘ σ) (σ' • pathSpeed γ (σ t)) t.
  have h_comp : HasDerivAt
      (((chartAt (H := ℂ) (γ (Jacobians.smoothStep01 t))).toFun ∘ γ) ∘
        Jacobians.smoothStep01)
      (Jacobians.smoothStep01_deriv t • Jacobians.pathSpeed γ (Jacobians.smoothStep01 t))
      t := HasDerivAt.scomp t hφ hσ
  -- HasDerivAt gives `(fderiv ℝ f t) 1 = f'` via `HasDerivAt.deriv`-style identity.
  -- Use deriv = (fderiv ...) 1.
  have h_deriv : deriv (((chartAt (H := ℂ) (γ (Jacobians.smoothStep01 t))).toFun ∘ γ) ∘
        Jacobians.smoothStep01) t =
      Jacobians.smoothStep01_deriv t • Jacobians.pathSpeed γ (Jacobians.smoothStep01 t) :=
    h_comp.deriv
  -- `deriv f x = (fderiv ℝ f x) 1` (unfold).
  have h_lhs_eq : (fderiv ℝ
      (((chartAt (H := ℂ) (γ (Jacobians.smoothStep01 t))).toFun ∘ γ) ∘
        Jacobians.smoothStep01) t) 1 =
      Jacobians.smoothStep01_deriv t • Jacobians.pathSpeed γ (Jacobians.smoothStep01 t) := by
    rw [← h_deriv]
    rfl
  rw [h_lhs_eq]
  -- Convert `r • z` (ℝ acting on ℂ) to `(r : ℂ) * z`.
  exact Complex.real_smul

/-- **Generic periodVec invariance under smoothStep01 reparameterization.**

For any path `γ : ℝ → X` whose chart-pullback is `DifferentiableAt ℝ`
at each `s ∈ [0, 1]`, and whose basis-form integrand is `ContinuousOn`
`[0, 1]`, `periodVec (γ ∘ smoothStep01) = periodVec γ`.

The proof:
1. By `pathSpeed_smoothStep01_comp_eq`, the integrand of
   `periodVec (γ ∘ σ) i` equals
   `σ'(t) • (α.toFun(γ(σ t)))(pathSpeed γ (σ t))` pointwise on `[0, 1]`.
2. By `intervalIntegral.integral_deriv_smul_comp'` (substitution-of-
   variables with `f = σ`, `f' = σ'`, `g(u) = α.toFun(γ u)(pathSpeed γ u)`),
   the integral equals `∫_{σ 0}^{σ 1} g(u) du = ∫_0^1 g(u) du =
   periodVec γ i`.

The substitution lemma's hypotheses:
* `HasDerivAt smoothStep01 (smoothStep01_deriv x) x` for each `x ∈ uIcc 0 1` (PROVEN).
* `ContinuousOn smoothStep01_deriv (uIcc 0 1)` (PROVEN).
* `ContinuousOn g (smoothStep01 '' [[0, 1]] = [0, 1])` (parameter — caller supplies). -/
lemma periodVec_smoothStep01_comp_eq_generic (γ : ℝ → X)
    (hγ_diff : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ s)).toFun ∘ γ) s)
    (hg_cont : ∀ i : Fin (genus X),
      ContinuousOn (fun u => (periodBasisForm X i).toFun (γ u)
        (Jacobians.pathSpeed γ u)) (Set.Icc (0 : ℝ) 1)) :
    Jacobians.periodVec (γ ∘ Jacobians.smoothStep01) = Jacobians.periodVec γ := by
  funext i
  -- Definitions: periodVec γ i = ∫_0^1 (periodBasisForm i).toFun (γ t) (pathSpeed γ t).
  show ∫ t in (0 : ℝ)..1, (periodBasisForm X i).toFun ((γ ∘ Jacobians.smoothStep01) t)
        (Jacobians.pathSpeed (γ ∘ Jacobians.smoothStep01) t) =
      ∫ t in (0 : ℝ)..1, (periodBasisForm X i).toFun (γ t) (Jacobians.pathSpeed γ t)
  -- Set g(u) := (periodBasisForm i).toFun(γ u)(pathSpeed γ u).
  set g : ℝ → ℂ :=
    fun u => (periodBasisForm X i).toFun (γ u) (Jacobians.pathSpeed γ u) with hg_def
  -- Step 1: integrand of LHS at t ∈ [0,1] equals σ'(t) • g(σ t).
  have h_integrand_eq : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      (periodBasisForm X i).toFun ((γ ∘ Jacobians.smoothStep01) t)
        (Jacobians.pathSpeed (γ ∘ Jacobians.smoothStep01) t) =
      Jacobians.smoothStep01_deriv t • g (Jacobians.smoothStep01 t) := by
    intro t ht
    have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht; exact ht
    have hs_Icc : Jacobians.smoothStep01 t ∈ Set.Icc (0 : ℝ) 1 :=
      Jacobians.smoothStep01_mem_unit t
    have hγ_diff_at_s := hγ_diff (Jacobians.smoothStep01 t) hs_Icc
    have h_speed := pathSpeed_smoothStep01_comp_eq γ t hγ_diff_at_s
    -- LHS = α.toFun(γ(σ t)) (pathSpeed (γ ∘ σ) t)
    -- = α.toFun(γ(σ t)) ((σ'(t) : ℂ) * pathSpeed γ (σ t))
    -- = (σ'(t) : ℂ) * α.toFun(γ(σ t)) (pathSpeed γ (σ t))  [ℂ-linearity]
    -- = σ'(t) • g(σ t)
    show (periodBasisForm X i).toFun (γ (Jacobians.smoothStep01 t))
        (Jacobians.pathSpeed (γ ∘ Jacobians.smoothStep01) t) =
      Jacobians.smoothStep01_deriv t • g (Jacobians.smoothStep01 t)
    rw [h_speed]
    -- α.toFun(γt) is ℂ-linear, so α.toFun(γt) ((σ' : ℂ) * x) = (σ' : ℂ) * α.toFun(γt)(x).
    -- Then (σ' : ℂ) * (...) = σ' • (...) via Complex.real_smul.symm.
    have h_lin : ((periodBasisForm X i).toFun (γ (Jacobians.smoothStep01 t)))
        ((Jacobians.smoothStep01_deriv t : ℂ) *
          Jacobians.pathSpeed γ (Jacobians.smoothStep01 t)) =
      (Jacobians.smoothStep01_deriv t : ℂ) *
        ((periodBasisForm X i).toFun (γ (Jacobians.smoothStep01 t)))
          (Jacobians.pathSpeed γ (Jacobians.smoothStep01 t)) := by
      -- Use ContinuousLinearMap.map_smul to extract the ℂ-scalar.
      have h_lin :=
        ((periodBasisForm X i).toFun (γ (Jacobians.smoothStep01 t))).map_smul
        (Jacobians.smoothStep01_deriv t : ℂ)
        (Jacobians.pathSpeed γ (Jacobians.smoothStep01 t))
      -- h_lin : α.toFun (γ ...) ((↑σ' : ℂ) • path) = (↑σ' : ℂ) • α.toFun (γ ...) (path)
      -- Convert smul to mul on both sides.
      simp only [smul_eq_mul] at h_lin
      exact h_lin
    rw [h_lin]
    -- Now: (σ' : ℂ) * g(σ t) = σ' • g(σ t) via Complex.real_smul.symm.
    show (Jacobians.smoothStep01_deriv t : ℂ) *
        ((periodBasisForm X i).toFun (γ (Jacobians.smoothStep01 t)))
          (Jacobians.pathSpeed γ (Jacobians.smoothStep01 t)) =
      Jacobians.smoothStep01_deriv t • g (Jacobians.smoothStep01 t)
    exact Complex.real_smul.symm
  -- Step 2: rewrite the integral via this pointwise identity.
  rw [intervalIntegral.integral_congr h_integrand_eq]
  -- Now: ∫ t in 0..1, σ'(t) • g(σ t) = ∫ t in 0..1, g t
  -- Step 3: apply substitution-of-variables.
  have h_subst : ∫ x in (0 : ℝ)..1, Jacobians.smoothStep01_deriv x •
        (g ∘ Jacobians.smoothStep01) x =
      ∫ x in Jacobians.smoothStep01 0..Jacobians.smoothStep01 1, g x :=
    intervalIntegral.integral_deriv_smul_comp'
      (h := fun x _ => Jacobians.smoothStep01_hasDerivAt_explicit x)
      (h' := Jacobians.smoothStep01_deriv_continuousOn_uIcc)
      (hg := by
        have h_subset : Jacobians.smoothStep01 '' (Set.uIcc (0 : ℝ) 1) ⊆ Set.Icc (0 : ℝ) 1 := by
          intro u hu
          obtain ⟨s, _, hs_eq⟩ := hu
          rw [← hs_eq]
          exact Jacobians.smoothStep01_mem_unit s
        exact (hg_cont i).mono h_subset)
  rw [Jacobians.smoothStep01_zero, Jacobians.smoothStep01_one] at h_subst
  -- The LHS of h_subst matches our goal's LHS (modulo composition unfolding).
  -- Note: σ'(t) • (g ∘ σ)(t) = σ'(t) • g(σ t).
  show ∫ t in (0 : ℝ)..1, Jacobians.smoothStep01_deriv t • g (Jacobians.smoothStep01 t) =
      ∫ t in (0 : ℝ)..1, g t
  exact h_subst

/-- **PeriodVec is invariant under `smoothStep01` reparameterization for ChartBallPath.**
Direct corollary of `periodVec_smoothStep01_comp_eq_generic` applied to
`ChartBallPath Q₀ Q₀ Q`. -/
lemma periodVec_ChartBallPathSmooth_eq (Q₀ Q : X)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.periodVec (Jacobians.ChartBallPathSmooth Q₀ Q) =
    Jacobians.periodVec (Jacobians.ChartBallPath Q₀ Q₀ Q) := by
  -- ChartBallPathSmooth Q₀ Q = ChartBallPath Q₀ Q₀ Q ∘ smoothStep01 (def unfolding).
  show Jacobians.periodVec (Jacobians.ChartBallPath Q₀ Q₀ Q ∘ Jacobians.smoothStep01) =
      Jacobians.periodVec (Jacobians.ChartBallPath Q₀ Q₀ Q)
  apply periodVec_smoothStep01_comp_eq_generic
  · -- Chart-pullback diff at each s ∈ [0, 1].
    intro s hs
    exact Jacobians.ChartBallPath_chart_at_self_differentiableAt Q₀ Q₀ Q s
      (h_chart_ball s hs)
  · -- ContinuousOn of integrand on [0, 1]. Use chartFrame_cancel:
    -- α.toFun (γt) (pathSpeed γ t) = chartFormCoeff Q₀ i (z₀ + t(z-z₀)) * (z - z₀).
    -- RHS is continuous on [0, 1] (chartFormCoeff continuous + polynomial in t).
    intro i
    -- Step 1: rewrite pointwise via chartFrame_cancel.
    set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀
    set z : ℂ := (chartAt (H := ℂ) Q₀) Q
    have h_eq : ∀ u ∈ Set.Icc (0 : ℝ) 1,
        (periodBasisForm X i).toFun (Jacobians.ChartBallPath Q₀ Q₀ Q u)
          (Jacobians.pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q) u) =
        chartFormCoeff (X := X) Q₀ i (z₀ + (u : ℂ) * (z - z₀)) * (z - z₀) := by
      intro u hu
      -- Need: nbhd hypothesis for chartFrame_cancel.
      have h_target_nbhd : ∀ᶠ s : ℝ in nhds u,
          ((1 - (s : ℂ)) * z₀ + (s : ℂ) * z) ∈ (chartAt (H := ℂ) Q₀).target := by
        have h_cont : Continuous (fun s : ℝ => (1 - (s : ℂ)) * z₀ + (s : ℂ) * z) := by
          refine Continuous.add ?_ ?_
          · exact (continuous_const.sub Complex.continuous_ofReal).mul continuous_const
          · exact Complex.continuous_ofReal.mul continuous_const
        have h_open : IsOpen
            {s : ℝ | (1 - (s : ℂ)) * z₀ + (s : ℂ) * z ∈ (chartAt (H := ℂ) Q₀).target} :=
          (chartAt (H := ℂ) Q₀).open_target.preimage h_cont
        exact h_open.mem_nhds (h_chart_ball u hu)
      have h_cf := chartFrame_cancel (X := X) Q₀ Q i u h_target_nbhd
      -- h_cf : chartFormCoeff Q₀ i ((1-u)·(chartAt Q₀)Q₀ + u·(chartAt Q₀)Q) *
      --        ((chartAt Q₀)Q - (chartAt Q₀)Q₀) = α.toFun (γu)(pathSpeed γu)
      -- Goal: α.toFun (γu)(pathSpeed γu) = chartFormCoeff Q₀ i (z₀ + u(z-z₀)) * (z - z₀)
      -- Where z₀ := chartAt Q₀ Q₀, z := chartAt Q₀ Q.
      have h_rewrite_form : z₀ + (u : ℂ) * (z - z₀) =
          (1 - (u : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ + (u : ℂ) * (chartAt (H := ℂ) Q₀) Q := by
        show z₀ + (u : ℂ) * (z - z₀) = (1 - (u : ℂ)) * z₀ + (u : ℂ) * z
        ring
      rw [h_rewrite_form]
      show ((periodBasisForm X i).toFun (Jacobians.ChartBallPath Q₀ Q₀ Q u))
          (Jacobians.pathSpeed (Jacobians.ChartBallPath Q₀ Q₀ Q) u) =
        chartFormCoeff (X := X) Q₀ i
          ((1 - (u : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ + (u : ℂ) * (chartAt (H := ℂ) Q₀) Q) *
        ((chartAt (H := ℂ) Q₀) Q - (chartAt (H := ℂ) Q₀) Q₀)
      exact h_cf
    -- Step 2: RHS continuous on [0, 1].
    have h_rhs_cont : ContinuousOn
        (fun u : ℝ => chartFormCoeff (X := X) Q₀ i (z₀ + (u : ℂ) * (z - z₀)) * (z - z₀))
        (Set.Icc (0 : ℝ) 1) := by
      refine ContinuousOn.mul ?_ continuousOn_const
      -- ContinuousOn of chartFormCoeff Q₀ i (affine in u).
      -- chartFormCoeff is continuous on chart target (from AnalyticOn).
      have h_chartFormCoeff_cont : ContinuousOn (chartFormCoeff (X := X) Q₀ i)
          (chartAt (H := ℂ) Q₀).target :=
        (chartFormCoeff_differentiableOn Q₀ i).continuousOn
      -- The affine map u ↦ z₀ + u(z - z₀) is continuous (ℝ → ℂ).
      have h_affine_cont : Continuous (fun u : ℝ => z₀ + (u : ℂ) * (z - z₀)) := by
        refine Continuous.add continuous_const ?_
        exact Complex.continuous_ofReal.mul continuous_const
      -- The affine maps [0,1] into chart target by h_chart_ball
      -- (after rewriting (z₀ + u(z-z₀)) = ((1-u)z₀ + uz)).
      have h_mapsTo : ∀ u ∈ Set.Icc (0 : ℝ) 1,
          z₀ + (u : ℂ) * (z - z₀) ∈ (chartAt (H := ℂ) Q₀).target := by
        intro u hu
        have h_rewrite : z₀ + (u : ℂ) * (z - z₀) = ((1 - (u : ℂ)) * z₀ + (u : ℂ) * z) := by
          ring
        rw [h_rewrite]
        exact h_chart_ball u hu
      exact h_chartFormCoeff_cont.comp h_affine_cont.continuousOn h_mapsTo
    -- Step 3: ContinuousOn of LHS via congruence.
    -- We have h_eq : ∀ u ∈ Icc 0 1, LHS(u) = RHS(u).
    -- ContinuousOn.congr converts ContinuousOn of RHS to ContinuousOn of LHS via EqOn.
    refine h_rhs_cont.congr ?_
    intro u hu
    exact h_eq u hu

/-! ### Smoothstep-reparameterized smoothPath

`smoothPath` from `Classical.choice` may not have zero derivative at
endpoints. To make the concat-at-junction smoothness work, we
similarly compose with `smoothStep01`. -/

/-- The smoothstep-reparameterized version of `smoothPath P Q`. -/
noncomputable def smoothPathSmooth (P Q : X) : ℝ → X :=
  fun t => Jacobians.smoothPath P Q (smoothStep01 t)

/-- `smoothPathSmooth` retains the start/end points of `smoothPath`. -/
@[simp] lemma smoothPathSmooth_zero (P Q : X) : smoothPathSmooth P Q 0 = P := by
  simp [smoothPathSmooth]

@[simp] lemma smoothPathSmooth_one (P Q : X) : smoothPathSmooth P Q 1 = Q := by
  simp [smoothPathSmooth]

/-- **PeriodVec invariance for smoothPath under `smoothStep01`**.

Direct corollary of `periodVec_smoothStep01_comp_eq_generic` applied to
`smoothPath P Q`, whose chart-pullback differentiability and integrand
continuity come from `Jacobians.isSmoothPath_smoothPath`. -/
lemma periodVec_smoothPathSmooth_eq (P Q : X) :
    Jacobians.periodVec (smoothPathSmooth P Q) =
    Jacobians.periodVec (Jacobians.smoothPath P Q) := by
  show Jacobians.periodVec (Jacobians.smoothPath P Q ∘ Jacobians.smoothStep01) =
      Jacobians.periodVec (Jacobians.smoothPath P Q)
  apply periodVec_smoothStep01_comp_eq_generic
  · -- Chart-pullback diff at each s ∈ [0, 1] from IsSmoothPath.diff.
    intro s hs
    have h_uIcc : s ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hs
    exact (Jacobians.isSmoothPath_smoothPath P Q).diff s h_uIcc
  · -- ContinuousOn of integrand on [0, 1] — sorry (needs continuity of
    -- pathSpeed for smoothPath). The IsSmoothPath.integrable field gives
    -- only integrability, not continuity. Continuity could be derived from
    -- C¹-ness of the chart-pullback but that's not directly available.
    sorry

/-- `smoothPathSmooth` is an `IsSmoothPath`, with zero derivative at
endpoints (via `smoothStep01`'s zero boundary derivatives). Closes
`start` (PROVEN), `finish` (PROVEN), `cont` (PROVEN, composition of
continuous smoothPath with continuous smoothStep01). `diff` and
`integrable` remain sub-sorries pending chain-rule + reparam
integrability work. -/
lemma isSmoothPath_smoothPathSmooth (P Q : X) :
    Jacobians.IsSmoothPath P Q (smoothPathSmooth P Q) := by
  have h_smoothPath := Jacobians.isSmoothPath_smoothPath P Q
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact smoothPathSmooth_zero P Q
  · exact smoothPathSmooth_one P Q
  · -- Continuous (smoothPath P Q ∘ smoothStep01)
    exact h_smoothPath.cont.comp Jacobians.smoothStep01_continuous
  · -- diff at each t ∈ uIcc 0 1 — via chain rule
    -- (chartAt (smoothPath ∘ σ t)) ∘ smoothPath ∘ σ = ((chartAt(γ ∘ σ t)) ∘ γ) ∘ σ
    -- Inner diff at σ t (from IsSmoothPath.diff of smoothPath at σ t).
    -- σ diff at t.
    -- Composition is diff.
    intro t ht
    have ht_Icc : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht; exact ht
    have hs_Icc : Jacobians.smoothStep01 t ∈ Set.Icc (0 : ℝ) 1 :=
      Jacobians.smoothStep01_mem_unit t
    have hs_uIcc : Jacobians.smoothStep01 t ∈ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]; exact hs_Icc
    have h_inner_diff := h_smoothPath.diff (Jacobians.smoothStep01 t) hs_uIcc
    have h_sigma_diff : DifferentiableAt ℝ Jacobians.smoothStep01 t :=
      Jacobians.smoothStep01_differentiable t
    -- smoothPathSmooth t = smoothPath (σ t), so chartAt (smoothPathSmooth t) = chartAt (smoothPath (σ t)).
    have h_eq : ((chartAt (H := ℂ) (smoothPathSmooth P Q t)).toFun ∘ smoothPathSmooth P Q) =
        ((chartAt (H := ℂ) (Jacobians.smoothPath P Q (Jacobians.smoothStep01 t))).toFun ∘
          Jacobians.smoothPath P Q) ∘ Jacobians.smoothStep01 := by
      funext s; rfl
    rw [h_eq]
    exact h_inner_diff.comp t h_sigma_diff
  · -- integrable — via reparam invariance of line integral
    sorry

/-! ### Closed loop via smoothstep junctions

With `ChartBallPathSmooth` and `smoothPathSmooth` both having zero
boundary derivatives, the bare `concat γ₁ (reverse γ₂)` has matching
(all zero) derivatives at the junction `t = 1/2`, hence is a closed
smooth loop. -/

/-- **The concat of `ChartBallPathSmooth Q₀ Q` and `reverse(smoothPathSmooth
Q₀ Q)` is a closed smooth loop at `Q₀`.**

All path endpoints have zero derivative (via `smoothStep01`), so the
bare `concat`'s derivative at the junction `t = 1/2` is `0` from both
sides → differentiable. -/
lemma isClosedSmoothLoop_concat_ChartBallPathSmooth_reverse_smoothPathSmooth
    (Q₀ Q : X)
    (_hQ_src : Q ∈ (chartAt (H := ℂ) Q₀).source)
    (_h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.IsClosedSmoothLoop (Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
      (Jacobians.reverse (smoothPathSmooth Q₀ Q))) :=
  sorry

/-- **periodVec of the concat = sum of periodVecs** for our specific paths. -/
lemma periodVec_concat_ChartBallPathSmooth_reverse_smoothPathSmooth
    (Q₀ Q : X)
    (_h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    Jacobians.periodVec (Jacobians.concat (Jacobians.ChartBallPathSmooth Q₀ Q)
      (Jacobians.reverse (smoothPathSmooth Q₀ Q))) =
    Jacobians.periodVec (Jacobians.ChartBallPathSmooth Q₀ Q) -
    Jacobians.periodVec (smoothPathSmooth Q₀ Q) :=
  sorry

/-- **Path-difference-in-lattice for ChartBallPath vs smoothPath.**

For `Q₀, Q : X` with the affine chart-coord segment from `(chartAt Q₀) Q₀`
to `(chartAt Q₀) Q` contained in `(chartAt Q₀).target`, the two smooth
paths `ChartBallPath Q₀ Q₀ Q` and `smoothPath Q₀ Q` both go from `Q₀`
to `Q`, so their periodVecs differ by a lattice element.

**Proof structure.** Apply `mk_periodVec_eq_of_endpoints` with `γ₁ :=
ChartBallPath Q₀ Q₀ Q`, `γ₂ := smoothPath Q₀ Q`. Hypotheses:
* `γ₁ 0 = γ₂ 0 = Q₀` (`ChartBallPath.start` + `smoothPath_zero`).
* `IsClosedSmoothLoop (concat γ₁ (reverse γ₂))`: needs ChartBallPath
  smoothness on chart-ball + smoothPath smoothness via
  `isSmoothPath_smoothPath` + reverse/concat smoothness preservation
  (proven infrastructure in `Jacobians/LineIntegral.lean` and
  `Jacobians/PeriodLattice.lean`).
* `periodVec_concat` formula: requires integrability of each basis
  form integrand on each piece. For `ChartBallPath`: integrand is
  bounded continuous on `[0, 1]` (using `chartFormCoeff` continuity
  + `chartFrame_cancel` to identify with the path integrand). For
  `smoothPath`: from `IsSmoothPath.integrable`.

We separate this as a single classical-content sub-sorry. -/
lemma chartBallPath_smoothPath_endpoints_eq_in_quotient
    (Q₀ Q : X)
    (hQ_src : Q ∈ (chartAt (H := ℂ) Q₀).source)
    (h_chart_ball : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ((1 - (s : ℂ)) * (chartAt (H := ℂ) Q₀) Q₀ +
        (s : ℂ) * (chartAt (H := ℂ) Q₀) Q) ∈ (chartAt (H := ℂ) Q₀).target) :
    (QuotientAddGroup.mk (Jacobians.periodVec (Jacobians.ChartBallPath Q₀ Q₀ Q)) :
      (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =
    QuotientAddGroup.mk (Jacobians.periodVec (Jacobians.smoothPath Q₀ Q)) := by
  -- Step 1: replace ChartBallPath by ChartBallPathSmooth (reparam-invariant periodVec).
  rw [← periodVec_ChartBallPathSmooth_eq Q₀ Q h_chart_ball]
  -- Step 2: replace smoothPath by smoothPathSmooth (same trick).
  rw [← periodVec_smoothPathSmooth_eq Q₀ Q]
  -- Step 3: Apply mk_periodVec_eq_of_endpoints with γ₁ = ChartBallPathSmooth, γ₂ = smoothPathSmooth.
  refine Jacobians.mk_periodVec_eq_of_endpoints
    (Jacobians.ChartBallPathSmooth Q₀ Q) (smoothPathSmooth Q₀ Q) ?_ ?_ ?_
  · -- h0: γ₁ 0 = γ₂ 0
    show Jacobians.ChartBallPathSmooth Q₀ Q 0 = smoothPathSmooth Q₀ Q 0
    rw [Jacobians.ChartBallPathSmooth.start Q₀ Q (mem_chart_source ℂ Q₀)]
    rw [smoothPathSmooth_zero]
  · -- hsmooth: concat is IsClosedSmoothLoop
    exact isClosedSmoothLoop_concat_ChartBallPathSmooth_reverse_smoothPathSmooth
      Q₀ Q hQ_src h_chart_ball
  · -- hconcat: periodVec(concat) = periodVec γ₁ - periodVec γ₂
    exact periodVec_concat_ChartBallPathSmooth_reverse_smoothPathSmooth Q₀ Q h_chart_ball

theorem localLift_quotient_eq_ofCurve_eventually
    (P Q₀ : X) :
    (fun Q => QuotientAddGroup.mk
        (localLift (X := X) Q₀ (periodVec (smoothPath P Q₀)) Q) :
      X → (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) =ᶠ[nhds Q₀]
      (fun Q => QuotientAddGroup.mk (periodVec (smoothPath P Q))) := by
  filter_upwards [affine_in_target_eventually Q₀, Q_in_chart_source_eventually Q₀]
    with Q hQ hQ_src
  -- Step 1: rewrite LHS via `localLift_eq_const_add_periodVec_ChartBallPath`.
  rw [localLift_eq_const_add_periodVec_ChartBallPath Q₀ Q _ hQ]
  -- LHS = [periodVec(smoothPath P Q₀) + periodVec(ChartBallPath Q₀ Q₀ Q)]
  --     = [periodVec(smoothPath P Q₀)] + [periodVec(ChartBallPath Q₀ Q₀ Q)]
  rw [QuotientAddGroup.mk_add]
  -- Step 2: use `chartBallPath_smoothPath_endpoints_eq_in_quotient` to replace
  -- [periodVec(ChartBallPath)] by [periodVec(smoothPath Q₀ Q)].
  rw [chartBallPath_smoothPath_endpoints_eq_in_quotient Q₀ Q hQ_src hQ]
  -- LHS now = [periodVec(smoothPath P Q₀)] + [periodVec(smoothPath Q₀ Q)]
  -- Step 3: rewrite RHS via `smoothPath_basepoint_change`.
  -- `smoothPath_basepoint_change Q₀ P Q`: with (P, P₀, A) = (Q₀, P, Q), gives:
  --   [periodVec(smoothPath P Q)] = [periodVec(smoothPath Q₀ Q)] + [periodVec(smoothPath P Q₀)]
  rw [Jacobians.smoothPath_basepoint_change Q₀ P Q]
  -- Goal: [periodVec(smoothPath P Q₀)] + [periodVec(smoothPath Q₀ Q)]
  --     = [periodVec(smoothPath Q₀ Q)] + [periodVec(smoothPath P Q₀)]
  -- Quotient is abelian; commute.
  exact add_comm _ _

/-! ## Top-level wiring for `ofCurve_contMDiff`

With `localLift_contMDiffAt` (analytic→ContMDiff bridge, PROVEN) and
`localLift_quotient_eq_ofCurve_eventually` (path-algebra identification,
sorry), the proof of `ofCurve_contMDiff` is a straightforward
local-to-global glue.

The function `Jacobians.OfCurveSkeleton.ofCurveContMDiff_via_localLift`
below packages the complete proof skeleton at the level of `Jacobians.
PeriodLattice`'s `truePeriodLattice` (since the quotient instance lives
there); the actual wiring into `Jacobians.ofCurve_contMDiff` in
`Jacobians.lean` requires the `Jacobian X = (Fin (genus X) → ℂ) ⧸
(periodLattice X)...` chartedSpace instance, which is `truePeriodLattice`
in different clothing — see `Jacobians.lean:periodLattice`. -/

end Jacobians.OfCurveSkeleton
