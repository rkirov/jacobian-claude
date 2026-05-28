/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Jacobians.PeriodLattice
import Jacobians.Discharge.Manifold.ContMDiffOmegaAnalytic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.CauchyIntegral

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
`z ∈ e.target`, the chart-pulled-back periodBasisForm is the action
of `(periodBasisForm X i)` at `e.symm z` against `(1 : ℂ)` viewed as
a chart-coord tangent vector.

Equivalently: the local coefficient of `ω_i` in the chart `e`. By
`HolomorphicOneForms`, this is holomorphic in `z` on `e.target`. -/
noncomputable def chartFormCoeff (Q₀ : X) (i : Fin (genus X)) (z : ℂ) : ℂ :=
  (periodBasisForm X i).toFun ((chartAt (H := ℂ) Q₀).symm z) (1 : ℂ)

/-- **The chart-form coefficient is holomorphic on the chart target.**

Classical content: `periodBasisForm X i` is a holomorphic 1-form, so
its coefficient in any chart is a holomorphic function of the chart
coordinate. The Lean route requires unfolding `HolomorphicOneForms`
to extract the analyticity of the coefficient. -/
theorem chartFormCoeff_differentiableOn (Q₀ : X) (i : Fin (genus X)) :
    DifferentiableOn ℂ (chartFormCoeff (X := X) Q₀ i)
      ((chartAt (H := ℂ) Q₀).target) := by
  -- `HolomorphicOneForms X` records (in its bundle structure) that
  -- the chart-coord coefficients are holomorphic. Extraction from
  -- the bundle structure is mechanical but requires unfolding the
  -- `HolomorphicOneForms` definition.
  --
  -- TODO(content): replay the chart-trivialization of the holomorphic
  -- 1-form bundle and extract the local section's analyticity.
  sorry

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

/-! ## Toward `ofCurve_contMDiff` (top-level theorem)

The remaining wiring:

1. **Local lift lifts `ofCurve P`** in the quotient: for `Q` close to
   `Q₀`, `[localLiftChart Q₀ constants i ((chartAt ℂ Q₀) Q)] =
   (ofCurve P Q) i` in the lattice quotient, when `constants` are
   chosen to be the periodVec of a fixed path `P → Q₀`. This uses
   `periodVec_concat` (already proven) and the lattice-mod identity.

2. **`AnalyticAt ⇒ ContMDiffAt`** in our chart-Lazy setup: from
   `AnalyticAt ℂ (localLiftChart Q₀ constants i)` at the chart point
   of `Q₀`, conclude `ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ^g) ω` of the original
   map at `Q₀`. (Uses `AnalyticAt.contDiffAt` + the manifold–normed-
   space contMDiffAt equivalence + the chart unfold.)

3. **Local-to-global**: `ContMDiff = ∀ Q, ContMDiffAt`. Apply Step 2
   at each `Q₀ ∈ X` and conclude `ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ^g) ω (fun Q
   => periodVec(some-path P → Q)) `. Compose with `contMDiff_mk` to
   reach `ofCurve P`.

Each step is mechanical given the lemmas above. -/

end Jacobians.OfCurveSkeleton
