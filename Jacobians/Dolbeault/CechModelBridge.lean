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

open Metric Topology BoundedContinuousFunction

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

/-- **Boundedness on a relatively-compact piece.**  An analytic function on `U` is bounded on any
compact `K ⊆ U` (it is continuous, hence bounded on the compact).  This supplies the `BddHol`
boundedness hypothesis: a cochain holomorphic on a cover-open is bounded on the (relatively-compact)
shrinking. -/
theorem bddOn_of_analyticOn_subset_compact {g : ℂ → ℂ} {U K : Set ℂ}
    (hg : AnalyticOn ℂ g U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C, ∀ z ∈ K, ‖g z‖ ≤ C :=
  hK.exists_bound_of_continuousOn (hg.continuousOn.mono hKU)

/-- **The practical K-bridge constructor.**  A function analytic on an open `U`, restricted to an
open `U'` whose closure is a compact subset of `U` (`U' ⋐ U`), is a `BddHol U'` element — the
boundedness is automatic on the relatively-compact piece.  This is the shape the germ→`BddHol` cochain
map uses: cover-cochains are holomorphic on the cover-open `U`, the model lives on the shrinking
`U' ⋐ U`. -/
noncomputable def ofAnalyticOnOfRelCompact {g : ℂ → ℂ} {U U' : Set ℂ} (hg : AnalyticOn ℂ g U)
    (hsub : closure U' ⊆ U) (hcpt : IsCompact (closure U')) : BddHol U' :=
  ofAnalyticOn g (hg.mono (subset_closure.trans hsub))
    (by
      obtain ⟨C, hC⟩ := bddOn_of_analyticOn_subset_compact hg hcpt hsub
      exact ⟨C, fun z hz => hC z (subset_closure hz)⟩)

@[simp] theorem ofAnalyticOnOfRelCompact_toFun_of_mem {g : ℂ → ℂ} {U U' : Set ℂ}
    (hg : AnalyticOn ℂ g U) (hsub : closure U' ⊆ U) (hcpt : IsCompact (closure U'))
    {z : ℂ} (hz : z ∈ U') :
    (ofAnalyticOnOfRelCompact hg hsub hcpt).toFun z = g z :=
  ofAnalyticOn_toFun_of_mem g _ _ hz

end BddHol

/-! ### Non-convex restriction compactness — Step 1: finite convex-disk cover

Toward generalizing `BddHol.isCompactOperator_restrictCLM` to a non-convex compact `K` (needed so a
`DiskOverlapData` can use chart-images of overlaps, which are not convex across charts).  Step 1: any
compact `K ⊆ U` (open) is covered by finitely many *closed balls* (convex compact) each `⊆ U`. -/

/-- **Finite convex-disk cover.**  For `K` compact inside an open `U ⊆ ℂ`, there is a finite family of
closed balls — centred on `K`, each contained in `U` (hence convex compact `⊆ U`) — whose open cores
cover `K`. -/
theorem exists_finite_closedBall_cover {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ (t : Finset K) (r : K → ℝ), (∀ z : K, 0 < r z) ∧
      (∀ z : K, Metric.closedBall (z : ℂ) (r z) ⊆ U) ∧
      K ⊆ ⋃ z ∈ t, Metric.ball (z : ℂ) (r z) := by
  have hr : ∀ z : K, ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall (z : ℂ) ρ ⊆ U := by
    intro z
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hKU z.2))
    exact ⟨ε / 2, by positivity, (Metric.closedBall_subset_ball (by linarith)).trans hball⟩
  choose r hr_pos hr_sub using hr
  have hcover : K ⊆ ⋃ z : K, Metric.ball (z : ℂ) (r z) := fun x hx =>
    Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr_pos ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => Metric.ball (z : ℂ) (r z))
    (fun _ => Metric.isOpen_ball) hcover
  exact ⟨t, r, hr_pos, hr_sub, ht⟩

/-! ### Non-convex restriction compactness — Step 2: equicontinuity on a non-convex compact

The convex equicontinuity lemma `Montel.uniformEquicontinuousOn_of_bounded_analyticOn` needs a global
mean-value inequality, which fails on a non-convex `K` (segments may leave `U`). We recover uniform
equicontinuity by a *local* mean-value argument with a **uniform Cauchy derivative bound**: thicken `K`
to a compact `K' = cthickening (δ/2) K ⋐ U`, where `δ` satisfies `cthickening δ K ⊆ U`. The repo's
`Montel.exists_cauchy_deriv_bound` (which needs no convexity) gives `‖(f i)' z‖ ≤ L·C` on all of `K'`.
For `x, y ∈ K` with `dist x y < δ/2`, the convex ball `closedBall x (δ/2) ⊆ K'` contains both, so the
1-dim mean-value inequality on that ball yields `‖f i x − f i y‖ ≤ L·C·dist x y` — a single equicontinuity
modulus valid across the whole (non-convex) `K`. This is exactly the Arzelà–Ascoli input. -/

/-- **Uniform equicontinuity of a bounded analytic family on a non-convex compact.** A family of
functions analytic on an open `U ⊆ ℂ` and uniformly bounded by `C` on `U` is uniformly equicontinuous
on *any* compact `K ⊆ U`, with no convexity assumption (cf. `Montel.uniformEquicontinuousOn_of_bounded_analyticOn`
which requires `Convex ℝ K`). -/
theorem uniformEquicontinuousOn_of_bounded_analyticOn_of_compact
    {ι : Type*} {U K : Set ℂ} {f : ι → ℂ → ℂ} {C : ℝ}
    (hU : IsOpen U) (hKcpt : IsCompact K) (hKU : K ⊆ U) (hCnn : 0 ≤ C)
    (hf : ∀ i, AnalyticOn ℂ (f i) U)
    (hfb : ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ C) :
    UniformEquicontinuousOn f K := by
  -- thicken K to a compact K' ⋐ U, so the Cauchy derivative bound is uniform on a neighborhood of K
  obtain ⟨δ, hδpos, hδsub⟩ := hKcpt.exists_cthickening_subset_open hU hKU
  set K' := Metric.cthickening (δ / 2) K with hK'def
  have hK'cpt : IsCompact K' := hKcpt.cthickening
  have hK'U : K' ⊆ U := (Metric.cthickening_mono (by linarith) K).trans hδsub
  obtain ⟨L, hLpos, hLbd⟩ := Jacobians.Montel.exists_cauchy_deriv_bound hU hK'cpt hK'U
  have hLC_nn : 0 ≤ L * C := mul_nonneg hLpos.le hCnn
  -- local mean-value Lipschitz bound on the convex ball `closedBall x (δ/2) ⊆ K'`
  have hmvt : ∀ i, ∀ x ∈ K, ∀ y ∈ K, dist x y < δ / 2 → ‖f i x - f i y‖ ≤ L * C * dist x y := by
    intro i x hx y hy hxy
    set s := Metric.closedBall x (δ / 2) with hsdef
    have hsK' : s ⊆ K' := Metric.closedBall_subset_cthickening hx (δ / 2)
    have hsU : s ⊆ U := hsK'.trans hK'U
    have hxs : x ∈ s := Metric.mem_closedBall_self (by linarith)
    have hys : y ∈ s := by rw [hsdef, Metric.mem_closedBall, dist_comm]; linarith
    have hconv : Convex ℝ s := convex_closedBall x (δ / 2)
    have hderBnd : ∀ z ∈ s, ‖deriv (f i) z‖ ≤ L * C := fun z hz =>
      hLbd (f i) (hf i) C (hfb i) z (hsK' hz)
    have hhasDer : ∀ z ∈ s, HasDerivWithinAt (f i) (deriv (f i) z) s z := by
      intro z hz
      have hz_in_U : z ∈ U := hsU hz
      have hdiff : DifferentiableAt ℂ (f i) z :=
        ((hf i).differentiableOn z hz_in_U).differentiableAt (hU.mem_nhds hz_in_U)
      exact hdiff.hasDerivAt.hasDerivWithinAt
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hhasDer hderBnd hconv hxs hys
    calc ‖f i x - f i y‖ = ‖f i y - f i x‖ := norm_sub_rev _ _
      _ ≤ L * C * ‖y - x‖ := hmv
      _ = L * C * dist x y := by rw [← dist_eq_norm, dist_comm]
  -- assemble `UniformEquicontinuousOn` via the metric ε-δ criterion on the subtype `↥K`
  rw [← uniformEquicontinuous_restrict_iff, Metric.uniformEquicontinuous_iff]
  intro ε hε
  refine ⟨min (δ / 2) (ε / (L * C + 1)), lt_min (by linarith) (by positivity), ?_⟩
  intro x y hxy i
  have hxy2 : dist (x : ℂ) (y : ℂ) < δ / 2 :=
    lt_of_lt_of_le (by rwa [Subtype.dist_eq] at hxy) (min_le_left _ _)
  have hxyε : dist (x : ℂ) (y : ℂ) < ε / (L * C + 1) :=
    lt_of_lt_of_le (by rwa [Subtype.dist_eq] at hxy) (min_le_right _ _)
  have hbd := hmvt i x.1 x.2 y.1 y.2 hxy2
  show dist (f i x.1) (f i y.1) < ε
  rw [dist_eq_norm]
  have hpos1 : (0 : ℝ) < L * C + 1 := by positivity
  calc ‖f i x.1 - f i y.1‖ ≤ L * C * dist (x : ℂ) (y : ℂ) := hbd
    _ ≤ (L * C + 1) * dist (x : ℂ) (y : ℂ) := by gcongr; linarith
    _ < (L * C + 1) * (ε / (L * C + 1)) := mul_lt_mul_of_pos_left hxyε hpos1
    _ = ε := by field_simp

/-- **Non-convex Montel atom.** A sup-`M`-bounded family of functions holomorphic on an open `U ⊆ ℂ`,
restricted to *any* compact `K ⋐ U`, is relatively compact in `K →ᵇ ℂ` — the convexity-free analogue of
`CechFiniteness.isCompact_closure_restrict_bddHolo`. Convexity is no longer needed thanks to
`uniformEquicontinuousOn_of_bounded_analyticOn_of_compact`. -/
theorem isCompact_closure_restrict_bddHolo_of_compact
    {U K : Set ℂ} (hU : IsOpen U) (hKcpt : IsCompact K) (hKU : K ⊆ U)
    {M : ℝ} (hMnn : 0 ≤ M)
    {S : Type*} (g : S → ℂ → ℂ)
    (hg_an : ∀ s, AnalyticOn ℂ (g s) U) (hg_bd : ∀ s, ∀ z ∈ U, ‖g s z‖ ≤ M)
    (hg_cont : ∀ s, ContinuousOn (g s) U) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
    IsCompact (closure (Set.range (fun s : S =>
      mkOfCompact ⟨K.restrict (g s), ((hg_cont s).mono hKU).restrict⟩))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
  apply BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) M) (isCompact_closedBall _ _)
  · -- bounded: every value lies in `closedBall 0 M`
    rintro f y ⟨s, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right, mkOfCompact_apply]
    exact hg_bd s y.1 (hKU y.2)
  · -- equicontinuous: the non-convex equicontinuity lemma + subtype transfer
    classical
    set F_bcf : S → (K →ᵇ ℂ) :=
      fun s => mkOfCompact ⟨K.restrict (g s), ((hg_cont s).mono hKU).restrict⟩ with hFbcf
    have hequi_on : UniformEquicontinuousOn g K :=
      uniformEquicontinuousOn_of_bounded_analyticOn_of_compact hU hKcpt hKU hMnn hg_an hg_bd
    have hFbcf_fn : Equicontinuous (fun s : S => (⇑(F_bcf s) : K → ℂ)) :=
      (equicontinuous_restrict_iff g).mpr hequi_on.equicontinuousOn
    let u : ↥(Set.range F_bcf) → S := fun x => Classical.choose x.2
    have hu_spec : ∀ x : ↥(Set.range F_bcf), F_bcf (u x) = x.val :=
      fun x => Classical.choose_spec x.2
    have hcomp : (fun x : ↥(Set.range F_bcf) => (⇑x.val : K → ℂ)) =
        (fun s : S => (⇑(F_bcf s) : K → ℂ)) ∘ u := by
      funext x y; simp only [Function.comp]; rw [hu_spec x]
    have hrange : Equicontinuous (fun x : ↥(Set.range F_bcf) => (⇑x.val : K → ℂ)) := by
      rw [hcomp]; exact hFbcf_fn.comp u
    exact hrange

namespace BddHol

/-- **Restriction is a compact operator for a general (non-convex) compact `K ⋐ U`.** The
convexity-free generalization of `BddHol.isCompactOperator_restrictCLM`: for `U` open and `K ⊆ U`
compact (no `Convex ℝ K`), `restrictCLM : BddHol U →L[ℂ] (K →ᵇ ℂ)` is a compact operator. Same Montel
reduction (`isCompactOperator_iff_isCompact_closure_image_closedBall`), now feeding the non-convex
atom `isCompact_closure_restrict_bddHolo_of_compact`. This unblocks `DiskOverlapData` for cross-chart
overlaps, whose chart-images are not convex. -/
theorem isCompactOperator_restrictCLM_of_compact {U K : Set ℂ} [CompactSpace K]
    (hU : IsOpen U) (hKcpt : IsCompact K) (hKU : K ⊆ U) :
    IsCompactOperator (restrictCLM (U := U) hKU) := by
  show IsCompactOperator (⇑(restrictCLM (U := U) hKU).toLinearMap)
  rw [isCompactOperator_iff_isCompact_closure_image_closedBall
    (restrictCLM (U := U) hKU).toLinearMap (one_pos)]
  have hatom := isCompact_closure_restrict_bddHolo_of_compact hU hKcpt hKU
    (M := (1 : ℝ)) zero_le_one
    (S := ↥(Metric.closedBall (0 : BddHol U) 1))
    (g := fun s => (s : BddHol U).toFun)
    (hg_an := fun s => (s : BddHol U).analyticOn)
    (hg_bd := fun s z hz => by
      have hs : ‖(s : BddHol U)‖ ≤ 1 := by
        have := s.2
        rwa [Metric.mem_closedBall, dist_zero_right] at this
      exact le_trans ((s : BddHol U).norm_toFun_le hz) hs)
    (hg_cont := fun s => (s : BddHol U).analyticOn.continuousOn)
  convert hatom using 3
  ext φ
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, by rwa [Metric.mem_closedBall, dist_zero_right]⟩, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨(s : BddHol U), by
      have := s.2; rwa [Metric.mem_closedBall, dist_zero_right] at this, rfl⟩

end BddHol

end Jacobians.Dolbeault
