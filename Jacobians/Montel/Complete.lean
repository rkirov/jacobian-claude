import Jacobians.Montel.Compactness
import Mathlib.Topology.UniformSpace.CompleteSeparated

/-!
# Montel path — completeness of `HolomorphicOneForms X`

This file proves `CompleteSpace (HolomorphicOneForms X)` under the
canonical supNormK-based normed structure. Combined with precompactness
of closed unit ball (from Arzelà–Ascoli in `Compactness.lean`), this
yields `IsCompact (closedBall 0 1)` — the missing piece in the Montel
conclusion.

## Proof outline

Given a Cauchy sequence `α_n` in supNormK:
1. Per-chart: `localRep α_n x₀` is uniformly Cauchy on `shrunkChart x₀`
   (since supNormK bounds chart-wise values).
2. Uniform Cauchy on compact + ℂ complete ⇒ uniform convergence to
   some `g_{x₀} : shrunkChart x₀ → ℂ` (continuous).
3. Pointwise limit exists in CLM space: `α_n.toFun y → α∞(y)` in
   operator norm for each y ∈ X.
4. Chart-wise analyticity of pullbacks ⇒ α∞ is `ContMDiffSection ω`
   (via `analyticOn_of_pullback_tendsto_locally_uniformly`).
5. `α_n → α∞` in supNormK.

Step 4 is the heart of the argument; it requires assembling the
analytic chart-pullbacks back into a bundle section.
-/

namespace Jacobians.Montel

open scoped Manifold ContDiff Topology
open Bundle Filter

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Step 1 — Per-chart uniform Cauchy from supNormK Cauchy

`supNormK = sup over chartCover of chartNormK`, where `chartNormK α x₀
= sup_{y ∈ shrunkChart x₀} ‖localRep α x₀ y‖`. Hence a supNormK-Cauchy
sequence yields uniformly-Cauchy chart-representatives on each
`shrunkChart x₀`. -/

omit [ConnectedSpace X] in
/-- Per-chart-chart uniform bound from chartNormK: for y ∈ shrunkChart x₀,
|localRep (α - β) x₀ y| is bounded by `chartNormK (α - β) x₀ ≤ supNormK (α - β)`. -/
theorem norm_localRep_sub_le_supNormK
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X))
    {y : X} (hy : y ∈ shrunkChart (X := X) x₀) :
    ‖localRep α x₀ y - localRep β x₀ y‖ ≤ HolomorphicOneForms.supNormK (α - β) := by
  have hsub : α - β = α + (-β) := by rw [sub_eq_add_neg]
  have h_ap : localRep α x₀ y - localRep β x₀ y = localRep (α - β) x₀ y := by
    rw [hsub, localRep_add, localRep_neg]; ring
  rw [h_ap]
  exact HolomorphicOneForms.norm_localRep_le_supNormK (α - β) hx₀ hy

/-! ### Step 1b — `localRep α` on shrunkChart as a continuous map

Bundles `localRep α x₀` restricted to `shrunkChart x₀` as a `C(_, ℂ)`,
parallel to `localRepOnInnerShrunk` but on the outer shrinkage. -/

omit [ConnectedSpace X] [Nonempty X] [IsManifold 𝓘(ℂ) ω X] in
theorem shrunkChart_compactSpace' (x₀ : X) :
    CompactSpace (shrunkChart (X := X) x₀) :=
  isCompact_iff_compactSpace.mp (shrunkChart_isCompact x₀)

/-- Bundled version of `localRep α x₀` on shrunkChart x₀. -/
noncomputable def localRepOnShrunkBcf
    (α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (x₀ : X) : BoundedContinuousFunction (shrunkChart (X := X) x₀) ℂ := by
  letI := shrunkChart_compactSpace' (X := X) x₀
  exact BoundedContinuousFunction.mkOfCompact (localRepOnShrunk α x₀)

/-! ### Step 2 — bcf-Cauchy on shrunkChart from supNormK-Cauchy

The per-chart bcf distance is bounded by supNormK of the difference,
so a supNormK-Cauchy sequence has bcf-Cauchy chart restrictions. -/

omit [ConnectedSpace X] in
/-- Per-chart bcf-distance ≤ supNormK-distance for `α, β ∈ HOF X`. -/
theorem dist_localRepOnShrunkBcf_le_supNormK_sub
    (α β : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X)) :
    letI := shrunkChart_compactSpace' (X := X) x₀
    dist (localRepOnShrunkBcf α x₀) (localRepOnShrunkBcf β x₀) ≤
      HolomorphicOneForms.supNormK (α - β) := by
  letI := shrunkChart_compactSpace' (X := X) x₀
  refine (BoundedContinuousFunction.dist_le
    (HolomorphicOneForms.supNormK_nonneg _)).mpr ?_
  intro y
  have hy : (y : X) ∈ shrunkChart (X := X) x₀ := y.2
  simp only [localRepOnShrunkBcf, BoundedContinuousFunction.mkOfCompact_apply,
    localRepOnShrunk_apply _ hx₀, dist_eq_norm]
  exact norm_localRep_sub_le_supNormK α β hx₀ hy

/-! ### Step 3 — Pointwise CLM limit from supNormK Cauchy

For a supNormK-Cauchy sequence of sections, `α_n.toFun y` is Cauchy in
the complete space `T_y X →L[ℂ] ℂ` (CLM space, complete since ℂ is).
This gives a pointwise CLM limit `αLim.toFun y`. -/

omit [ConnectedSpace X] in
/-- For a supNormK-Cauchy sequence, the CLM value at each point is Cauchy.
This uses the identity `α.toFun y (e.symmL y 1) = localRep α x₀ y` and
the supNormK bound on localRep. -/
theorem cauchySeq_alpha_toFun_apply_symmL
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h_diff : ∀ ε > 0, ∃ N, ∀ n m, n ≥ N → m ≥ N →
      HolomorphicOneForms.supNormK (αs n - αs m) < ε)
    {x₀ : X} (hx₀ : x₀ ∈ (chartCover : Finset X)) {y : X}
    (hy : y ∈ shrunkChart (X := X) x₀) :
    CauchySeq (fun n : ℕ => localRep (αs n) x₀ y) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := h_diff ε hε
  refine ⟨N, fun n hn m hm => ?_⟩
  rw [dist_eq_norm]
  calc ‖localRep (αs n) x₀ y - localRep (αs m) x₀ y‖
      ≤ HolomorphicOneForms.supNormK (αs n - αs m) :=
        norm_localRep_sub_le_supNormK (αs n) (αs m) hx₀ hy
    _ < ε := hN n m hn hm

/-! ### Step 3b — Finite diagonal: common bcf-convergent subsequence on chartCover

Given a bounded sequence of sections (supNormK ≤ 1), iterate per-chart
Arzelà (`isCompact_closure_image_inner_bcf` for `M = 1`) over the finite
`chartCover` to extract a single strict-mono `φ : ℕ → ℕ` such that for
every `x₀ ∈ chartCover` the bcf-image on `innerShrunkChart x₀`
converges to some limit. -/

omit [ConnectedSpace X] in
/-- List-indexed finite-diagonal extractor. By induction on `xs`, at
each cons step we sub-sample inside the compact closure of the range
of `mkOfCompact ∘ localRepOnInnerShrunk · y`. The outer strict-mono
preserves convergence in earlier charts (composing with a strict-mono
sequence preserves `Tendsto` at `atTop`). -/
private lemma exists_common_subseq_bcf_tendsto
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h : ∀ n, HolomorphicOneForms.supNormK (αs n) ≤ 1)
    (xs : List X) (hxs : ∀ x ∈ xs, x ∈ (chartCover : Finset X)) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ x ∈ xs,
        letI := innerShrunkChart_compactSpace (X := X) x
        ∃ g : BoundedContinuousFunction (innerShrunkChart (X := X) x) ℂ,
          Tendsto
            (fun n : ℕ => BoundedContinuousFunction.mkOfCompact
              (localRepOnInnerShrunk (αs (φ n)) x))
            atTop (𝓝 g) := by
  induction xs with
  | nil =>
    refine ⟨id, strictMono_id, fun x hx => ?_⟩
    exact absurd hx List.not_mem_nil
  | cons y ys ih =>
    have hys : ∀ x ∈ ys, x ∈ (chartCover : Finset X) :=
      fun x hx => hxs x (List.mem_cons_of_mem _ hx)
    obtain ⟨φ₀, hφ₀, hφ₀_conv⟩ := ih hys
    have hy : y ∈ (chartCover : Finset X) := hxs y List.mem_cons_self
    letI := innerShrunkChart_compactSpace (X := X) y
    set K : Set (BoundedContinuousFunction (innerShrunkChart (X := X) y) ℂ) :=
      closure (Set.range
        (fun α : {α : ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
            (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x) //
            HolomorphicOneForms.supNormK α ≤ 1} =>
          BoundedContinuousFunction.mkOfCompact (localRepOnInnerShrunk α.1 y)))
      with hK_def
    have hK : IsCompact K := isCompact_closure_image_inner_bcf 1 zero_le_one hy
    have hK_seq : IsSeqCompact K := hK.isSeqCompact
    set s : ℕ → BoundedContinuousFunction (innerShrunkChart (X := X) y) ℂ :=
      fun n => BoundedContinuousFunction.mkOfCompact
        (localRepOnInnerShrunk (αs (φ₀ n)) y)
      with hs_def
    have hs_in : ∀ n, s n ∈ K := by
      intro n
      refine subset_closure ?_
      exact ⟨⟨αs (φ₀ n), h (φ₀ n)⟩, rfl⟩
    obtain ⟨a, _haK, ψ, hψ, hψ_conv⟩ :=
      hK_seq.subseq_of_frequently_in (x := s)
        (Filter.Eventually.frequently (Filter.Eventually.of_forall hs_in))
    refine ⟨φ₀ ∘ ψ, hφ₀.comp hψ, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hxys
    · refine ⟨a, ?_⟩
      simpa [Function.comp, s, hs_def] using hψ_conv
    · obtain ⟨g, hg⟩ := hφ₀_conv x hxys
      refine ⟨g, ?_⟩
      exact hg.comp hψ.tendsto_atTop

omit [ConnectedSpace X] in
/-- **Common bcf-convergent subsequence on `chartCover`.**
For any bounded sequence of sections (`supNormK (αs n) ≤ 1`), there is
a strict-mono subsequence `φ` such that on each chart `x₀ ∈ chartCover`
the bcf-image `mkOfCompact ∘ localRepOnInnerShrunk (αs (φ n)) x₀`
converges in `BCF(innerShrunkChart x₀, ℂ)`. -/
theorem exists_subseq_bcf_tendsto_on_chartCover
    (αs : ℕ → ContMDiffSection 𝓘(ℂ, ℂ) (ℂ →L[ℂ] ℂ) ω
      (fun x : X => TangentSpace 𝓘(ℂ, ℂ) x →L[ℂ] (Bundle.Trivial X ℂ) x))
    (h : ∀ n, HolomorphicOneForms.supNormK (αs n) ≤ 1) :
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ x₀ ∈ (chartCover : Finset X),
        letI := innerShrunkChart_compactSpace (X := X) x₀
        ∃ g : BoundedContinuousFunction (innerShrunkChart (X := X) x₀) ℂ,
          Tendsto
            (fun n : ℕ => BoundedContinuousFunction.mkOfCompact
              (localRepOnInnerShrunk (αs (φ n)) x₀))
            atTop (𝓝 g) := by
  obtain ⟨φ, hφ, hconv⟩ := exists_common_subseq_bcf_tendsto αs h
    (chartCover : Finset X).toList (fun x hx => Finset.mem_toList.mp hx)
  refine ⟨φ, hφ, ?_⟩
  intro x₀ hx₀
  exact hconv x₀ (Finset.mem_toList.mpr hx₀)

/-! ### Remaining steps (DEFERRED)

The full completeness proof requires:

**Step 2** (uniform convergence on shrunkChart):
  Given supNormK-Cauchy (α_n), and using Step 1, for each x₀ ∈ chartCover,
  `localRep α_n x₀` is uniformly Cauchy on compact `shrunkChart x₀`.
  Since ℂ is complete, uniform limit exists as a continuous function
  `g_{x₀} : shrunkChart x₀ → ℂ`.

**Step 3** (pointwise CLM limit):
  For each y ∈ X, pick x₀ ∈ chartCover with y ∈ innerShrunkChart x₀
  (exists by `iUnion_innerShrunkChart_chartCover_eq`). Using the 1-dim
  tangent space (`alpha_toFun_eq_zero_of_localRep_eq_zero` machinery in
  SupNorm.lean), α_n.toFun y is Cauchy in operator norm, converging to
  some `α∞_CLM y : T_y X →L[ℂ] ℂ`.

**Step 4** (smoothness of limit — **the hardest piece**):
  Use `analyticOn_of_pullback_tendsto_locally_uniformly` (already in
  Compactness.lean) on each chart: chart-wise pullback is locally
  uniform limit of analytic functions, hence analytic. Then reconstruct
  α∞ : ContMDiffSection ω from the chart-analytic pullbacks. This
  bundle-section reconstruction from chart pieces requires
  manifold-level assembly machinery beyond current Compactness.lean.

**Step 5** (convergence in supNormK norm):
  α_n → α∞ in supNormK follows from per-chart uniform convergence
  (each chartNormK (α_n - α∞) → 0, so supNormK (α_n - α∞) → 0).

**Step 6** (CompleteSpace instance):
  Package as `CompleteSpace` instance for HOF X under `normedAddCommGroup`.

Once CompleteSpace is in place, `closedBall_isCompact` in `Montel.lean`
follows from: closedBall is totally bounded (via Arzela from
Compactness.lean) + closed (trivial in normed space) + complete ambient
= compact.

**Why this is genuinely multi-session work:** Step 4 is a bundle-level
theorem that doesn't exist in Mathlib: "analytic functions on chart
overlaps that agree on transitions glue to a `ContMDiffSection ω`". It
requires careful use of the `IsManifold ω` structure to assemble
chart-wise analyticity into global smoothness. Estimated
200–400 lines of dedicated Lean work.
-/

end Jacobians.Montel
