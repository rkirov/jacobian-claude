# Preimage-cycle lift — completion plan

Continuation plan for `exists_preimageCycle_of_off_branchLocus`
(`Jacobians/TracePullback.lean`), the geometric heart of the Jacobian
pushforward∘pullback = degree identity. This is the "§3 / loop-lifting machinery"
referenced throughout the codebase. Written 2026-05-30 after sub-piece A landed.

## Goal

`exists_preimageCycle_of_off_branchLocus (f hf hnonconst) (δ) (hδ : IsClosedSmoothLoop δ)
(havoid : ∀ t, δ t ∉ branchLocus f) : Nonempty (PreimageCycle f hf δ)`.

A `PreimageCycle` bundles: `n`, `loops : Fin n → ℝ → X`, `loops_smooth` (each
`IsClosedSmoothLoop`), `coeffs : Fin n → ℤ`, `sheets : ℕ`, and the two identities
- `pullback_eq : ambientPullbackJac f hf (periodVec δ) = ∑ i, coeffs i • periodVec (loops i)`
- `pushforward_eq : ∑ i, coeffs i • periodVec (f ∘ loops i) = (sheets : ℤ) • periodVec δ`.

## Status

- **A — continuous path-lift: DONE, sorry-free** (`exists_continuous_lift_off_branchLocus`,
  commit `32d435e`). `δ` off-branch lifts through the proven covering via Mathlib's
  `IsCoveringMap.liftPath`, repackaged to `ℝ → X` with `Set.projIcc`. `#print axioms` =
  `[propext, Classical.choice, Quot.sound]`. (Added `import Mathlib.Topology.Homotopy.Lifting`.)
- **B — smoothness of the lift: DONE, sorry-free**
  (`differentiableAt_chart_lift_of_notMem_criticalSet`). A continuous lift `Γ` of `δ`
  through a non-critical point is chart-pullback-differentiable wherever `δ` is.
  Proof exactly as planned: two-sided local inverse `g` at `Γ t₀`, `Γ =ᶠ g∘δ` near `t₀`
  (no lift-uniqueness needed), `G∘d` chart factorization, `g` holomorphic ⇒ `ℝ`-diff via
  `writtenInExtChartAt`+`restrictScalars`. `#print axioms` = `[propext, Classical.choice,
  Quot.sound]`. Compiled essentially first-try (mirrors `IsClosedSmoothLoop.comp`).

## Proven infrastructure to build on

- **Covering**: `isCoveringMap_restrictPreimage_compl_branchLocus` (PeriodLattice) — a genuine
  `IsCoveringMap` of `(univ \ branchLocus f).restrictPreimage f` on subtypes. Mathlib
  `IsCoveringMap.liftPath` / `liftPath_trans` / `liftPath_apply_one_eq_of_homotopicRel`
  (`Mathlib.Topology.Homotopy.Lifting`). NB: `IsCoveringMap` unfolds to a Pi type, so
  dot-notation fails — use explicit `IsCoveringMap.liftPath cov …`.
- **Local sections**: `exists_twoSided_localInverse` (TraceForm.lean) — at any non-critical
  `x₀`, a holomorphic `g` with `f∘g=id` on open `V∋f x₀`, `g∘f=id` near `x₀`, `g(f x₀)=x₀`,
  `g` `C^ω` on `V`. Also `exists_holo_localInverse_of_notMem_criticalSet`, `isLocalHomeoOffCritical`.
- **Fibre finiteness**: `fiber_finite_off_branchLocus` (PeriodLattice) — `(f⁻¹'{y}).Finite` off-branch
  (= the sheet count, classically `deg f`).
- **Line-integral change of variables**: `lineIntegral_pullback` (LineIntegral.lean, PROVEN),
  `periodVec_comp_eq_lineIntegral_pullback`, `periodVec_pushforward` (PeriodLattice).
- **Trace off-branch**: `traceForm_toFun_of_notMem_branchLocus` (TraceForm.lean) — off-branch
  `traceForm = traceFun = ∑ sheets sheetPullback`.
- **Chart chain-rule template**: `pathSpeed_comp_eq_mfderiv` (LineIntegral.lean:492-576) — the
  `chartY ∘ map ∘ chartX.symm` differentiability pattern, to be mirrored in B.

## Remaining steps

### B — smoothness of the lift (tractable, ~100 lines)
Lemma `differentiableAt_chart_lift_of_notMem_criticalSet`:
given `Γ` continuous, `∀ᶠ t in 𝓝 t₀, f (Γ t) = δ t`, `Γ t₀ ∉ criticalSet f`, and
`DifferentiableAt ℝ ((chartAt ℂ (δ t₀)).toFun ∘ δ) t₀`, conclude
`DifferentiableAt ℝ ((chartAt ℂ (Γ t₀)).toFun ∘ Γ) t₀`.
Proof: get `g` from `exists_twoSided_localInverse` at `Γ t₀`. **`Γ =ᶠ[𝓝 t₀] g∘δ`** follows
directly from `g∘f=id` near `Γ t₀` + continuity of `Γ` + `f∘Γ=δ` — **no lift-uniqueness needed**.
Then `(chartAt Γt₀)∘Γ =ᶠ G∘d` where `G = (chartAt Γt₀)∘g∘(chartAt δt₀).symm` (`g` in charts) and
`d = (chartAt δt₀)∘δ`; chain rule `(DifferentiableAt G (d t₀)).comp _ hδ_diff`, then
`congr_of_eventuallyEq`. The one boilerplate sub-step is `DifferentiableAt ℝ G (d t₀)` — `g`
holomorphic ⇒ `ℝ`-differentiable in charts: extract from `pathSpeed_comp_eq_mfderiv` steps 4-7
(`hf_mdiff.differentiableWithinAt_writtenInExtChartAt` + `range_eq_univ` + `restrictScalars`;
note the `IsScalarTower ℝ ℂ ℂ` diamond worked around there via manual `HasFDerivAt.restrictScalars`).

### C — monodromy → closed loops (THE CRUX)
From each fibre point `e ∈ f⁻¹'{δ 0}`, lift `δ` (A+B). The lift endpoints realise the monodromy
permutation `σ` (`Γ_e 1 = the next sheet`); concatenate `Γ_e * Γ_{σe} * …` over `σ`'s orbit
(`liftPath_trans`) until returning to `e` — that is one closed loop. `n` = #orbits, `coeffs` from
orbit lengths, `sheets` = `#(f⁻¹'{δ 0})`.
**Genuine difficulty — seam/endpoint smoothness:** A's `Set.projIcc`-clamped lift is *constant*
outside `[0,1]`, so it is NOT differentiable at the seam. Closing into an `IsClosedSmoothLoop`
needs the smoothness at the concatenation seams, which comes from the monodromy endpoint-match
(`liftPath_apply_one_eq_of_homotopicRel` / uniqueness of lifts) together with `δ`'s own
loop-smoothness at `δ 0 = δ 1`. This is the hard, delicate part — budget the most time here.

### D — pullback_eq (projection formula)
`ambientPullbackJac f hf (periodVec δ) = ∑ coeffs • periodVec (loops)`. Per basis component `i`:
`(Tᵀ (periodVec δ))_i = ∫_δ traceForm(ωᵢ^X)` (since `ambientPullbackJac = Tᵀ`, `T` = `traceForm`
matrix, and `lineIntegral` is linear) `= ∑_loops ∫_{loop} ωᵢ^X`. The last `=` is the projection
formula: off-branch `traceForm(ωᵢ) = ∑_sheets sheetPullback`, and `lineIntegral_pullback` turns
each sheet's `∫_δ (pullback along section)` into `∫_{section∘δ} ωᵢ`; the sheet-sections∘δ assemble
(monodromy) into the `loops`. **Key: `δ` stays off-branch, so this needs NO branch-point
continuity** — unlike `traceForm_comp` (see below). The sheet-sum ↔ loop-sum glue is the monodromy
bookkeeping from C.

### E — pushforward_eq
`∑ coeffs • periodVec (f ∘ loops) = sheets • periodVec δ`. Each `f ∘ loop` is `δ` traversed
(orbit length) times; `periodVec (f∘loop) = (orbit length) • periodVec δ` via `periodVec_pushforward`
+ `periodVec_concat`; summing with `coeffs` gives `sheets • periodVec δ`.

### F — assemble `PreimageCycle` from B–E and conclude `Nonempty`.

## Separately recorded: `traceForm_comp` is infrastructure-blocked

The other open trace gap, `traceForm_comp` (TraceForm.lean, the `(g∘f)₊ = g₊∘f₊` functoriality
law), is NOT a quick win. Both a density+continuity proof and the `exists_traceForm` framework
need `ContinuousAt` of an opaque `traceForm.choose`'s *coefficient* at branch points — i.e. a
general **cotangent-hom-bundle coefficient-continuity extractor** (`contMDiffAt_hom_bundle`-style,
~40-80 lines of bundle work). Two subagents stalled there. Unlike D above, `traceForm_comp` cannot
avoid branch-point continuity. `traceForm_id` IS done (commit `2c2ad32`) because `branchLocus(id)=∅`.
