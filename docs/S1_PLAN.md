# S1 closure plan — `exists_smoothPath_family`

_Target: `Jacobians/PeriodLattice.lean:345` — the highest-leverage sorry.
Closing it makes `ofCurve_contMDiff` (the Abel–Jacobi map is holomorphic)
fully sorry-free, since the entire `OfCurveAnalyticitySkeleton` already
reduces to it (verified axiom-clean modulo S1)._

## What S1 asks for

A single family `sp : X → X → ℝ → X` with, for all `P Q P₀ A`:
1. `IsSmoothPath P Q (sp P Q)` — a C¹ (chart-pullback differentiable),
   integrable path from `P` to `Q`;
2. **basepoint change mod lattice**:
   `[periodVec (sp P₀ A)] = [periodVec (sp P A)] + [periodVec (sp P₀ P)]`
   in `(Fin g → ℂ) / Λ`.

(The provably-false third conjunct — unquotiented smoothness — was
removed 2026-05-28; see `project_smoothpath_math_error`.)

## The key architectural insight

`concat γ₁ γ₂` glues `γ₁(2t)` on `[0,½]` to `γ₂(2t−1)` on `[½,1]`. For the
`diff` field (C¹) at the junction `t=½`, the **left and right velocities
must agree**. For two arbitrary smooth paths they don't — so a *general*
`IsSmoothPath.concat` is false.

The fix (already used in the one proven 2-piece junction lemma,
`isClosedSmoothLoop_concat_ChartBallPathSmooth_reverse_smoothPathSmooth`):
reparametrize every piece by **`smoothStep01`**, whose derivative is `0` at
both endpoints (`smoothStep01_deriv_zero/_one`). Then `pathSpeed = 0` at
every junction on both sides, both one-sided derivatives are `0`, and they
glue to a genuine `HasDerivAt … 0`. So:

> **Every hop in the global construction must be smoothstep-reparametrized
> (zero endpoint velocity).** Then concatenation preserves C¹.

## Existing assets (proven, axiom-clean — do not re-derive)

- `smoothStep01` C¹ calculus: `_hasDerivAt_zero/_one` (deriv 0 at ends),
  `_differentiable`, `_monotoneOn_Icc`, `_image_Icc`, `_mem_unit`,
  `pathSpeed_smoothStep01_comp_eq` (chain rule).  `SmoothPath.lean`.
- `ChartBallPathSmooth Q₀ Q` (smoothstep-reparametrized chart-ball hop)
  and `isSmoothPath_ChartBallPathSmooth` — a single hop is a smooth path,
  given `Q ∈ chart.source` + affine-segment-in-`chart.target`.
  `OfCurveAnalyticitySkeleton.lean:922`.
- The 2-piece junction lemma (closed+cont+**diff**+integrable) —
  `…:1426`. This is the template to generalize.
- `concat` / `reverse` reparam algebra and `pathSpeed_concat_left/right`,
  `pathSpeed_reverse`.  `LineIntegral.lean`.
- period algebra: `periodVec_concat`, `periodVec_reverse`,
  `mk_periodVec_eq_of_endpoints`, `periodVec_sub_mem_truePeriodLattice`,
  `mk_periodVec_concat_eq_add`.  `PeriodLattice.lean`.
- `exists_chartCover` — Lebesgue-number chart cover of `[0,1]` for any
  continuous path.  `SmoothPath.lean:134` (currently dead code; repurpose).
- `PathConnectedSpace X` instance is automatic from the ambient typeclasses.

## Decomposition (intermediate lemmas — "one sorry → many")

The CI guard (`scripts/check_sorries.py N`) tracks the count; bump `N` as
sub-lemmas are scaffolded, drive it back to 8 as they close.

### Sub-lemma A — general junction concat (keystone, reusable)
```
IsSmoothPath.concat {P Q R} {γ₁ γ₂}
  (h₁ : IsSmoothPath P Q γ₁) (h₂ : IsSmoothPath Q R γ₂)
  (hv₁ : pathSpeed γ₁ 1 = 0) (hv₂ : pathSpeed γ₂ 0 = 0) :
  IsSmoothPath P R (concat γ₁ γ₂)
```
Generalize the 4 fields of the 2-piece junction proof. closed/cont are
easy; `diff` is the `Iic/Ici` HasDerivWithinAt glue (both 0 by `hv₁/hv₂`);
`integrable` reuses the substitution machinery. **~250–350 LOC.**

### Sub-lemma B — chart-ball cover with in-target hops
Strengthen `exists_chartCover` so consecutive anchor points
`x₀,…,x_n` along a continuous reference path satisfy, for each hop,
`x_{k+1} ∈ chart(x_k).source` **and** the affine segment between their
chart images stays in `chart(x_k).target`. Needs a Lebesgue number on
chart-coordinate **balls** (convex), not just sources. **~80–150 LOC.**

### Sub-lemma C — n-piece glued path
Define `sp P Q` as the right-fold concat of `ChartBallPathSmooth`-style
hops along the cover of `somePath P Q`. Prove `IsSmoothPath P Q (sp P Q)`
by induction on the number of pieces using A (every hop has zero endpoint
velocity, so every junction is C¹). **~150–250 LOC.**

### Sub-lemma D — basepoint-change cocycle
For the concrete `sp` from C, prove
`[periodVec (sp P₀ A)] = [periodVec (sp P A)] + [periodVec (sp P₀ P)]`
by exhibiting `concat (sp P₀ P) (concat (sp P A) (reverse (sp P₀ A)))`
(or equivalent) as an `IsClosedSmoothLoop` whose `periodVec ∈ Λ`, via the
proven `periodVec_concat/_reverse` + `mk_periodVec_eq_of_endpoints`.
Must NOT route through `smoothPath` (= `sp`) to avoid circularity.
**~150–300 LOC.**

### Assembly
`exists_smoothPath_family := ⟨sp, fun P Q => C, fun P P₀ A => D⟩`.

## Order of attack
A (keystone, unblocks C) → B → C → D → assemble. Build each as a
standalone proven lemma, verify `#print axioms` shows no `sorryAx`, commit,
then proceed. Total realistic: **~480–900 LOC, multi-session.** The hard
*math* (chart-frame covariance, smoothstep C¹, reparam invariance) is
already done; what remains is Lean induction/bookkeeping over the glue.
