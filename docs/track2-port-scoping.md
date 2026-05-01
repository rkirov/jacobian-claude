# Track 2 Port Scoping: `ProjectiveLine` and `Elliptic`

This document scopes the port of the `ProjectiveLine` and `Elliptic ω₁ ω₂` curve
constructions from [`mrdouglasny/jacobian-challenge`][src-repo] into
[`rkirov/jacobian-claude`][tgt-repo] (this repo). Both repos target Lean 4 /
Mathlib at commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`.

[src-repo]: https://github.com/mrdouglasny/jacobian-challenge
[tgt-repo]: https://github.com/rkirov/jacobian-claude

---

## Context: the carrier gap

The two repos differ in their `HolomorphicOneForm[s]` carrier.

| Repo | Carrier |
|------|---------|
| **TARGET** (`rkirov`) | `ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (TangentSpace _ →L[ℂ] Bundle.Trivial X ℂ)` — Mathlib bundle sections of the cotangent bundle. Defined in `Jacobians/Genus.lean` lines 30–55. |
| **SOURCE** (`mrdouglasny`) | `↥(holomorphicOneFormSubmodule X)` — a hand-rolled submodule of `X → ℂ → ℂ` cut out by `IsHolomorphicOneFormCoeff ∧ SatisfiesCotangentCocycle ∧ IsZeroOffChartTarget`. Defined in [`Jacobians/RiemannSurface/OneForm.lean`][src-oneform]. |

[src-oneform]: https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/RiemannSurface/OneForm.lean

These types are **not defeq**. Any theorem that mentions the 1-form space needs
translation; theorems that only mention the manifold structure port directly.

---

## 1. `ProjectiveLine` port

### Source files read

- [`Jacobians/ProjectiveCurve/Line.lean`][src-line] — 302 LOC, the main manifold file
- [`Jacobians/ProjectiveCurve/Line/Genus.lean`][src-line-genus] — 36 LOC
- [`Jacobians/ProjectiveCurve/Line/OneForm.lean`][src-line-oneform] — 35 LOC

[src-line]: https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Line.lean
[src-line-genus]: https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Line/Genus.lean
[src-line-oneform]: https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Line/OneForm.lean

### 1a. Carrier-free part — ports directly

Everything in `Line.lean` is carrier-free. The full block:

```
abbrev ProjectiveLine : Type := OnePoint ℂ

chart0 : OpenPartialHomeomorph ProjectiveLine ℂ  -- identity on ℂ ⊂ OnePoint ℂ
chart1 : OpenPartialHomeomorph ProjectiveLine ℂ  -- ∞ ↦ 0, z ↦ 1/z

instance : ChartedSpace ℂ ProjectiveLine          -- two-chart atlas
instance : IsManifold 𝓘(ℂ) ω ProjectiveLine      -- transition 1/z is analytic

stereographic : ProjectiveLine ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
```

This is ~270 LOC of manifold infrastructure. The key Mathlib ingredients are
already the same in both repos:
- `OnePoint.isOpenEmbedding_coe` for `chart0`
- `Filter.tendsto_inv₀_cobounded` for continuity of `chart1` at `∞`
- `contDiffOn_inv` for analyticity of the `1/z` transition
- `onePointEquivSphereOfFinrankEq` for `stereographic`

The `ChartedSpace` and `IsManifold` proofs discharge via `isManifold_of_contDiffOn`
checking four 2×2 transition-map cases (id, 1/z, 1/z, id). Mechanically
identical for both repos.

Mathlib-level instances on `OnePoint ℂ` that land automatically (no proof needed):
`TopologicalSpace`, `T2Space` (via `LocallyCompactSpace ℂ`), `CompactSpace`,
`ConnectedSpace`, `Nonempty`.

**Assessment:** copy-paste of `Line.lean` with namespace adjustments. Estimated
**mechanical** work (no novel math).

### 1b. Carrier-sensitive part — `genus_ProjectiveLine_eq_zero`

**mrdouglasny's proof** (`Line/Genus.lean`): routes through
`AX_genus_eq_zero_iff_homeo` (a uniformization sorry-axiom) applied to the
`stereographic` homeomorphism:
```lean
theorem genus_projectiveLine_eq_zero :
    genus ProjectiveLine = 0 :=
  AX_genus_eq_zero_iff_homeo.mpr ⟨ProjectiveLine.stereographic⟩
```

**kirov's situation:** `Jacobians/Genus.lean` already carries
`genus_eq_zero_iff_homeo` as a `sorry`:
```lean
lemma genus_eq_zero_iff_homeo {X : ...} :
    genus X = 0 ↔ Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
  sorry
```
So the same one-liner would close the goal, but at the cost of that sorry.

**Direct proof for kirov's bundle-section carrier (no new sorry, genuine math):**

The classical fact is $H^0(\mathbb{P}^1, \Omega^1) = 0$: the cotangent bundle on
$\mathbb{P}^1$ is $\mathcal{O}(-2)$, which has no global holomorphic sections.

In terms of kirov's `ContMDiffSection` carrier, the argument is:

1. Let `α : HolomorphicOneForms ProjectiveLine`, so `α.toFun x : TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ`.
2. In `chart0` (the standard affine chart over `ℂ`), write `a(z) := α.toFun (↑z) 1 : ℂ`.
   Since `α` is a `ContMDiffSection`, `a` is holomorphic on all of `ℂ` (it's the
   pullback to the chart).
3. The `chart0–chart1` transition is `w = 1/z`. The standard cotangent-bundle
   transformation law gives: in chart1, the coefficient is `b(w) = a(1/w) · (-1/w²)`.
   (Derivative of `z = 1/w` w.r.t. `w` is `−1/w²`; pullback reverses.)
4. `b(w)` must extend holomorphically to `w = 0` (since `α` is a section at `∞`).
   But `b(w) = -a(1/w)/w²`. As `w → 0`, `1/w → ∞`; for `b` to be bounded near
   `w = 0`, we need `a(1/w) = O(w²)` as `w → 0`, i.e. `a(z) = O(1/z²)` as `z → ∞`.
5. By Liouville (`Complex.liouville_theorem` / `Differentiable.apply_eq_const_of_compactSpace`
   on the extended function), a holomorphic `a : ℂ → ℂ` with `a(z) → 0` as `z → ∞`
   must be identically zero.
6. Hence `α = 0`.

**Mathlib lemmas needed for the direct proof:**
- `Differentiable.apply_eq_const_of_compactSpace` or `MDifferentiable.exists_eq_const_of_compactSpace`
  (exists in Mathlib at this commit — used by mrdouglasny for the Elliptic proof).
- The chart-transition-derivative computation for `ProjectiveLine.chart0 ≫ₕ chart1`:
  need `fderiv ℂ (chart1.toFun ∘ chart0.symm) z 1 = -1/z²` (or equivalent).
  This is not in Mathlib; ~10-20 LOC to derive from `fderiv` on `Inv.inv`
  (`Complex.hasDerivAt_inv`).
- `Differentiable.eq_zero_of_tendsto_zero` or equivalent Liouville variant:
  a holomorphic function on all of `ℂ` that decays at infinity is zero.
  Likely derivable from `Complex.liouville_theorem` +
  `IsConnected.eq_const_of_analyticOn` via a Riemann extension argument.
  This is the hardest step (~50-100 LOC), and it is **genuinely new mathematical
  content** — not present in Mathlib at this commit.

**Practical recommendation:** port the `ProjectiveLine` manifold construction
without touching genus. Use `genus_eq_zero_iff_homeo` (the existing kirov sorry)
to get `genus_ProjectiveLine_eq_zero` immediately. File a TODO for the direct
Liouville proof as a future sorry-elimination task.

### 1c. `Subsingleton (HolomorphicOneForms ProjectiveLine)` analog

mrdouglasny's `Line/OneForm.lean` derives `Subsingleton (HolomorphicOneForm ProjectiveLine)`
from `genus = 0` + finite-dimensionality. In kirov:

```lean
instance : Subsingleton (HolomorphicOneForms ProjectiveLine) :=
  Module.finrank_zero_iff.mp genus_ProjectiveLine_eq_zero
```

(`HolomorphicOneForms` is already `FiniteDimensional` via `HolomorphicForms.lean`.)
This is carrier-insensitive once `genus = 0` is established. ~5 LOC.

### 1d. Target file layout in kirov

```
Jacobians/
  ProjectiveLine.lean   ← NEW (flat layout, no nesting)
```

Content:
- `namespace Jacobians` (matching kirov's flat namespace style)
- `ProjectiveLine`, `chart0`, `chart1`, `ChartedSpace`, `IsManifold`,
  `stereographic` — ported from `Line.lean`
- `genus_ProjectiveLine_eq_zero` — via `genus_eq_zero_iff_homeo`
- `instSubsingletonHolomorphicOneFormsProjectiveLine` — 5 LOC

No subdirectory `Jacobians/ProjectiveCurve/` needed; kirov uses a flat layout.

---

## 2. `Elliptic ω₁ ω₂` port

### Source files read

- [`Jacobians/ProjectiveCurve/Elliptic.lean`][src-elliptic] — 145 LOC
- [`Jacobians/ProjectiveCurve/Elliptic/OneForm.lean`][src-elliptic-oneform] — 260 LOC
- [`Jacobians/ProjectiveCurve/Elliptic/Genus.lean`][src-elliptic-genus] — 40 LOC
- [`Jacobians/AbelianVariety/ComplexTorus.lean`][src-complextorus] — 650 LOC
  (mrdouglasny's `ComplexTorus` plays the role of kirov's `ZLatticeQuotient`)

[src-elliptic]: https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Elliptic.lean
[src-elliptic-oneform]: https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Elliptic/OneForm.lean
[src-elliptic-genus]: https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Elliptic/Genus.lean
[src-complextorus]: https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/AbelianVariety/ComplexTorus.lean

### 2a. Carrier-free part — mostly reduces to `ZLatticeQuotient`

mrdouglasny defines:
```lean
abbrev Elliptic ω₁ ω₂ h : Type :=
  ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)
```
where `ComplexTorus V L := V ⧸ L.toAddSubgroup`.

kirov's `ZLatticeQuotient.lean` already provides exactly this structure for
`E ⧸ Λ.toAddSubgroup` with `[DiscreteTopology Λ] [IsZLattice ℝ Λ]`.
The definition in kirov would be:

```lean
noncomputable abbrev ellipticLattice (ω₁ ω₂ : ℂ)
    (h : LinearIndependent ℝ ![ω₁, ω₂]) : Submodule ℤ ℂ :=
  Submodule.span ℤ (Set.range (basisOfLinearIndependentOfCardEqFinrank h
    (by simp [Complex.finrank_real_complex])))

noncomputable def Elliptic (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) : Type :=
  ℂ ⧸ (ellipticLattice ω₁ ω₂ h).toAddSubgroup
```

The following instances are then **automatic from `ZLatticeQuotient`**:
- `AddCommGroup` — from `QuotientAddGroup`
- `TopologicalSpace` — from `QuotientAddGroup`
- `IsTopologicalAddGroup` — from quotient of topological group
- `T2Space` — from `QuotientAddGroup.instT2Space` (closed subgroup)
- `CompactSpace` — `Jacobians.ZLatticeQuotient.instCompactSpaceQuotient`
- `ChartedSpace ℂ` — `Jacobians.ZLatticeQuotient.chartedSpaceQuotient`
- `IsManifold 𝓘(ℂ, ℂ) ω` — `Jacobians.ZLatticeQuotient.instIsManifoldQuotient`
- `LieAddGroup 𝓘(ℂ, ℂ) ω` — `Jacobians.ZLatticeQuotient.instLieAddGroupQuotient`

**Missing from kirov's `ZLatticeQuotient`** (need explicit instances or Mathlib lemmas):
- `ConnectedSpace (ℂ ⧸ Λ.toAddSubgroup)`: `ℂ` is connected and `QuotientAddGroup.mk`
  is surjective and continuous, so the quotient is connected. Mathlib should have
  `QuotientMap.connectedSpace` or `IsQuotientMap.connectedSpace`; ~5 LOC.
- `Nonempty (ℂ ⧸ Λ.toAddSubgroup)`: trivially from `⟨0⟩`; 1 LOC.
- `DiscreteTopology (ellipticLattice ω₁ ω₂ h)` and `IsZLattice ℝ (ellipticLattice ω₁ ω₂ h)`:
  mrdouglasny gets these from `abbrev`-unfolding to match Mathlib instance patterns
  (`ZSpan.instDiscreteTopology` etc.). Same approach works in kirov.

The `linearIndependent_one_of_pos_im` lemma and `Elliptic.ofUpperHalfPlane` helper
(normalized form `τ ∈ ℍ`) are also carrier-free and port directly.

**Assessment:** ~120 LOC of wiring, mostly `inferInstanceAs` delegation.
All **mechanical**.

### 2b. Carrier-sensitive part — `ellipticDz` and `genus_Elliptic_eq_one`

This is the substantive translation challenge.

#### The source proof strategy

mrdouglasny's proof in [`Elliptic/OneForm.lean`][src-elliptic-oneform] uses the
`X → ℂ → ℂ` submodule carrier:

1. **`ellipticDz`**: construct the `dz` witness with chart-local coefficient `1`
   on each chart target (and `0` off-target via `IsZeroOffChartTarget`).
   The cocycle check uses `ComplexTorus.transition_fderiv_apply_one`: the chart
   transitions of a complex torus are translations, whose derivative is `1`.

2. **`ellipticCoeffFun`**: extract the function `x ↦ form.coeff x (extChartAt x x)`
   (chart-centre value of the coefficient). The cocycle relation
   + `transition_fderiv_apply_one` imply this equals `form.coeff x z` for all
   `z ∈ chart target`.

3. **`ellipticCoeffFun_mdifferentiable`**: show this extracted function is
   `MDifferentiable`. Relies on `form.coeff x` being analytic on the chart
   target (the `IsHolomorphicOneFormCoeff` hypothesis).

4. **`MDifferentiable.exists_eq_const_of_compactSpace`** (Mathlib): since
   `Elliptic` is compact and connected, the MDifferentiable function is constant.

5. **`eq_smul_ellipticDz`**: every form equals `c • ellipticDz` for the constant `c`.
   Follows from steps 2–4 + `IsZeroOffChartTarget`.

6. **`genus_Elliptic_eq_one`**: `finrank ≤ 1` from `eq_smul_ellipticDz` (span = ⊤)
   + `finrank ≥ 1` from `ellipticDz ≠ 0`.

#### Adaptation for kirov's `ContMDiffSection` carrier

**`ellipticDz` as a `ContMDiffSection`:**

The goal type is:
```lean
ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω
  (fun x : Elliptic ω₁ ω₂ h =>
    TangentSpace 𝓘(ℂ) x →L[ℂ] (Bundle.Trivial (Elliptic ω₁ ω₂ h) ℂ) x)
```

Since the charts of `Elliptic` come from `ZLatticeQuotient.chartedSpaceQuotient`
(which uses the covering map `QuotientAddGroup.mk`), the tangent space at any
`x : Elliptic` identifies with `ℂ` via the chart trivialization. The translation-
invariant form `dz` on `ℂ` descends to the quotient because all chart transitions
are translations (derivative identically `1`).

Concrete construction:
```lean
noncomputable def ellipticDz (ω₁ ω₂ : ℂ) (h : ...) :
    HolomorphicOneForms (Elliptic ω₁ ω₂ h) where
  toFun := fun _x => ContinuousLinearMap.id ℂ ℂ
  -- In the trivialization: TangentSpace 𝓘(ℂ) x ≅ ℂ → ℂ, sending v ↦ v.
  contMDiff_toFun := by
    -- Reduce via contMDiffAt_hom_bundle to showing the coordinate map is constant
    -- (it's literally the identity CLM in every chart).
    -- The key: chart transitions on Elliptic have derivative 1
    -- (from transition_contDiffOn_of_agrees_with_mk: transitions are translations),
    -- so the inCoordinates factor is always the identity.
    ...
```

The `contMDiff_toFun` proof uses `contMDiffAt_hom_bundle` to unfold to
`ContMDiffAt` on the coordinate representation, then appeals to the fact that
chart transitions are translations with derivative `1`. The needed lemma:

```lean
-- Needed: chart transition derivative = 1
lemma ellipticTransitionDeriv_eq_one (x y : Elliptic ω₁ ω₂ h) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) x).target)
    (hyz : (extChartAt 𝓘(ℂ) x).symm z ∈ (extChartAt 𝓘(ℂ) y).source) :
    fderiv ℂ ((extChartAt 𝓘(ℂ) y) ∘ (extChartAt 𝓘(ℂ) x).symm) z 1 = 1
```

This is the kirov analog of mrdouglasny's `ComplexTorus.transition_fderiv_apply_one`.
It follows from `ZLatticeQuotient.transition_contDiffOn_of_agrees_with_mk` (already
in kirov): since the transition is a translation `z ↦ z + λ₀`, its derivative is
`id`, so `fderiv (· + λ₀) z 1 = 1`. ~20-30 LOC.

**`ellipticCoeffFun` analog:**

Instead of mrdouglasny's `form.coeff x (extChartAt x x)`, for kirov's carrier
we extract:
```lean
noncomputable def ellipticCoeffFun (form : HolomorphicOneForms (Elliptic ω₁ ω₂ h)) :
    Elliptic ω₁ ω₂ h → ℂ :=
  fun x => form.toFun x 1
  -- Here 1 : TangentSpace 𝓘(ℂ) x = ℂ, and form.toFun x : ℂ →L[ℂ] ℂ.
```

This is simpler than mrdouglasny's version because `TangentSpace 𝓘(ℂ) x = ℂ`
by definition, so there's no chart-centre indirection. The function
`x ↦ form.toFun x 1` is `MDifferentiable` directly from `form.contMDiff_toFun`
(applying the CLM evaluation at `1` is continuous linear). ~30 LOC.

**Liouville step:**

`MDifferentiable.exists_eq_const_of_compactSpace` applies unchanged, giving
constant `c : ℂ` with `form.toFun x 1 = c` for all `x`. Since `form.toFun x`
is a `ℂ`-linear map `ℂ →L[ℂ] ℂ`, knowing its value at `1` determines it:
`form.toFun x = c • ContinuousLinearMap.id ℂ ℂ`. So `form = c • ellipticDz`. ~40 LOC.

**`genus_Elliptic_eq_one`:** same structure as mrdouglasny:
- Lower bound: `ellipticDz ≠ 0` (its value at any point is `id ≠ 0`)
- Upper bound: span = ⊤ via `eq_smul_ellipticDz`
- Conclude `finrank = 1` ~30 LOC.

### 2c. Target file layout in kirov

```
Jacobians/
  Elliptic.lean   ← NEW (flat layout)
```

Content:
- `ellipticLattice`, `Elliptic`, all manifold instances (wiring to `ZLatticeQuotient`)
- `linearIndependent_one_of_pos_im`, `Elliptic.ofUpperHalfPlane`
- `ellipticDz : HolomorphicOneForms (Elliptic ω₁ ω₂ h)` (bundle section)
- `ellipticTransitionDeriv_eq_one` (helper)
- `ellipticCoeffFun`, its MDifferentiability, constancy
- `eq_smul_ellipticDz`, `ellipticDz_ne_zero`, `genus_Elliptic_eq_one`

---

## 3. Prerequisites

### Absent from kirov, needed but small

| Item | Where needed | Status | Effort |
|------|-------------|--------|--------|
| `ConnectedSpace (E ⧸ Λ.toAddSubgroup)` | `Elliptic` | Mathlib `IsQuotientMap.connectedSpace` or derive from surjective continuous image of connected space | ~5 LOC |
| `Nonempty (E ⧸ Λ.toAddSubgroup)` | `Elliptic` | `⟨0⟩` | 1 LOC |
| `DiscreteTopology (ellipticLattice ω₁ ω₂ h)` | `Elliptic` | Mathlib `ZSpan.instDiscreteTopology` (via `abbrev`-unfolding) | 0 LOC if `abbrev` |
| `IsZLattice ℝ (ellipticLattice ω₁ ω₂ h)` | `Elliptic` | Mathlib `instIsZLatticeRealSpan` (via `abbrev`-unfolding) | 0 LOC if `abbrev` |
| `ellipticTransitionDeriv_eq_one` | `ellipticDz` smoothness | Derivable from `ZLatticeQuotient.transition_contDiffOn_of_agrees_with_mk` + `fderiv` of translation | ~25 LOC |

### Absent from Mathlib, needed for direct genus-0 proof (ProjectiveLine)

| Item | Purpose | Effort |
|------|---------|--------|
| Chart-transition derivative computation for `ProjectiveLine` | Need `fderiv ℂ (1/z) z 1 = -1/z²` and application to the `chart0–chart1` overlap | ~20 LOC; uses `Complex.hasDerivAt_inv` |
| Liouville for decaying entire functions | An entire function with `f(z) → 0` as `z → ∞` must be zero | ~50-100 LOC; build from `Complex.liouville_theorem` via a removable-singularity / Riemann-extension argument. **Genuinely new mathematical content.** |

If the ProjectiveLine genus proof routes through `genus_eq_zero_iff_homeo`
(the existing kirov sorry), these Mathlib gaps are irrelevant for the initial port.

### Present in Mathlib, used by both

- `MDifferentiable.exists_eq_const_of_compactSpace` — used in `ellipticCoeffFun`
  constancy step and analogous ProjectiveLine argument.
- `finrank_le_of_span_eq_top` — used in genus upper-bound argument.
- `Module.finrank_zero_iff` — used for `Subsingleton` from `genus = 0`.

---

## 4. Effort estimate

| Sub-task | Type | LOC est. | Time est. |
|----------|------|----------|-----------|
| **ProjectiveLine manifold** (`ProjectiveLine`, charts, `ChartedSpace`, `IsManifold`, `stereographic`) | Mechanical translation | 250 | 2–3 h |
| **`genus_ProjectiveLine_eq_zero`** (via existing `genus_eq_zero_iff_homeo` sorry) | Mechanical | 5 | 30 min |
| **`Subsingleton (HolomorphicOneForms ProjectiveLine)`** | Mechanical | 5 | 15 min |
| **`ellipticLattice`, `Elliptic`, manifold wiring** | Mechanical | 100 | 1–2 h |
| **`ConnectedSpace`, `Nonempty` for quotient** | Mechanical | 10 | 30 min |
| **`ellipticTransitionDeriv_eq_one`** | Mechanical (fderiv of translation) | 25 | 1 h |
| **`ellipticDz` as `ContMDiffSection`** | New content (bundle-section construction) | 80 | 3–5 h |
| **`ellipticCoeffFun` + MDifferentiability** | New content (unwrapping bundle-section) | 60 | 2–3 h |
| **`eq_smul_ellipticDz`, `genus_Elliptic_eq_one`** | New content (Liouville conclusion) | 80 | 2–4 h |
| **Direct Liouville proof for ProjectiveLine** (optional, sorry-elimination) | Genuinely new math | 150 | 1–2 days |

**Without the optional Liouville task:** ~615 LOC total, ~12–20 hours of
focused Lean work. The mechanical portions (~400 LOC) are straightforward
translations. The carrier-sensitive Elliptic work (~220 LOC) is new content
but the proof strategy is clear and the mathematics is classical.

**With the optional Liouville task:** add ~150 LOC and 1–2 days.

---

## 5. Order of operations

**Recommended order: `ProjectiveLine` first, then `Elliptic`.**

Rationale:

1. **`ProjectiveLine` is self-contained and shorter.** The manifold
   construction (the bulk of the work) requires no carrier involvement and
   no dependency on `ZLatticeQuotient`. It can be started and completed
   independently.

2. **`stereographic` is load-bearing for kirov's `genus_eq_zero_iff_homeo`.** 
   The kirov sorry `genus_eq_zero_iff_homeo` is already stated as a biconditional
   with the sphere. Once `ProjectiveLine` exists in kirov, `stereographic` provides
   the concrete `Nonempty (ProjectiveLine ≃ₜ S²)` witness that discharges the
   `genus = 0` direction.

3. **`Elliptic` genus proof benefits from the pattern established by
   `ProjectiveLine`.** The `eq_smul_ellipticDz` argument is the Elliptic
   analog of the ProjectiveLine Liouville argument; doing ProjectiveLine
   first clarifies what "coefficient extraction from a `ContMDiffSection`"
   looks like in the kirov carrier.

4. **`ZLatticeQuotient` is already done.** The `Elliptic` manifold wiring
   is mostly `inferInstanceAs` delegation — it's fast once `ProjectiveLine`
   confirms the namespace/import conventions.

The two tasks have no dependency on each other at the manifold level and
could be parallelized, but the carrier-sensitive Elliptic work benefits from
having resolved the bundle-section pattern on the simpler ProjectiveLine case first.

---

## Appendix: source file cross-reference

| mrdouglasny source | kirov target | Notes |
|--------------------|-------------|-------|
| [`Jacobians/ProjectiveCurve/Line.lean`][src-line] | `Jacobians/ProjectiveLine.lean` | ~1:1 translation, namespace change |
| [`Jacobians/ProjectiveCurve/Line/Genus.lean`][src-line-genus] | append to `Jacobians/ProjectiveLine.lean` | 5 LOC |
| [`Jacobians/ProjectiveCurve/Line/OneForm.lean`][src-line-oneform] | append to `Jacobians/ProjectiveLine.lean` | 5 LOC, adjust carrier type |
| [`Jacobians/ProjectiveCurve/Elliptic.lean`][src-elliptic] | `Jacobians/Elliptic.lean` | Replace `ComplexTorus` with `ZLatticeQuotient` delegation |
| [`Jacobians/ProjectiveCurve/Elliptic/OneForm.lean`][src-elliptic-oneform] | append to `Jacobians/Elliptic.lean` | Significant rewrite: submodule → `ContMDiffSection` |
| [`Jacobians/ProjectiveCurve/Elliptic/Genus.lean`][src-elliptic-genus] | append to `Jacobians/Elliptic.lean` | Re-exports `genus_Elliptic_eq_one` |
| [`Jacobians/AbelianVariety/ComplexTorus.lean`][src-complextorus] | `Jacobians/ZLatticeQuotient.lean` (already exists) | No action needed |
