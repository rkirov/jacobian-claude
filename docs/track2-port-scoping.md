# Track 2 Port Scoping: `ProjectiveLine` and `Elliptic`

**Date:** 2026-05-01  
**Repos read:**
- SOURCE: [`mrdouglasny/jacobian-challenge`](https://github.com/mrdouglasny/jacobian-challenge) at commit `5453b1f6b7eaeb721c50e512b8817c7055b56b38`
- TARGET: [`rkirov/jacobian-claude`](https://github.com/rkirov/jacobian-claude)

Both repos target Mathlib commit `8e3c989104daaa052921bf43de9eef0e1ac9fbf5`.

---

## Carrier type reminder

The two repos use incompatible carriers for holomorphic 1-forms:

| Repo | Carrier for `HolomorphicOneForms X` |
|------|-------------------------------------|
| SOURCE (mrdouglasny) | `↥(holomorphicOneFormSubmodule X)` — a submodule of `X → ℂ → ℂ` cut out by `IsHolomorphicOneFormCoeff ∧ SatisfiesCotangentCocycle ∧ IsZeroOffChartTarget` |
| TARGET (rkirov) | `ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (fun x => TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x)` — Mathlib bundle sections |

These types are not defeq. Every theorem that mentions 1-forms must be re-derived; only theorems about the manifold topology/geometry are carrier-free.

---

## 1. `ProjectiveLine` port

### Source files read

- [`Jacobians/ProjectiveCurve/Line.lean`](https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Line.lean)
- [`Jacobians/ProjectiveCurve/Line/Genus.lean`](https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Line/Genus.lean)
- [`Jacobians/ProjectiveCurve/Line/OneForm.lean`](https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Line/OneForm.lean)

### 1a. Carrier-free part — ports directly

All of `Line.lean` is carrier-free. It contains:

1. **Type definition** (1 line):
   ```lean
   abbrev ProjectiveLine : Type := OnePoint ℂ
   ```
   `OnePoint ℂ` already has `CompactSpace`, `T2Space`, `NormalSpace`, `ConnectedSpace` from Mathlib; those transfer by `abbrev`.

2. **Two charts** (`chart0`, `chart1` : `OpenPartialHomeomorph ProjectiveLine ℂ`, ~130 lines):
   - `chart0` via `OnePoint.isOpenEmbedding_coe.toOpenPartialHomeomorph.symm`
   - `chart1` hand-built (`∞ ↦ 0`, `z ↦ z⁻¹`), with all five continuity obligations discharged using `OnePoint.continuousAt_infty'`, `Filter.tendsto_inv₀_cobounded`, `continuousOn_update_iff`.
   - Both proofs are complete (no `sorry`) in the source.

3. **`ChartedSpace ℂ ProjectiveLine`** instance (~25 lines): `chartAt` picks `chart1` at `∞`, `chart0` elsewhere.

4. **`IsManifold 𝓘(ℂ) ω ProjectiveLine`** instance (~80 lines): four cases of `chart ≫ₕ chart`; reduces to `contDiffOn_id` (same–same transitions) and `contDiffOn_inv` on `{0}ᶜ` (cross-transitions).

5. **`stereographic : ProjectiveLine ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1`** (3 lines): directly from Mathlib's `onePointEquivSphereOfFinrankEq`, using `finrank ℝ ℂ = 2`.

**Translation cost:** namespace change (`Jacobians.ProjectiveCurve` → `Jacobians`) and flattening the import path. The body ports line-for-line. Estimated **~250 LOC**, purely mechanical.

### 1b. Carrier-sensitive part — `genus_ProjectiveLine_eq_zero`

**Source approach** (`Line/Genus.lean`):
```lean
theorem genus_projectiveLine_eq_zero :
    Jacobians.RiemannSurface.genus ProjectiveLine = 0 := by
  rw [Jacobians.Axioms.AX_genus_eq_zero_iff_homeo]
  exact ⟨ProjectiveLine.stereographic⟩
```
This uses mrdouglasny's `AX_genus_eq_zero_iff_homeo` (an axiom in their framework).

**Kirov's situation:** `Jacobians/Genus.lean` already states:
```lean
lemma genus_eq_zero_iff_homeo {X ...} :
    genus X = 0 ↔ Nonempty (X ≃ₜ sphere ...) := sorry
```
So the port is a **1-line proof** that introduces no new `sorry`:
```lean
theorem genus_ProjectiveLine_eq_zero : genus ProjectiveLine = 0 := by
  rw [genus_eq_zero_iff_homeo]
  exact ⟨ProjectiveLine.stereographic⟩
```
The underlying mathematical gap (`genus_eq_zero_iff_homeo`) is already accounted for in kirov's repo.

**Alternative direct proof (carrier-honest, no extra sorry):** Show `HolomorphicOneForms ProjectiveLine` is a subsingleton directly on the bundle-section carrier, without uniformization. Concretely: any global section of `TangentSpace →L[ℂ] Trivial` on `OnePoint ℂ` corresponds — in `chart0` coordinates — to an entire function `f : ℂ → ℂ` (the chart-local coefficient), and in `chart1` coordinates to `g(w) = -f(1/w)/w²`. Holomorphicity of `g` at `w = 0` forces `f(z)/z² → 0` as `z → ∞`, so `f` is entire and bounded, hence constant by Liouville, and the boundary condition forces `f ≡ 0`.

This argument needs:
- `AnalyticOn.bounded_of_compact` or a Mathlib Liouville lemma for entire functions on `ℂ`.
- `Complex.norm_tendsto_zero_of_norm_inv_pow_mul_bounded` or similar (to upgrade the `z → ∞` bound to a polynomial growth bound).
- In practice, `Liouville` for entire functions is `Complex.liouville_theorem_aux` in Mathlib, but connecting it to the section formalism is ~80 additional lines of new Lean.

**Recommendation:** Use the uniformization sorry route for now. File the direct proof as a future `TODO(carrier)` comment.

**`Subsingleton (HolomorphicOneForms ProjectiveLine)`** (from `Line/OneForm.lean`):
```lean
instance : Subsingleton (HolomorphicOneForms ProjectiveLine) :=
  Module.finrank_zero_iff.mp genus_ProjectiveLine_eq_zero
```
Ports verbatim with carrier substitution. Needs kirov's `FiniteDimensional ℂ (HolomorphicOneForms X)` instance (available in `HolomorphicForms.lean` via Montel).

### 1c. Target file layout in `rkirov/jacobian-claude`

```
Jacobians/ProjectiveLine.lean
```
Single flat file (matching kirov's layout under `Jacobians/`). Contents:
1. Carrier-free: type, charts, ChartedSpace, IsManifold, stereographic.
2. Carrier-sensitive (bottom of file): `genus_ProjectiveLine_eq_zero`, `instSubsingletonHolomorphicOneForms`.

Imports needed:
```lean
import Jacobians.Genus        -- for genus and genus_eq_zero_iff_homeo
import Jacobians.HolomorphicForms  -- for FiniteDimensional instance
import Mathlib                      -- or targeted Mathlib imports
```

---

## 2. `Elliptic ω₁ ω₂` port

### Source files read

- [`Jacobians/ProjectiveCurve/Elliptic.lean`](https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Elliptic.lean)
- [`Jacobians/ProjectiveCurve/Elliptic/OneForm.lean`](https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Elliptic/OneForm.lean)
- [`Jacobians/ProjectiveCurve/Elliptic/Genus.lean`](https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Elliptic/Genus.lean)
- [`Jacobians/RiemannSurface/OneForm.lean`](https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/RiemannSurface/OneForm.lean) (for carrier context)

### 2a. Carrier-free part — reduces to instantiating ZLatticeQuotient

The source defines:
```lean
noncomputable def Elliptic (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) : Type :=
  ComplexTorus ℂ (ellipticLattice ω₁ ω₂ h)
```
where `ComplexTorus V L := V ⧸ L.toAddSubgroup` with all manifold/Lie-group instances from `AbelianVariety/ComplexTorus.lean`.

Kirov's `ZLatticeQuotient.lean` already provides **exactly the same package** for `E ⧸ Λ.toAddSubgroup` when `E` is a finite-dimensional normed ℝ-space and `Λ` is a ZLattice:
- `CompactSpace`, `T2Space`, `T3Space`, `IsTopologicalAddGroup` ✓
- `ChartedSpace E (E ⧸ Λ)` ✓ (via `isLocalHomeomorph_mk`)
- `IsManifold 𝓘(𝕜, E) n (E ⧸ Λ)` ✓ (via `instIsManifoldQuotient`)
- `LieAddGroup 𝓘(𝕜, E) n (E ⧸ Λ)` ✓ (via `instLieAddGroupQuotient`)

So the carrier-free port is:
```lean
import Jacobians.ZLatticeQuotient

noncomputable abbrev ellipticRealBasis (ω₁ ω₂ : ℂ)
    (h : LinearIndependent ℝ ![ω₁, ω₂]) : Module.Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank h (by simp [Complex.finrank_real_complex])

noncomputable abbrev ellipticLattice (ω₁ ω₂ : ℂ)
    (h : LinearIndependent ℝ ![ω₁, ω₂]) : Submodule ℤ ℂ :=
  Submodule.span ℤ (Set.range (ellipticRealBasis ω₁ ω₂ h))

noncomputable def Elliptic (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) : Type :=
  ℂ ⧸ (ellipticLattice ω₁ ω₂ h).toAddSubgroup
```

All 7+ Buzzard instances then come from `inferInstanceAs` pointing at `ZLatticeQuotient` typeclass instances, precisely as in the source's `inferInstanceAs (... (ComplexTorus ...))` pattern.

**One subtlety:** The source uses `𝓘(ℂ, ℂ)` as the model, which equals `modelWithCornersSelf ℂ ℂ`. Kirov's `ZLatticeQuotient` works for any `𝕜`, so `𝓘(ℂ, ℂ)` is the correct instantiation here.

**Translation cost:** ~100 LOC, mechanical. No new content — every instance is a direct `inferInstanceAs` of an already-proved `ZLatticeQuotient` instance.

### 2b. Carrier-sensitive part — `ellipticDz` and `genus_Elliptic_eq_one`

#### 2b-i. `ellipticDz` in kirov's bundle-section carrier

**Source construction** (`Elliptic/OneForm.lean`):

In mrdouglasny's submodule carrier, `ellipticDz` is the coefficient family:
```lean
fun x z => Set.indicator (extChartAt 𝓘(ℂ, ℂ) x).target (fun _ => (1 : ℂ)) z
```
with three obligations discharged: holomorphicity, cotangent cocycle, zero-off-target. The cotangent cocycle check requires `ComplexTorus.transition_fderiv_apply_one` — a lemma (proved in `AbelianVariety/ComplexTorus.lean`) that the chart transition fderiv on the torus equals 1 when applied to 1.

**Kirov's construction** (new content, ~40 LOC):

In kirov's framework, `HolomorphicOneForms X = ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω (fiber)`. A section assigns to each `x : X` a continuous ℂ-linear map `TangentSpace 𝓘(ℂ) x →L[ℂ] ℂ`. On `Elliptic ω₁ ω₂ h`, charts are local inverses of `QuotientAddGroup.mk : ℂ → ℂ ⧸ Λ`, so the tangent space at every point is canonically `ℂ` (as a Lean fact: `TangentSpace (𝓘(ℂ, ℂ)) q = ℂ` by definition for `ChartedSpace ℂ`-modelled manifolds).

The `dz` section is the **constant section at `id`**:
```lean
noncomputable def ellipticDz (ω₁ ω₂ : ℂ) (h : LinearIndependent ℝ ![ω₁, ω₂]) :
    HolomorphicOneForms (Elliptic ω₁ ω₂ h) where
  toFun := fun _ => ContinuousLinearMap.id ℂ ℂ
  contMDiff_toFun := contMDiff_const
```

The `contMDiff_const` lemma (`ContMDiffSection` constant sections are smooth) handles the smoothness obligation directly — the bundle formalism absorbs the cocycle check that mrdouglasny had to verify explicitly. **This is a genuine simplification**: the bundle-section carrier makes `dz` easier to construct than the submodule carrier.

`ellipticDz ≠ 0` follows immediately: `ContinuousLinearMap.id ℂ ℂ ≠ 0` as a CLM.

**Risk:** `contMDiff_const` may need to be applied carefully to sections of a non-trivial fiber bundle. The fiber here is `TangentSpace 𝓘(ℂ) q →L[ℂ] Trivial q` which is definitionally `ℂ →L[ℂ] ℂ` — so this is morally constant-into-a-normed-space and `contMDiff_const` should apply. If Lean's elaborator doesn't see through the defeq automatically, a short `show`-cast will suffice.

#### 2b-ii. `genus_Elliptic_eq_one`

**Lower bound (`genus ≥ 1`):** From `ellipticDz ≠ 0` + `FiniteDimensional` (kirov's Montel instance): `finrank ≥ 1`.

**Upper bound (`genus ≤ 1`):** The argument is the same as mrdouglasny's `eq_smul_ellipticDz` + Liouville, translated to kirov's carrier (~80 LOC of new content):

1. For `α : HolomorphicOneForms (Elliptic ω₁ ω₂ h)`, define `f : Elliptic → ℂ` by:
   ```lean
   f q := α.toFun q (1 : ℂ)
   ```
   (evaluating the CLM at the tangent vector `1`)

2. `f` is smooth: follows from `α.contMDiff_toFun` by post-composing with the continuous evaluation `(· 1)`.

3. `f` is constant: `MDifferentiable.exists_eq_const_of_compactSpace` (Mathlib) applied to `f`.
   - Prerequisite: `ConnectedSpace (Elliptic)` ✓ (quotient of connected `ℂ`).
   - Prerequisite: `CompactSpace (Elliptic)` ✓ (from `ZLatticeQuotient`).
   - This is the intrinsic Liouville theorem on compact complex manifolds.

4. `α = f(q₀) • ellipticDz`: From step 3, `α.toFun q = c • id` for all `q`, hence `α` is the scalar multiple `c • ellipticDz`.

5. `finrank ≤ 1` via `finrank_le_of_span_eq_top`.

**Dependency on `MDifferentiable.exists_eq_const_of_compactSpace`:** mrdouglasny uses this Mathlib lemma explicitly (see `Elliptic/OneForm.lean` line `rcases MDifferentiable.exists_eq_const_of_compactSpace ...`). It should be available at the pinned Mathlib commit since it appears in the source.

### 2c. Target file layout in `rkirov/jacobian-claude`

```
Jacobians/Elliptic.lean          -- carrier-free: type, lattice, all instances
Jacobians/EllipticGenus.lean     -- carrier-sensitive: ellipticDz, genus = 1
```

Imports for `Elliptic.lean`:
```lean
import Jacobians.ZLatticeQuotient
import Mathlib.LinearAlgebra.Matrix.Basis  -- basisOfLinearIndependent...
```

Imports for `EllipticGenus.lean`:
```lean
import Jacobians.Elliptic
import Jacobians.Genus
import Jacobians.HolomorphicForms
import Jacobians.ZLatticeQuotient
```

---

## 3. Prerequisites — what is needed but absent

### 3a. Mathlib gaps (at commit 8e3c989)

| Lemma | Where needed | Status |
|-------|-------------|--------|
| `MDifferentiable.exists_eq_const_of_compactSpace` | Upper bound in `genus_Elliptic_eq_one` | Present (used by mrdouglasny) |
| `onePointEquivSphereOfFinrankEq` | `stereographic` in ProjectiveLine | Present (used by mrdouglasny) |
| `contMDiff_const` for `ContMDiffSection` | `ellipticDz` construction | Should be present; may require `show`-cast to the right bundle type |
| `IsOpenEmbedding.toOpenPartialHomeomorph` | `chart0` in ProjectiveLine | Present (used by mrdouglasny) |
| `Filter.tendsto_inv₀_cobounded` | `chart1` continuity | Present (used by mrdouglasny) |
| `continuousOn_update_iff` | `chart1` inverse continuity | Present (used by mrdouglasny) |

No Mathlib gaps are expected to block the port. All lemmas used in mrdouglasny's proofs are by definition available at the pinned commit.

### 3b. Kirov-side gaps

| Item | Needed for | Status |
|------|-----------|--------|
| `Jacobians/ProjectiveLine.lean` | ProjectiveLine type + manifold instances | **New file, does not exist** |
| `Jacobians/Elliptic.lean` | Elliptic type + all instances | **New file, does not exist** |
| `Jacobians/EllipticGenus.lean` | `ellipticDz`, `genus_Elliptic_eq_one` | **New file, does not exist** |
| `genus_eq_zero_iff_homeo` proof | `genus_ProjectiveLine_eq_zero` | **Sorry in `Genus.lean`** — acceptable, pre-existing |
| `ZLatticeQuotient.instIsManifoldQuotient` | Elliptic `IsManifold` | **Present, sorry-free** |
| `ZLatticeQuotient.instLieAddGroupQuotient` | Elliptic `LieAddGroup` | **Present, sorry-free** |
| `HolomorphicForms.lean` `FiniteDimensional` instance | `genus ≥ 1` from `dz ≠ 0` | **Present (1 sorry: `closedBall_isCompact`)** |
| `transition_fderiv_apply_one` analog | **Not needed** — kirov's `dz` is `contMDiff_const`; bundle formalism handles cocycles automatically | N/A |

### 3c. One critical missing lemma to anticipate

The step `f q := α.toFun q (1 : ℂ)` is smooth requires composing a `ContMDiffSection` with the continuous evaluation map `ev₁ : (ℂ →L[ℂ] ℂ) → ℂ`. This composes a smooth section with a linear map, giving a smooth function. The needed lemma is something like:

```lean
ContMDiffSection.contMDiff_toFun_apply :
  (α : ContMDiffSection 𝓘(ℂ) (ℂ →L[ℂ] ℂ) ω E) → (v : ℂ) →
  ContMDiff 𝓘(ℂ) 𝓘(ℂ, ℂ) ω (fun x => α.toFun x v)
```

This should follow from `ContMDiff.clm_apply` + `α.contMDiff_toFun`. If it is not directly in Mathlib at this name, it is ~5 lines to derive.

---

## 4. Effort estimate

| Sub-task | LOC | Time | Classification |
|----------|-----|------|----------------|
| ProjectiveLine: charts + ChartedSpace + IsManifold (from `Line.lean`) | ~250 | 2 days | Mechanical translation — namespace change + import flattening, proofs port verbatim |
| ProjectiveLine: `stereographic` | ~5 | 0.5 days | Mechanical (3-line Mathlib call) |
| ProjectiveLine: `genus_ProjectiveLine_eq_zero` + subsingleton | ~15 | 0.5 days | Mechanical (1-line proof against existing sorry) |
| Elliptic: `ellipticLattice`, `def Elliptic`, all instances | ~100 | 1 day | Mechanical — `inferInstanceAs` rewiring to `ZLatticeQuotient` |
| Elliptic: `ellipticDz` as `ContMDiffSection` | ~50 | 1–2 days | New mathematical content — understanding `ContMDiffSection` constant-section API, `contMDiff_const` elaboration |
| Elliptic: `genus_Elliptic_eq_one` (Liouville upper bound) | ~100 | 2–3 days | New mathematical content — adapting the coefficient-function argument to bundle sections, `MDifferentiable.exists_eq_const_of_compactSpace` |
| **Total** | **~520** | **7–9 days** | |

**LOC split:** ~370 mechanical (71%) / ~150 genuinely new (29%).  
**Time split:** ~4 days mechanical / ~3–5 days new content.

The `contMDiff_const` elaboration for bundle sections is the highest-uncertainty item; the cocycle check that consumed ~40% of mrdouglasny's `ellipticDz` proof simply vanishes in kirov's framework.

---

## 5. Order of operations

**Recommended order:**

1. **`Jacobians/ProjectiveLine.lean` — carrier-free content first** (~2.5 days)

   Rationale: pure mechanical translation with zero carrier interaction. Validates the import/namespace translation pipeline before touching anything carrier-sensitive. Immediately gives kirov an inhabited `ProjectiveLine` example with all 7 Buzzard instances. The full `Line.lean` has complete (non-sorry) proofs for the manifold structure; this is a direct win.

2. **`genus_ProjectiveLine_eq_zero` + subsingleton** (bottom of same file, ~0.5 days)

   Rationale: 1-line proof against an existing sorry; closes the ProjectiveLine example fully within the sorry budget kirov already has.

3. **`Jacobians/Elliptic.lean` — carrier-free content** (~1 day)

   Rationale: mechanical rewiring of `inferInstanceAs` from `ComplexTorus` to `ZLatticeQuotient`. No risk; kirov's `ZLatticeQuotient` is already sorry-free.

4. **`Jacobians/EllipticGenus.lean` — `ellipticDz` + `genus_Elliptic_eq_one`** (~3–5 days)

   Rationale: do last — this is the only genuinely new content and has the highest uncertainty. Doing it last means steps 1–3 are already committed and buildable if the hard step takes longer than expected.

**Why ProjectiveLine before Elliptic (not the other way):**  
The carrier-sensitive part of ProjectiveLine (`genus = 0`) is a 1-line proof with no new content; the carrier-sensitive part of Elliptic (`genus = 1`, `dz` construction) is ~150 LOC of new content. So the difficulty gradient goes: easy → easy → medium → hard. This ordering maximizes early commits and gives the clearest signal if the `ContMDiffSection` constant-section API is harder than expected.

---

## Appendix: source file cross-references

All URLs point to commit `5453b1f6b7eaeb721c50e512b8817c7055b56b38` in `mrdouglasny/jacobian-challenge`.

| Content | URL |
|---------|-----|
| ProjectiveLine type, charts, manifold, stereographic | https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Line.lean |
| genus_projectiveLine_eq_zero | https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Line/Genus.lean |
| Subsingleton HolomorphicOneForm ProjectiveLine | https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Line/OneForm.lean |
| Elliptic type, instances | https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Elliptic.lean |
| ellipticDz, eq_smul_ellipticDz, genus_Elliptic_eq_one | https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Elliptic/OneForm.lean |
| genus_Elliptic_eq_one re-export | https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/ProjectiveCurve/Elliptic/Genus.lean |
| SOURCE carrier definition (HolomorphicOneForm submodule) | https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/RiemannSurface/OneForm.lean |
| ComplexTorus (mrdouglasny's analogue of ZLatticeQuotient) | https://github.com/mrdouglasny/jacobian-challenge/blob/5453b1f6b7eaeb721c50e512b8817c7055b56b38/Jacobians/AbelianVariety/ComplexTorus.lean |
