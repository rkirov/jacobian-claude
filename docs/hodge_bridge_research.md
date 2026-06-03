# Research — the Hodge/Serre bridge `H^{0,1}(X) ≅ Ω(X)` (the gate for `arithmeticGenus_eq_genus`)

Read-only scoping note for `/home/rado/jacobian`. Companion to `docs/architecture_map.md`,
`docs/abel_riemannroch_research.md`, `docs/period_lattice_realbasis_research.md`. Verified against
the repo's Mathlib pin (`8e3c989…`) and this session's capability survey.

Legend: **[VERIFIED]** read off Mathlib/repo this session; **[BOOK]** Forster/Griffiths–Harris;
**[BELIEVED]** standard, not re-derived.

---

## 0. Bottom line (recommendation)

**The headline (`genus_eq_zero_iff_homeo`, forward) bottoms out in Serre duality at `D=0`, which is a
genuine research-scale analysis formalization — not a "hard lemma." Mathlib has *zero* scaffolding for
it (no differential forms on manifolds, no de Rham, no Hodge, no elliptic regularity; a known multi-year
gap with no open PR).** The repo's own intrinsic ∂̄ + (0,1)-forms + finiteness make a *Forster-style*
proof (residue-pairing perfectness, not full Hodge-Laplacian) the cheapest route, but it is still
multi-month, research-grade work.

**The target `arithmeticGenus_eq_genus : h1Dim 0 = genus` splits into two very unequal halves:**

| Half | Statement | Cost | Reuses |
|---|---|---|---|
| **EASY** | `genus ≤ h1Dim 0` | ~shared with #7 (2–4k LoC, partly built) | the #7 cut-surface/Green/`CurveIntegral` engine + the L² positivity `(i/2)∮ω∧ω̄>0` |
| **HARD** | `h1Dim 0 ≤ genus` | research-grade, multi-month, **the wall** | nothing in Mathlib; the repo's finiteness + comparison help but don't close it |

**Recommended posture:** keep `arithmeticGenus_eq_genus` (and `serre_h1_eq`) as **named honest kernels**
— the project has *already* achieved the defensible milestone "challenge API + RR ladder complete modulo
a handful of named classical-theorem inputs (Serre duality, residue theorem, Abel)." If a real discharge
is wanted, **invest in the EASY half first** (it is mostly the #7 build, unlocks part of #7 and #1b too),
and isolate the HARD half as the single kernel `serre_pairing_perfect`. Do **not** attempt full
Hodge-Laplacian decomposition — it is strictly larger and equally unscaffolded.

---

## 1. The exact target and why the comparison alone is not enough

`genus X := Module.finrank ℂ (HolomorphicOneForms X)` (`Genus.lean`); `HolomorphicOneForms X` = analytic
sections of the cotangent bundle (`HolomorphicForms.lean`), finite-dim (Montel). [VERIFIED]

`arithmeticGenus_eq_genus (𝔘) (hL) : 𝔘.h1Dim 0 = genus X` where `h1Dim 0 = finrank ℂ (cechH1 𝔘 0)`.

The Dolbeault comparison (`cechH1_dolbeault_comparison`, this session: round-trip 1 + crux done,
round-trip 2 scoped) gives only
```
finrank ℝ (DolbeaultH01 X) = 2 · finrank ℂ (cechH1 𝔘 0) = 2 · h1Dim 0.
```
This relates `cechH1` to the Dolbeault `H^{0,1}` — it is **`H¹(𝒪) ≅ H^{0,1}`**, the *first* iso of the
classical chain `H¹(𝒪) ≅ H^{0,1} ≅ Ω(X)*`. By itself it yields the **tautology** `2·h1Dim = 2·h1Dim`.
To reach `h1Dim 0 = genus` we additionally need the **second** iso
```
finrank ℝ (DolbeaultH01 X) = 2 · genus X      i.e.   dim_ℂ H^{0,1}(X) = dim_ℂ Ω(X) = g,
```
which is **Serre duality at `D=0`** (equivalently the Hodge fact `H^{0,1} ≅ conjugate of Ω`). This is
the bridge this note scopes.

(Note: `DolbeaultH01 X` is built as a `Module ℝ` only; its natural `Module ℂ` — the pointwise codomain
action — is part of the bridge build, needed to phrase `dim_ℝ = 2·dim_ℂ`. Minor, ~tens of LoC.)

---

## 2. The two-direction decomposition (the precise math)

The natural map is the **conjugation** `Φ : Ω(X) → H^{0,1}(X)`, `ω ↦ [ω̄]` (a holomorphic `(1,0)`-form's
conjugate is a `∂̄`-closed `(0,1)`-form; on a curve `A^{0,2}=0` so every `(0,1)`-form is a class). `Φ`
is **conjugate-ℂ-linear**. Serre duality at `D=0` ⟺ `Φ` is a (conjugate-linear) **isomorphism**.

### 2a. EASY half — `Φ` injective ⟹ `g ≤ dim_ℂ H^{0,1}` [shared with #7]

`Φ(ω)=0` means `ω̄ = ∂̄f` for some smooth `f`. Then
```
∫_X ω̄ ∧ ω = ∫_X (∂̄f) ∧ ω = ∫_X d(f·ω) = 0      (Stokes; ω holomorphic ⟹ dω = ∂ω, and (∂f)∧ω is (2,0)=0)
```
but the **L² positivity** `(i/2)∫_X ω̄∧ω = ∫_X |coeff|² dA > 0` for `ω ≠ 0`. Contradiction, so `ω=0`. ⟹
`Φ` injective ⟹ `g ≤ dim_ℂ H^{0,1}` (= `h1Dim 0` via the comparison).

**This is the *same* positivity `(i/2)∮∮ ω∧ω̄ > 0` that `#7` (`exists_periodLattice_realBasis`) needs**
(Riemann's second bilinear relation) — see `period_lattice_realbasis_research.md`. The integration
engine (cut-surface → planar `4g`-gon → Mathlib divergence theorem / `CurveIntegral` / `extDeriv`) is
shared. So the EASY half is *not new analysis* beyond #7; it is bookkeeping on top of the #7 build.

### 2b. HARD half — `Φ` surjective ⟹ `dim_ℂ H^{0,1} ≤ g` [the wall]

Surjectivity = every `(0,1)`-class has a **conjugate-holomorphic** (= harmonic, on a curve)
representative. Equivalently: the `∂̄`-cokernel `A^{0,1}/im ∂̄` is no bigger than `Ω(X)`. This is the
**existence** half of Hodge/Serre and needs one of:
- **Hodge decomposition** `A^{0,1} = (harmonic) ⊕ im ∂̄` via the `∂̄`-Laplacian + **elliptic
  regularity** + **Fredholm/closed-range**; or
- **Weyl's lemma** + L² methods (Forster §19–§24 route); or
- **residue-pairing perfectness** (Forster §17): the pairing `H¹(𝒪) × Ω(X) → ℂ` is nondegenerate on
  the `H¹` side too — this is where the analysis hides, even though the *pairing* reuses integration.

There is **no cheap shortcut**, and the `g=0` headline case is **not** exempt: it needs `h1Dim 0 = 0`,
i.e. `∂̄ : A⁰ → A^{0,1}` surjective on a genus-0 surface — still global `∂̄`-solvability-with-obstruction
= the same wall. Likewise `cohomological_riemannRoch` (χ-additivity, proven mod skyscraper) gives
`h⁰(D) − h¹(D)` in terms of the **arithmetic** genus `p_a := h¹(0)`; the identity `p_a = g` (geometric)
is *exactly* this bridge — χ-additivity cannot supply it. [VERIFIED by structural analysis]

---

## 3. Mathlib status (this session's survey) [VERIFIED]

**Absent (the whole differential-geometric layer):** differential forms `Ω^k` on manifolds; exterior
derivative `d` on manifolds; de Rham cohomology; Dolbeault cohomology / `∂̄` operator (beyond the plane);
integration of forms over a manifold/chain; manifold Stokes; **Hodge decomposition**; **elliptic
regularity**; Fredholm theory for differential operators; Weyl's lemma; ∂̄-estimates;
Rellich–Kondrachov. (Hodge theory is a known multi-year Lean gap, no open PR.)

**Present & reusable:**
- **Divergence theorem on boxes** `MeasureTheory.Integral.DivergenceTheorem` (2-D Green, countable
  exceptional set) — the engine for the EASY-half positivity (planar, chart-local).
- **`Mathlib.MeasureTheory.Integral.CurveIntegral`** — `curveIntegral`, concat/symm, **homotopy
  invariance of closed-form integrals**; `Convex.exists_forall_hasDerivWithinAt` (primitive on a convex
  set); `Analysis.Complex.HasPrimitives` (Morera). Closes the "primitive on the cut surface" gap.
- **`Analysis.Calculus.DifferentialForm`** — `extDeriv`, `d²=0`, `extDeriv_pullback` (on **normed
  spaces**, not manifolds — fine because the proof is chart-local).
- **Harmonic functions + Laplacian on ℝⁿ** (`Analysis.InnerProductSpace.Harmonic`, `…Laplacian`) —
  building blocks for a harmonic-rep argument, but no operator-on-forms / Hodge wrapper.
- **Hilbert spaces + orthogonal projection** (`InnerProductSpace.Projection`) — the abstract Hodge
  ingredient (projection onto a closed subspace), but the *closed-range* fact for `∂̄` is the missing
  analysis.
- **Sobolev spaces (distributional, Bessel-potential, on ℝⁿ)** `Analysis.Distribution.Sobolev` — recent;
  not yet the Sobolev-embedding/elliptic toolkit a Hodge proof needs.
- Cauchy integral / Cauchy–Goursat in ℂ (`Analysis.Complex.CauchyIntegral`).

**Repo-built and reusable (axiom-clean unless noted):** intrinsic ∂̄ operator `RealForms.dbar`/`dbarL`;
the `(0,1)`-forms `OneFormsZeroOne`/`DolbeaultH01`; the **Dolbeault comparison** `H¹(𝒪)≅H^{0,1}` (RT1 +
crux done this session, RT2 scoped); `finiteDimensional_cechH1` (de-risked, Montel/Riesz); the planar
∂̄-disk solvability `DbarDisk`/`cauchyTransform`; the #7 cut-surface/period/Green machinery (R1/R2 +
`periodVec_linearIndependent` — the positivity infrastructure); `HolomorphicOneForms` finite-dim (Montel).

---

## 4. Routes for the HARD half, ranked

**Route B — Forster residue-pairing perfectness [RECOMMENDED, the repo's chosen route].** Define the
pairing `H¹(𝒪) × Ω(X) → ℂ` (Čech-residue, Forster §17); the integration side reuses #7. Show
nondegeneracy on the `H¹` side using the **finiteness theorem** (done) + Dolbeault + Weyl's lemma. This
is the architecture map's `serre_h1_eq`/`arithmeticGenus_eq_genus` 🔴 box ("residue pairing: ✅ int side;
🔴 perfectness"). Smaller than full Hodge because it leans on the already-built finiteness. Still
research-grade (Weyl's lemma / elliptic regularity for the obstruction-vanishing is the irreducible
core). **Estimate: multi-month; the single genuine wall of the project.**

**Route A — full Hodge-Laplacian decomposition.** Build the `∂̄`-Laplacian, prove elliptic regularity +
closed range + Fredholm, get `A^{0,1} = harmonic ⊕ im∂̄`, identify harmonic `(0,1)` with `Ω̄`. Most
classical, **strictly larger** (needs Sobolev-embedding/elliptic toolkit Mathlib lacks). Not recommended.

**Route C — Weyl's lemma + L² (Hörmander) directly.** Solve `∂̄u=f` in L² with the holomorphic
obstruction; the obstruction space is `Ω(X)`. Comparable to B's core; B is preferable because it slots
into the existing Forster scaffold (finiteness + Čech) the repo already follows.

---

## 5. Cost & strategic read

- **EASY half (`g ≤ h1Dim`):** ~the #7 build (2–4k LoC, partly built). High value: it is *shared* with
  #7 (`exists_periodLattice_realBasis`) and contributes to #1b. A defensible, finite, mostly-scaffolded
  target.
- **HARD half (`h1Dim ≤ g`):** research-grade, multi-month, **no Mathlib scaffolding**. This is the
  irreducible wall and is shared by the RR headline, #1b, and (via RR) #3. Formalizing it = contributing
  Serre duality / a slice of Hodge theory to the ecosystem — a project in its own right.

**Therefore:** full sorry-free `genus_eq_zero_iff_homeo` is gated on a Serre-duality formalization that
is realistically a multi-month-to-year effort with zero upstream support. The **honest, already-reached
milestone** is: *the entire challenge API and the Riemann–Roch ladder are mechanized and axiom-clean
modulo a small, explicit set of named classical-theorem kernels* — `arithmeticGenus_eq_genus`/
`serre_h1_eq` (Serre duality), `deg_div` (residue theorem), `exists_cutSurface` (#7), and
`abelJacobi_twoPoint_ne_zero` (#3). Each is a single TRUE statement, not open design.

---

## 6. Concrete next steps (if pursuing a real discharge)

1. **Finish the Dolbeault comparison (RT2 + wire `cechH1_dolbeault_comparison`).** Needed on *every*
   route; ~1 focused session; the gateway (`holoFn_cocycle_add`) is done. Removes one named kernel.
2. **Build the EASY half** as `genus_le_h1Dim` reusing the #7 cut-surface/Green/positivity engine
   (coordinate with the #7 build — same `(i/2)∮ω∧ω̄>0`). Gives `g ≤ h1Dim 0` axiom-clean.
3. **Isolate the HARD half** as a single named kernel `serre_pairing_perfect`
   (`h1Dim 0 ≤ genus`), documented against Forster §17. Then `arithmeticGenus_eq_genus` = step 2 + step 3
   (antisymmetry of `≤` on `ℕ`), and the project's unproved surface shrinks to that one kernel + residue
   + #3 + #7.
4. Only after 1–3, if the Serre-duality formalization is greenlit as a standalone multi-month effort,
   attack `serre_pairing_perfect` via Route B (Weyl's lemma core).

**My recommendation to the maintainer:** do steps 1–3 (finite, high-value, shrinks and clarifies the
surface), then *decide explicitly* whether to commit to the step-4 Serre-duality build or to declare the
"modulo named classical kernels" milestone as the deliverable. Steps 1–3 are the right work regardless of
that decision.
