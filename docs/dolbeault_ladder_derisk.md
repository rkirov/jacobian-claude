# G3/G4 de-risk — representation decision + refined cost (2026-06-01)

De-risk probe for the **fully-sorry-free** finish, run before committing to the Dolbeault→Serre→RR
monolith (user directive: "go sorry-free; de-risk G3/G4 first"). Companion to
`docs/riemann_roch_proof_plan.md` (the deep reference) and `docs/STATUS.md` (current snapshot).

All "VERIFIED" claims below were checked this session by reading source at the repo's Mathlib pin
`8e3c989104da` (`.lake/packages/mathlib/Mathlib`) and the repo files cited. LoC figures are
engineering estimates (calibrated to the period-lattice / Abel notes), not measurements.

---

## TL;DR verdict

1. **Representation: concrete fixed-finite-cover Čech `H¹` valued in `ModuleCat ℂ`** — NOT Mathlib's
   abstract `Sheaf.H` (Ext-based, gives no handle for the Montel estimate). Analysis acts directly on
   the cochain spaces (products of holomorphic-function spaces on overlap-disks); the abstract
   homological-algebra machinery (`HomologySequence`, `eulerChar`, snake lemma) still applies *to the
   concrete cochain complexes* for the χ-additivity bookkeeping. Best of both, and it matches
   Forster's actual §14–16 proof.

2. **The wall is bimodal, not a uniform monolith.** It splits into a **de-risked ~2–4k-LoC scaffold**
   (cohomological RR: ∂̄-globalization + finiteness + χ-additivity — every hard analytic primitive is
   already in Mathlib or the repo) and a **concentrated ~2–4k-LoC high-variance core** (Serre duality
   / Dolbeault `H^{0,1}`, no Mathlib scaffold). Total RR ≈ **4–8k LoC**, down from the earlier
   "9–18k monolith" and — more usefully — with the high risk *isolated*.

3. **Scoping win for the headline.** `#1-forward` (`genus 0 → S²`, the wired consumer) needs only the
   **`D=0` case of Serre duality** (`g₁ = g`, i.e. `dim H¹(X,𝒪) = dim Ω(X)`), *not* the full
   residue-pairing-perfectness for all `D`. The `l(K−P)` term is killed by the already-proven
   negative-degree vanishing, and `h¹(P) ≤ h¹(0) = g₁` falls out of the skyscraper LES. So the
   high-risk Dolbeault core can be attacked in its smallest form first.

4. **Recommended order:** build the de-risked scaffold (G2 → finiteness → χ-additivity) to land
   *cohomological RR* `l(D) − h¹(D) = deg D + 1 − g₁` with `H¹` finite — isolating exactly two
   analytic inputs (`g₁ = g`, and `deg_div`) — then attack the `D=0` Dolbeault/Serre nugget last,
   with all the bookkeeping already in place.

---

## Representation decision (the key deliverable)

**Model `𝒪_D` and `Čech-H¹` concretely on a fixed finite chart-disk cover; keep them in `ModuleCat ℂ`
so the abstract homology toolkit applies.**

- **Cover.** `X` compact ⇒ finite cover `𝔘 = {Uᵢ}` by chart-disks. The repo already builds exactly
  this (`Jacobians/Montel/Cover.lean`: `chartCover : Finset X`, shrinkings). Reuse it.
- **Sheaf sections.** `𝒪_D(U) := { f : MeromorphicFunction over U // ∀ x∈U, -D x ≤ orderW f x }`, a
  `Submodule ℂ`. Built on the repo's existing order/divisor layer
  (`Discharge/Manifold/MeromorphicDivisor.lean`: `orderFun`, `divisor`, `zeros_finite`,
  `poles_finite`) and `RiemannRoch.lean`'s `linearSystem`/`orderW`/`germZeroSubmodule` (the
  `toFun`-junk quotient is *already solved* there — reuse it for the local sections too).
- **Čech complex.** `C⁰ = ∏ᵢ 𝒪_D(Uᵢ)`, `C¹ = ∏_{i<j} 𝒪_D(Uᵢ∩Uⱼ)`, alternating-difference `δ`.
  Package as a `CochainComplex (ModuleCat ℂ)` (two terms suffice — a Riemann surface has cohomological
  dimension 1, so a disk-cover is Leray and `H^{≥2}=0`). `H¹(𝔘,𝒪_D) := homology at degree 1`.
- **Cover-independence is deferred.** Forster fixes one cover and never refines; do the same. (Leray
  `H¹(𝔘)=H¹(X)` needs `H¹(disk,𝒪)=0`, itself a consequence of G1 ∂̄-on-a-disk — provable later if
  ever needed, but the RR proof does not need cover-independence.)

**Why not abstract `Sheaf.H`.** Mathlib's `CategoryTheory.Sheaf.H` is `Ext`-from-the-constant-sheaf
(Joël Riou). It is *present and verified* but is the wrong tool: (i) there is no `𝒪_D` sheaf on a
complex manifold to feed it (no structure sheaf on `Geometry/Manifold` — VERIFIED absent); (ii) even
with one, the Montel finiteness argument needs to grab the *cochain Banach spaces* and run a
compact-operator estimate, which the Ext definition hides. The concrete complex exposes them.

**What we still borrow from the abstract toolkit (VERIFIED present at pin):** `ShortComplex.SnakeInput`,
`Algebra/Homology/HomologySequence*` (LES from a SES of complexes), `HomologicalComplex.eulerChar`
(+ additivity), `Topology/Sheaves/Skyscraper`. These run on the concrete `ModuleCat ℂ` cochain
complexes — so the skyscraper SES → LES → "χ jumps by 1 per point" bookkeeping is *not* greenfield.

---

## Per-node feasibility (VERIFIED inventory)

| Node | What it is | Mathlib / repo support (VERIFIED) | Risk | LoC |
|---|---|---|---|---|
| **G1** ∂̄-disk atom | `∂̄u=g` solvable, `g` cpt-supp `C^∞` | **DONE** — `DbarDisk.dbar_solvable_of_compactSupport` (Cauchy–Pompeiu, axiom-clean) | — | 0 |
| **G2** globalize ∂̄ | `∂̄u=g` on compact `X` | Partition of unity `SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source` + G1 per chart | Med | 300–600 |
| **G3a** disk-Montel | bounded holo family ⇒ loc-unif-conv subseq, limit holo | **Primitives off-the-shelf**: `Analysis/Complex/LocallyUniformLimit` (`TendstoLocallyUniformlyOn.differentiableOn`, `cderiv` Cauchy bounds) + Arzelà–Ascoli + Riesz. Repo wrappers (`Montel/Compactness.lean`: `analyticOn_of_tendstoLocallyUniformlyOn`, `uniformEquicontinuousOn_of_bounded_analyticOn`) reusable. **Repo's Ω(X)-Montel is *not* directly reusable** (different space) but its disk-level lemmas are. | Low–Med | 400–800 |
| **G3b** finiteness `H¹(𝔘,𝒪_D)<∞` (Forster 14.9) | Schwartz lemma: compact restriction ⇒ finite codim | **Engine present, packaging absent**: `IsCompactOperator` (`Operator/Compact.lean`), `RieszLemma`, spectral Fredholm (`FredholmAlternative.lean` — the closed-`range(Sⁿ)`/antilipschitz/Riesz technique is *exactly* Forster 14.9's). No packaged "id+compact ⇒ finite-codim". | Med | 800–1500 |
| **χ-additivity** | skyscraper SES → LES → `χ(D)=deg D+χ(0)` | Abstract homology toolkit present (above); work = build the **SES of concrete cochain complexes** `0→C(𝒪_D)→C(𝒪_{D+P})→C(ℂ_P)→0` + exactness, then turn the crank. `Divisor.deg_add/_single` present. | Low–Med | 400–800 |
| **`χ(0)=1−g₁`** | `l(0)=1` (Liouville) ⊕ `g₁:=dim H¹(X,𝒪)` | `l(0)=1` **already proven** (`lDim_zero_eq_one`, Liouville). `g₁` is *defined* by the finiteness above. | Low | ~50 |
| **G4** Serre duality | `H¹(X,𝒪_D)≅Ω(−D)^*` (perfect residue pairing) | **The irreducible nugget.** Dolbeault `H¹≅H^{0,1}` + Hodge-star/conjugation pairing. No Mathlib scaffold. Repo's CutSurface/Green stack supplies the pairing's *integral* side only. | **High** | full 2000–4000 / **`D=0` only 1000–2000** |
| **`deg_div`** | principal divisor has degree 0 (∑Res=0) | Manifold residue theorem; rides the same Stokes build as G4's pairing. Green stack integrates only pole-free forms today. | High | 400–900 |

---

## The scoping win, in detail — `#1-forward` needs only `D=0` Serre

Cohomological RR (the "Riemann part", from χ-additivity + finiteness, **no Serre duality**):
```
χ(D) := l(D) − h¹(D) = deg D + χ(0) = deg D + 1 − g₁,   g₁ := h¹(0) = dim H¹(X,𝒪).
```
Genus-0 forward wants `l(P)=2` for a point `P` (then the one-pole function gives the degree-1 map to
ℙ¹ ≃ₜ S²; that reduction is **already proven**). Apply at `D=P` (`deg P=1`):
```
l(P) − h¹(P) = 2 − g₁.
```
The skyscraper LES `0→𝒪→𝒪_P→ℂ_P→0` gives `H¹(𝒪_P)` as a quotient of `H¹(𝒪)` (skyscraper has no
`H¹`), so `h¹(P) ≤ h¹(0) = g₁`. Hence **if `g₁ = 0` then `h¹(P)=0` and `l(P)=2`.** Since `genus X = 0`
means `g := dim Ω(X) = 0`, all we need is `g₁ = g` — the **`D=0` case of Serre duality**. The full
`l(K−D)=h¹(D)` for general `D` is **not** needed for the headline; it is needed only for the clean
general RR statement and for `#3` (Abel, via Kleinerman's `h⁰(Ω(P+Q))=g+1`).

**Interface note (flag for the user — *not* relocation).** The committed sorry
`exists_riemannRoch_divisor` is stated for *all* `D` with the `l(K−D)` term, so discharging it
*as written* needs full Serre. The genus-0 endgame can instead be re-derived from the strictly weaker,
genuinely-provable pair {cohomological RR, `g₁=g`} + `deg_div`. That is proving a *truer* statement
closer to the analysis, not a `Data`-typeclass that hides the gap — but it does change the RR
interface, so it is a decision to make explicitly, not silently.

---

## Refined cost & risk — the "3k vs 6k" answer

- **De-risked scaffold (cohomological RR):** G2 + G3a + G3b + χ-additivity + `χ(0)` ≈ **2–4k LoC,
  Med risk.** Every hard analytic primitive is present (∂̄-disk done; Vitali/Montel, compact
  operators, Riesz, abstract homology all in Mathlib). The only genuinely-new analysis is the
  Schwartz finiteness assembly (G3b). This scaffold is *independently valuable*: it yields the Riemann
  inequality and the entire χ machinery, and isolates the remaining analytic inputs to exactly two.
- **Concentrated Dolbeault/Serre core:** `D=0` Serre ≈ **1–2k**, full Serre ≈ **2–4k**, **High risk** —
  the irreducible greenfield, no scaffold. `deg_div` (**400–900**) rides the same Stokes build.
- **So the wall is bimodal**, not uniform. Full sorry-free RR ≈ **4–8k**, of which ~3k is
  de-risked-assembly and ~2–4k is the high-variance Dolbeault nugget. For the *headline* (`#1`-fwd),
  the high-risk part scopes down to ~1–2k (`D=0` Serre) + `deg_div`.

This refines the earlier `9–18k monolithic / HIGH` estimate **down and apart**: the monolith was
overstated because it didn't credit the now-confirmed Mathlib primitives, and the right move is to
build the de-risked scaffold first so the Dolbeault core is attacked *in isolation, last, smallest*.

---

## Recommended build order

1. **G2 — globalize ∂̄** on compact `X` (partition of unity + G1). Concrete, medium, unblocks
   everything analytic. *Good first empirical validation of the scaffold estimate.*
2. **Concrete Čech layer** — `𝒪_D(U)`, the two-term `CochainComplex (ModuleCat ℂ)`, `H¹`. Reuse
   `chartCover` + the `germZero` junk-quotient.
3. **G3b finiteness** — disk-Montel compact restriction + Schwartz/Riesz–Schauder ⇒ `H¹(𝔘,𝒪_D)<∞`.
   The single largest scaffold node; its primitives are all present.
4. **χ-additivity** — skyscraper SES of cochain complexes + the abstract LES/`eulerChar` ⇒
   cohomological RR `l(D)−h¹(D)=deg D+1−g₁`. Lands the Riemann inequality.
5. **`deg_div`** — manifold residue ∑Res=0 (extend Green/CutSurface to meromorphic forms). Shares
   machinery with step 6; also discharges the standalone `Res` sorry.
6. **`D=0` Serre (`g₁=g`)** — the Dolbeault nugget, smallest form. Discharges `#1-forward` (with the
   re-derivation from cohomological RR). *Then* generalize to full Serre for the clean all-`D` RR and
   `#3`.

After the trunk lands, the branches are thin glue already scoped in `STATUS.md` / the research docs:
`#7` cut-chart via the Hodge reuse, `#1-backward` (`genus` topological) via de Rham, `#3` via
RR + the reciprocity law (CutSurface stack, already built).

---

## What this probe did NOT de-risk (honest residual)

The **Dolbeault core itself** (G3b finiteness end-to-end, and the `H^{0,1}` half of Serre) is
*structurally* de-risked (primitives identified, representation fixed) but not *empirically* — no Lean
was written. The genuine remaining uncertainty is whether the Schwartz finiteness (G3b) and the
`H^{0,1}` conjugation pairing assemble as cleanly as the primitive inventory suggests. **Next probe to
collapse that uncertainty: actually build steps 1–2 + a skeleton of step 3** (G2 + the concrete cochain
complex + the compact-restriction operator, stopping at the finiteness `sorry`). That ~1–2 day spike
would convert the G3b estimate from "believed" to "measured" and either confirm the ~3k scaffold or
expose a hidden snag before the big commit.

---

## Evidence appendix (VERIFIED this session)

- `Jacobians/DbarDisk.lean:644` `dbar_solvable_of_compactSupport` — G1 done.
- `Jacobians/Montel.lean` — `FiniteDimensional ℂ (HolomorphicOneForms X)` is finiteness of **Ω(X)**
  (via `closedBall_isCompact`/Riesz), *not* `H¹(𝒪_D)`. Its only open `sorry` is the bundle-Montel
  `exists_convergent_subseq_of_bounded` (Ω(X)-specific). Disk-level wrappers in `Montel/Compactness.lean`
  are reusable.
- Mathlib `Analysis/Complex/LocallyUniformLimit.lean` — `TendstoLocallyUniformlyOn.differentiableOn`,
  `cderiv`/`norm_cderiv_le` Cauchy bounds, `TendstoUniformlyOn.cderiv`. The disk-Montel analytic core.
- Mathlib `Analysis/Normed/Operator/`: `Compact.lean` (`IsCompactOperator`), `FredholmAlternative.lean`
  (spectral Fredholm via closed `range(Sⁿ)` + Riesz lemma + antilipschitz), `RieszLemma`, `Banach.lean`.
- Mathlib (per `riemann_roch_proof_plan.md §4`, verified at this pin): `ShortComplex.SnakeInput`,
  `HomologySequence`, `HomologicalComplex.eulerChar`, `Skyscraper`, `Sheaf.H`/`Cech` (abstract).
  **Absent**: structure sheaf on a manifold, coherent-sheaf finiteness, Serre duality, Dolbeault,
  Weil/Cartier divisor / `O(D)`, residue theorem / `deg(div f)=0`, complex ℙ¹-as-manifold.
- `Jacobians/RiemannRoch.lean` — `linearSystem`/`orderW`/`germZeroSubmodule`/`lDim` defs present;
  `exists_riemannRoch_divisor` (271, all-`D`) + `deg_div` (278) the only sorries; `lDim_eq_zero_of_deg_neg`
  (negative-degree vanishing) proven from `deg_div`; `lDim_zero_eq_one` (`l(0)=1`, Liouville) proven.
- `Jacobians/Discharge/Manifold/MeromorphicDivisor.lean` — `orderFun`/`divisor`/`zeros_finite`/
  `poles_finite`, the manifold order/divisor layer for `𝒪_D(U)`.
