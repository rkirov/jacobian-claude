# Gate A wall 1 (`AdaptedCover` existence): genuine book requirement, or formalization over-engineering?

**Date:** 2026-06-08 · **Mode:** READ-ONLY textbook re-reading (no Lean edits/builds) · **Sources read
this session:** Miranda §VIII.3 (printed pp. 251–256), Forster GTM 81 §16 (pp. 127–131) and **all of
§17** (pp. 132–145) and §18.7–18.9 (pp. 149–152).

---

## VERDICT

**Wall 1 (`AdaptedCover` existence — the demand that the branched cover `f` be a *regular non-pole*
at every pole of `α = ω₀·g`) is a FORMALIZATION OVER-ENGINEERING, not a genuine book requirement.**

- It is **NOT** needed by the §VIII.3 residue-theorem argument. Miranda's argument **explicitly
  tolerates ramified fibres, including fibres that contain poles of `α`**, handling them via the
  `z = wᵐ` normal form and formula **(3.1)** (Miranda p. 253). The only thing his Step 1 asks of `f`
  is "**nonconstant**" — verbatim "simply choose *any* nonconstant meromorphic `f`" (p. 254).
- It therefore needs **NO Riemann–Roch-with-prescribed-jets**. The repo's current docstrings
  (`FormTraceGateAAssemble.lean:38–41`) assert wall 1 "needs Riemann–Roch with *prescribed local
  jets*". **That assertion is mathematically false for this argument.** The book needs only the weak
  existential "a nonconstant meromorphic `f` exists" (Miranda's "immediate when `X` is algebraic";
  Forster's RR Cor. **16.11/16.12**, which the repo *already has* as `exists_riemannRoch_divisor` →
  `exists_singleSimplePole…`). Jets are needed only to make `f` *regular at chosen points*, which the
  book never requires here.
- **Stronger conclusion (the cleanest path):** for the *purpose Gate A actually serves* (descending
  `residueSum` to `H¹(X,Ω)`, see §5), the cover/trace route is **one of two textbook routes**, and the
  cover is not even forced. Forster proves the *same* residue theorem with **no cover at all** (§17.1–
  17.3, 17.11). So wall 1 can be (i) **weakened to just "`f` nonconstant"** if we keep the Miranda
  trace route — but that requires teaching the Lean `FibreTrace` the ramified `z=wᵐ` case — or
  (ii) **eliminated entirely** by switching to the cover-free cohomological residue theorem.

The decision this resolves: **do NOT grind RR-with-jets.** Either drop the regularity hypotheses
(handling ramified pole fibres via the SUM + (3.1)), or drop the cover.

---

## (A) Does the book's residue-theorem argument require `f` regular/unramified/non-pole at poles of `α`?

**No.** Quoting the two relevant sources.

### Miranda §VIII.3 (the trace route the repo follows)

The whole point of the "Trace of a 1-Form" subsection (pp. 252–253) is to show `Tr(ω)` is a *bona
fide* meromorphic 1-form on `Y` **across branch points**, i.e. precisely where `f` is *ramified*:

> *"To see that Tr(ω) extends nicely across the branch points, we make a computation similar to what
> we did above for the functions. Again we may assume that `q` has a single preimage `p`, with
> multiplicity `m`, and we may choose centered coordinates `z` and `w` such that `F` has the form
> `z = wᵐ`. We then write `ω = h(w)dw`, where `h` has a Laurent series `Σₙ cₙwⁿ`… we may write
> `ω = [h(w)/m·w^{m−1}]dz`. We have the formula (valid for nonzero `z = wᵐ`) … "*
> — **Miranda, p. 252–253**

leading to

> **(3.1)** `Tr(ω) = Σₖ c_{km−1} z^{k−1} dz`, *"which shows that Tr(ω) is also meromorphic at `q`, and
> indeed is holomorphic if `ω` is holomorphic at the preimages of `q`."* — **Miranda, p. 253**

So `Tr(ω)` is meromorphic at *every* `q ∈ ℂ_∞`, **ramified or not, pole-containing or not**. There is
no exclusion of fibres containing poles of `ω = α`.

**Lemma 3.2** (the fibrewise residue identity, the repo's `resAt_traceCoeff'`) is then proved *at
ramified fibres explicitly*:

> **Lemma 3.2.** *Let `F : X → Y` be a nonconstant holomorphic map of compact Riemann surfaces, `ω` a
> meromorphic 1-form on `X`. Then for any `q ∈ Y`, `Res_q(Tr(ω)) = Σ_{p∈F⁻¹(q)} Res_p(ω)`.*
> **Proof.** *"It suffices to check that the residues are equal if the preimage of `q` is a single
> point `p`, with multiplicity `m`. Using the notation above, we have that `Res_p(ω) = c_{−1}`, the
> coefficient of `w⁻¹` in the Laurent series for `ω`. By (3.1), this is also the coefficient of `z⁻¹`
> in the Laurent series for Tr(ω)."* — **Miranda, p. 253**

The proof's *representative case is the ramified one* (`m`-fold single preimage). Ramified pole fibres
are not merely "tolerated" — they are the case Miranda actually writes down.

And **Step 1** of the algebraic proof asks nothing of `f` beyond nonconstancy:

> *"The first part is immediate when `X` is an algebraic curve; simply choose any nonconstant
> meromorphic function `f` on `X` and `F` be the associated holomorphic map to `ℂ_∞`. The assumption
> that `X` is algebraic is used simply to guarantee the existence of a single such `f`."* —
> **Miranda, p. 254**

No regularity, no non-pole-over-poles, no unramified-over-poles condition anywhere in pp. 251–256.

### Forster GTM 81 §17 (the cover-free route — even stronger evidence)

Forster proves the residue theorem **without any branched cover `f` at all**. His residue functional

> **17.1. Definition of a Linear Form `Res: H¹(X,Ω) → ℂ`.** `Res(ξ) := (1/2πi) ∬_X ω`, where `ω ∈
> 𝓔^{(2)}(X)` represents `ξ` under the Dolbeault iso `H¹(X,Ω) ≅ 𝓔^{(2)}(X)/d′𝓔^{1,0}(X)`. —
> **Forster p. 132**

and the residue theorem proper,

> **17.3. Theorem.** *`Res(μ) = Res([δμ])`* (Mittag–Leffler distribution `μ` of 1-forms), proved by a
> **partition-of-unity + Stokes (10.20)** computation. — **Forster pp. 133–134**

with the consequence (the classical `∑Res = 0`):

> **17.11. Consequence.** *For `D = 0` … the mapping `Res: H¹(X,Ω) → ℂ` is an isomorphism.* —
> **Forster p. 139**; and Ex. 17.2 / §15.3 give `H¹(X,ℂ) ≅ Ω(X)/d𝓜(X)`, the cohomological form of
> "a global meromorphic 1-form has total residue 0".

Forster uses **no `f`, no fibres, no branch points** for the residue theorem. (His §17.14 Riemann–
Hurwitz *does* use a cover, but that is a different theorem.) This independently confirms: the cover
and its genericity are an *artifact of the chosen route*, not intrinsic to the residue theorem.

---

## (B) Does the book need Riemann–Roch *with prescribed local jets*, or only "a nonconstant `f` exists"?

**Only the weak existential.** Neither book uses RR-with-jets for the residue theorem.

- **Miranda** invokes nothing beyond "`X` algebraic ⟹ a nonconstant meromorphic `f` exists" (p. 254,
  quoted above). That is the bare existence statement.
- **Forster's** route needs *no* meromorphic function at all (it is cohomological, §17.1–17.3).
- The general source of "a nonconstant meromorphic function exists on a compact Riemann surface" is
  **Forster Theorem 16.11 / Corollary 16.12** (p. 130–131): *"there is a non-constant meromorphic
  function `f` with a pole of order `≤ g+1` at `a`"*, proved straight from **Riemann–Roch**
  (`dim H⁰(X, 𝒪_D) ≥ 1 − g + deg D = 2` for `D = (g+1)·a`). This is the **weak `lDim ≥ 2`** statement.

**Repo status:** the repo *already proves* exactly this. `RiemannRoch.exists_riemannRoch_divisor` +
`exists_singleSimplePole_of_genus_zero_of_rr` / `RRScout` produce a nonconstant meromorphic function
from the Riemann *inequality* `2 ≤ lDim (single P 1)` — the same Forster 16.11 content. So the "weak
existential" wall 1 *actually* needs is already in hand; **the gap is purely the regularity/non-pole
extras that `AdaptedCover` bolts on**, which the book never asks for.

**Where jets *would* be needed (and are not):** RR-with-prescribed-jets (an `f` immersive/regular at
finitely many chosen points) is the machinery to *force `f` unramified over a prescribed finite set*.
That is exactly the `AdaptedCover` over-specification. The book sidesteps it (Miranda via (3.1),
Forster via no cover), so the repo can too.

---

## (C) The book's route to ramified pole fibres, and whether our SUM can absorb it

### What the book does (Miranda)

Over a **ramified** fibre (single preimage `p`, multiplicity `m`), Miranda does **not** write `Tr(ω)`
as a sum of `m` distinct biholomorphic-sheet pullbacks. Instead he uses the **single `z=wᵐ` normal
form** and reads the trace off the Puiseux/Laurent expansion directly:

`ω = h(w)dw`, `dz = m·w^{m−1}dw`, so `ω = [h(w)/(m·w^{m−1})]dz`; summing over the `m` sheets `ζⁱw`
(`ζ = e^{2πi/m}`) the only surviving terms are `n = km−1`, giving **(3.1)** `Tr(ω) = Σₖ c_{km−1}
z^{k−1}dz`. The residue `c_{-1}` upstairs (`k=0`) is the `z⁻¹` coefficient downstairs (Lemma 3.2).

The general fibre (several preimages of various multiplicities) is the *sum* of these per-preimage
local traces (Miranda p. 252, "the trace … is simply the sum of the traces obtained from
neighborhoods of each preimage point"). So the book's `Tr(ω)` is **fibre-additive**, with each
preimage contributing its (possibly ramified) (3.1) local trace.

### Can our bundle-SUM trace absorb it?

**Yes — and this is exactly why wall 1 can be dropped/weakened.** Three observations:

1. **The trace extends across *all* branch values, pole-fibres included.** The repo's own design note
   (the `infty_eq` circularity analysis, `FormTraceGlobalConstruct.lean:51–60`, and `MittagLeffler.lean`
   docstring) already builds `Tr_F α` as a global meromorphic function on the *compact* `ℂℙ¹` whose
   only requirement is meromorphy at the finite exceptional set ∪ {∞}. Meromorphy at a *ramified
   pole value* is supplied by (3.1) — the same `z^{k−1}` principal part — not by an unramified-sheet
   sum. The global SUM-trace (a section of the pushforward bundle that extends across all branch
   values) is *precisely* Miranda's fibre-additive `Tr`.

2. **The over-engineering is localized in one Lean structure field.** The driver of wall 1 is
   `MeromorphicTrace.FibreTrace.sheet_deriv_ne : ∀ i, deriv (sheet i) b ≠ 0`
   (`Jacobians/MeromorphicTrace.lean:326`) and its consumer `FibreRegularData.ofRegular`'s `hderiv`
   (`Jacobians/Dolbeault/FormTraceFibre.lean:193`). `FibreTrace` models the trace as a sum of `d`
   **local biholomorphic inverse sections `φᵢ` with nonzero derivative** — i.e. the *unramified*
   picture only. It literally cannot represent a single ramified `z=wᵐ` sheet. `AdaptedCover` exists
   *solely to make this unramified model applicable over the finitely many pole-values*
   (`FormTraceGlobalConstruct.lean:104–106`: "the honest geometric input the unramified-fibre
   `FibreTrace` machinery consumes"). The book requirement is weaker; the Lean structure is stronger.

3. **Two concrete ways to discharge wall 1 without RR-with-jets:**

   **(C-route i) Weaken `AdaptedCover` to "`f` nonconstant", teach `FibreTrace`/Lemma 3.2 the
   ramified case.** Add a *ramified* fibre datum (single preimage, normal form `z = wᵐ`) and prove
   the (3.1)-version of `resAt_traceCoeff'` there: `res` of the `z=wᵐ` local trace = `c_{-1}`
   upstairs. This is Miranda's Lemma 3.2 proof verbatim (a Puiseux/Laurent-coefficient identity, the
   same `ResidueChangeOfVariables` residue-of-pushforward atom specialized to `w ↦ wᵐ` instead of a
   biholo). Then **drop `hnp`/`hderiv`** from `AdaptedCover` (keep only `hdiv : f.div ≠ 0` and
   `hg_mero` — the latter is just "`α·g` has an isolated singularity at each pole", which is true for
   any meromorphic `α` and is *not* a genericity demand). The fibre enumeration (`fibreReg`,
   `fibreEnum_*`) is already route-agnostic; only `ofRegular`'s `hderiv` consumer needs the ramified
   branch. **Cost:** one new local lemma (the `z=wᵐ` Lemma 3.2 case) + a small refactor of
   `FibreRegularData` to admit ramified preimages. **No RR-with-jets, no genericity perturbation.**

   **(C-route ii) Eliminate the cover entirely — Forster's cohomological residue theorem.** Define
   `Res: H¹(X,Ω) → ℂ` à la Forster 17.1 and prove `∑Res = 0` via 17.3/17.11. This deletes
   `AdaptedCover`, `TraceRationalityWitness`, `FibreTrace`, the whole `FormTrace*` cover stack, and
   wall 1 *and* the trace-rationality wall in one move. **Cost:** it needs manifold Stokes / the
   `(1/2πi)∬_X` integral (the repo's stated reason for *not* taking this route —
   `MittagLeffler.lean:50–52`). So this is only attractive if/when manifold-2-form integration lands.
   For the *near-term*, **C-route i is the recommended path**: it stays inside the repo's existing
   trace machinery and only swaps the over-strong unramified hypothesis for the book's actual
   normal-form handling.

**Net:** the bundle-SUM does absorb ramified pole fibres (that is what (3.1) is for); wall 1 is the
artifact of an unramified-only Lean `FibreTrace`. **Wall 1 can be WEAKENED to "`f` nonconstant"**
(C-route i) and the deep RR-with-jets is **never** needed.

---

## (D) Does *any* step genuinely need `f` simple/unramified somewhere?

**Not for THIS residue theorem.** Distinguishing carefully:

| Step | Needs `f` unramified/regular? | Where it lives |
|---|---|---|
| Step 1: pick nonconstant `f` | **No** — only `f` nonconstant (Miranda p. 254). | RR weak existence — repo has it. |
| `Tr(ω)` meromorphic on `ℂℙ¹` | **No** — (3.1) covers ramified + pole fibres (Miranda p. 253). | the trace-rationality content. |
| Lemma 3.2 (fibre residue identity) | **No** — proved *at* ramified fibres (Miranda p. 253). | `resAt_traceCoeff'` (+ ramified case for C-route i). |
| `ℂℙ¹` residue thm on `Tr(ω)` | **No** — partial fractions on `ℙ¹` (Miranda p. 254). | `finiteResidueSum_add_resAtInfty_eq_zero` (proved). |
| Combine (Step 4–5) | **No** — fibre bookkeeping only (Miranda p. 254). | `FormTraceGlobal` descent (proved). |

The trace `Tr(ω) = Σᵢ φᵢ*(ω|_{Vᵢ})` is *defined* over **non-branch** points (`d` distinct sheets,
Miranda p. 252–253), so the unramified picture is the *generic-fibre* definition — but the theorem's
correctness does **not** require the *pole* fibres to be generic; those are handled by (3.1).

**Where unramifiedness IS genuinely needed — elsewhere, not here:**

- **Forster 18.7–18.9 (Weierstrass points / hyperelliptic Cor. 18.9)** and the **Riemann–Hurwitz
  formula (Forster 17.14)** genuinely use branching data, but that is a *different* theorem (counting
  Weierstrass points / relating genera), not the residue theorem.
- **The repo's `exists_properMapDegree` / `deg_div`** (already CLOSED, `ProperMapDegreeSheets.lean`)
  uses a *generic regular value* (a fibre of `d` distinct simple points) — but that is the
  **degree/sheet-count** argument, explicitly the special case `α = df/f` (orders, not Laurent
  residues), and per `MittagLeffler.lean:43–52` it is **NOT** this 1-form residue theorem. So even the
  one place the repo legitimately uses a generic *regular value* is a different node.

Conclusion for (D): **no step of the §VIII.3 residue theorem needs `f` simple/unramified at the poles
of `α`.** The genericity that appears elsewhere (deg_div, Riemann–Hurwitz, Weierstrass) is for other
theorems and does not back-justify `AdaptedCover`.

---

## What `AdaptedCover` currently demands vs. what the book needs

`AdaptedCover` (`Jacobians/Dolbeault/FormTraceGlobalConstruct.lean:107–118`) has four fields:

| Field | Demands | Book need? |
|---|---|---|
| `hdiv : f.div ≠ 0` | `f` nonconstant | ✅ **YES** (Miranda Step 1; the only real requirement). |
| `hnp` : non-pole of `f` at every finite-value pole of `α` | `f` regular*ish* over poles | ❌ **NO** — over-engineering; (3.1) handles pole fibres. |
| `hderiv` : chart-pullback deriv `≠ 0` at every finite-value pole | `f` **unramified** over poles | ❌ **NO** — the core over-specification (drives `sheet_deriv_ne`). |
| `hg_mero` : `g`'s chart-pullback meromorphic at each pole | `α·g` isolated singularity | ✅ harmless — true for any meromorphic `α`, not a genericity demand. |

The two ❌ fields (`hnp`, `hderiv`) are *exactly* the unramified-over-poles condition Miranda's (3.1)
makes unnecessary. They are present only to satisfy the unramified Lean `FibreTrace`. **Drop them**
(C-route i) and wall 1 collapses to `hdiv` (free from RR-weak-existence, already proven) + `hg_mero`
(free for meromorphic `α`).

---

## Cross-check against the prior confirmation doc

`docs/miranda_VIII3_confirmation_2026-06-08.md` (§3.1, "Ramification points / adapted cover") already
recorded: *"Miranda's argument tolerates ramified-over-pole fibres (Lemma 3.2 holds there via (3.1)).
Our `AdaptedCover` additionally demands `F` unramified over the finite pole-values… This is a strictly
stronger genericity hypothesis than Miranda strictly needs."* **This session confirms that note from
the primary text and upgrades its consequence:** because it is strictly stronger and the book route to
the weaker version is concrete ((3.1) + the ramified Lemma 3.2), wall 1 is droppable WITHOUT
RR-with-jets. The prior doc framed `AdaptedCover` as "a sound simplifying choice" needing a deferred
*genericity perturbation* (gate D). **That framing is wrong on the cost:** the cheaper move is not to
*build* the genericity (perturb `f` off the poles — which is what would tempt RR-with-jets), but to
*remove the need for it* via (3.1). The repo's `FormTraceGateAAssemble.lean:38–41` claim that wall 1
"needs Riemann–Roch with prescribed local jets" should be **corrected**: it does not.

---

## Bottom line / recommendation

- **Wall 1 is formalization over-engineering (option (ii)).** It is not a genuine §VIII.3 requirement
  and needs no Riemann–Roch-with-jets.
- **Do not grind RR-with-jets.** Instead:
  - **Primary (near-term):** *weaken* `AdaptedCover` to just `hdiv` (`f` nonconstant) + `hg_mero`,
    and add the ramified `z=wᵐ` case of Lemma 3.2 to `FibreTrace`/`FibreRegularData` (Miranda (3.1),
    p. 253). This stays inside the existing trace stack; the only new content is one Puiseux-coefficient
    residue lemma (a `w↦wᵐ` specialization of the already-proven `ResidueChangeOfVariables` atom).
  - **Alternative (if manifold Stokes lands):** *eliminate* the cover via Forster's cohomological
    `Res: H¹(X,Ω)→ℂ` (§17.1–17.3, 17.11), deleting `AdaptedCover` + `TraceRationalityWitness` +
    the whole `FormTrace*` cover stack at once.
- The weak existential the book *does* need ("a nonconstant meromorphic `f` exists" = Forster 16.11,
  the Riemann inequality `lDim ≥ 2`) is **already proven in the repo**
  (`exists_riemannRoch_divisor` → `RRScout`/`exists_singleSimplePole…`), so even after weakening,
  `∃ f, AdaptedCover` is discharged from existing nodes.

### Exact citations
- Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3: trace of a 1-form **pp. 252–253**;
  normal-form formula **(3.1)**, p. 253; **Lemma 3.2** (ramified-fibre residue identity), p. 253;
  algebraic residue theorem Step 1 "*any nonconstant meromorphic `f`*", **p. 254**.
- Forster, GTM 81, §17: **17.1** `Res: H¹(X,Ω)→ℂ` def (p. 132); **17.3** `Res(μ)=Res([δμ])` (pp. 133–
  134); **17.11** `Res` iso for `D=0` (p. 139). Weak meromorphic existence: **16.11/16.12** (pp. 130–
  131, from Riemann–Roch). Riemann–Hurwitz (a *different* theorem using branching): **17.14**, p. 145.
- Repo: `AdaptedCover` def `FormTraceGlobalConstruct.lean:107–118`; the over-engineering driver
  `FibreTrace.sheet_deriv_ne` `MeromorphicTrace.lean:326` + `FibreRegularData.ofRegular`'s `hderiv`
  `FormTraceFibre.lean:193`; the false "RR-with-jets" claim `FormTraceGateAAssemble.lean:38–41`; the
  route note `MittagLeffler.lean:43–52`; prior confirmation `docs/miranda_VIII3_confirmation_2026-06-08.md`.
