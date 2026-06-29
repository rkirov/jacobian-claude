# Clean-room hint: proving the Jacobians challenge from scratch

*A "modulo hint": the path to the whole proof, the genuinely hard steps, the routing
decisions that are not obvious from the textbooks, and where to read each piece. It
deliberately gives no Lean — only the mathematics and the strategy, so the formalization
can be reconstructed independently.*

## What is to be proved

Buzzard's v0.4 API for a compact connected Riemann surface `X`:

- `genus X` (= dim of global holomorphic 1-forms) is well-defined and finite;
- the **headline**: `genus X = 0 ↔ X ≃ₜ S²`;
- the `Jacobian X = ℂ^g / Λ` is a complex torus / Lie group (period lattice `Λ` full rank `2g`);
- the Abel–Jacobi map `ofCurve : X → Jacobian X` is smooth and **injective** for `g ≥ 1`;
- functoriality `pushforward`/`pullback` and `ContMDiff.degree` with `pushforward_pullback`.

Everything is built from scratch over current Mathlib — no future-Mathlib algebraic geometry,
no scheme theory, no abstract sheaf cohomology library. The whole edifice is analytic and
hand-built. Plan ~60k lines of Lean, ~30 chapter-sized units.

## References (and which one to trust per topic)

- **Forster, *Lectures on Riemann Surfaces* (GTM 81)** — the spine. Use it for the ∂̄/Dolbeault
  lemma (§13–15), finiteness of `H¹` (§14), the residue theorem (§10), Serre duality and
  Riemann–Roch (§16–17), Abel's theorem (§20), and the period lattice (§21). Forster's analytic,
  cohomology-first development is the one that formalizes.
- **Miranda, *Algebraic Curves and Riemann Surfaces* (GSM 5)** — use it for the **Laurent-tail**
  presentation of `H¹`, Riemann–Roch, and Serre duality (Ch. VI). This is the route that actually
  closes Serre duality concretely; prefer it to abstract duality.
- **Griffiths–Harris, *Principles of Algebraic Geometry*** — background only, for the Jacobian /
  Abel–Jacobi picture and intuition on periods. Do **not** try to follow its Hodge-theoretic
  development; the Hodge route is a trap here (see the routing warnings below).

## The four targets and the spines that feed them

The proof is four interlocking arguments.

1. **Headline forward (`g=0 ⇒ S²`)** needs only the **Riemann inequality** half of Riemann–Roch:
   a genus-0 surface admits a meromorphic function with a single simple pole, i.e. a degree-1 map
   to `ℙ¹`, which is a homeomorphism. It does **not** need full deg(K−D) bookkeeping or Serre
   duality. Headline backward (`S² ⇒ g=0`) is pure topology (π₁ S² = 0).
2. **Riemann–Roch + Serre duality** (the analytic make-or-break) — the cohomology spine:
   ∂̄ on disks → Čech `H¹(𝒪_D)` finite → Dolbeault comparison → Laurent-tail RR → tail Serre duality.
3. **Residue theorem `∑ Res = 0`** — partition of unity + planar Stokes; genus-agnostic.
   Feeds Serre duality and Abel.
4. **Abel + period lattice** — Abel's two-point nonvanishing (g≥1) and the rank-`2g` real basis
   of the period lattice, both via Forster's *dissection-free* §20–21 arguments.

The 30 units below. Each entry ends with its direct dependencies (**Builds on**); those edges
*are* the whole dependency DAG — reconstruct it, and any valid build order, from them. The units
happen to be listed in one such order, but nothing here relies on that. Each entry: what it gives,
the strategy, the key object, where to read, and **⚠ the trap**.

---

## The units

### surfaces-and-charts  (`Surface/`)
Riemann-surface foundations: a `ChartedSpace` from local homeomorphisms, transport of the manifold
structure, the **holomorphic inverse function theorem** on manifolds, and the underlying real
2-manifold. The holomorphic IFT is the foundation everything local (normal forms, multiplicity)
rides on. Read: Forster §1, §A (charts); standard complex IFT.
⚠ The real-2-manifold instance and the ℝ↔ℂ tangent identification are a recurring source of
typeclass/`restrictScalars` diamonds; pin down `extChartAt 𝓘(ℝ,ℂ) = extChartAt 𝓘(ℂ)` (it is `rfl`).
**Builds on:** — (foundation)

### local-multiplicity  (`LocalMultiplicity/`)
Local theory at a point: analytic factorization `f(z) = z^k · unit`, derivative orders, local
multiplicity of a holomorphic map. Strategy: the Weierstrass-style `z^k·unit` normal form is the
atom for degree, ramification, and the argument principle. Read: Forster §1–2.
⚠ Keep multiplicity defined from the normal form, not from a junk-valued derivative count.
**Builds on:** — (foundation)

### holomorphic-forms  (`Forms/`)
Global holomorphic 1-forms as a smooth-section bundle; **`genus` := dim of that space**; Montel-type
compactness for form/function families. Strategy: fix the genus *definition* here as a finrank, so
later "g" is unambiguous. Read: Forster §9–10. Montel via uniform-on-compacts + Arzelà.
⚠ Summing sections (Finset.sum of forms) trips the section-module instance — work pointwise or fix
the module instance before you need linear-algebra over the form space.
**Builds on:** — (foundation)

### mapping-degree  (`MappingDegree/`)
The degree machine for branched covers: regular values, finiteness of critical values, fibre
counting, and **well-definedness of the degree** (fibre cardinality locally constant ⇒ constant on a
connected base). Largest unit. Strategy: degree = #fibre over a regular value; prove it is locally
constant via the local normal form and Hurwitz patching, then constant by connectedness. Read:
Forster §4, §8; this is portable from existing challenge attempts (Brsanch's degree tree).
⚠ The topology (path-connectedness of base minus a finite/countable set, clopen locally-constant
argument) is most of the work, not the complex analysis.
**Builds on:** local-multiplicity, surfaces-and-charts

### paths-and-integrals  (`Path/`)
Smooth paths/loops, the **line integral** of a 1-form along a path, primitives along paths, and
perturbing a loop off a finite bad set. Read: Forster §10. Strategy: define `∫_γ ω` and prove
homotopy invariance; the off-branch perturbation lemma is needed later for Abel and for monodromy.
⚠ Perturb the loop's *breakpoint values* off the bad set, not the loop pointwise; the naive "move
the path" statement is false/under-determined (needs δ(k/n) ∉ branch locus).
**Builds on:** holomorphic-forms

### residue-calculus  (`ResidueCalculus/`)
Planar residues `resAt`, Laurent coefficients of pair integrands, Mittag-Leffler distributions of
principal parts. Read: Forster §17.1–17.2. Strategy: pure ℂ-plane; this is the local input to the
global residue theorem and to canonical forms.
**Builds on:** holomorphic-forms

### jacobian-construction  (`JacobianConstruction/`)
The Jacobian as `ℂ^g/Λ`: the period lattice as the ℤ-span of loop periods, period vectors, and the
`ZLattice` quotient-manifold/Lie-group structure. Read: Forster §20–21; G–H Ch. 2 for the picture.
This unit supplies the torus *structure* (manifold + group instances) over an abstract lattice; the
*full-rank* fact lives in the period-lattice unit. Mathlib's `ZLattice` gives the quotient.
**Builds on:** mapping-degree, paths-and-integrals

### projective-line  (`ProjectiveLine/`)
`ℙ¹` as the model compact Riemann surface, with its genus-0 facts. Read: Forster §5. This is the
target of the genus-0 headline and the base of every branched cover.
**Builds on:** paths-and-integrals

### meromorphic-and-divisors  (`Meromorphic/`)
Meromorphic functions as germ data, **divisors** (`Finsupp X ℤ`), orders, linear systems `L(D)` and
`l(D) = dim L(D)`; Liouville and normal-form repair. Read: Forster §6, §20. Strategy: represent
`L(D)` junk-free (germs over a codiscrete set), so `l(D)` is an honest finrank.
⚠ A `toFun`-junk representation silently makes `l ≡ 0` and Riemann–Roch *false* — use a germ /
quotient model from the start.
**Builds on:** jacobian-construction

### meromorphic-trace  (`MeromorphicTrace/`)
Surface-level trace of functions/forms along a degree-`d` map, and the **argument principle on `X`**
(zeros = poles for an exact log-derivative trace). Read: Forster §4; Miranda Lemma 3.2 (the residue
identity). Strategy: trace = sum over the fibre; the argument principle is the engine for
`deg(div f) = 0` later.
**Builds on:** jacobian-construction, residue-calculus

### sphere-topology  (`SphereTopology/`)
Topology of `S²`: van Kampen ⇒ simple connectivity ⇒ **backward headline** (`X ≃ₜ S² ⇒ g = 0`).
Read: any algebraic topology text; Forster §10.5 for the analytic consequence. Strategy: a
simply-connected compact surface has no nonzero holomorphic 1-forms (every closed form is exact),
so its genus is 0.
**Builds on:** projective-line

### cech-cohomology  (`Cech/`)
Čech theory for `𝒪_D`: junk-free **germ cochains** over a codiscrete set, the complex, refinements,
chart-disk covers, and **`H⁰ = L(D)`**. Read: Miranda Ch. VI pp. 186–188; Forster §12.
Strategy: the cochain spaces must be germ-valued (over `codiscreteWithin`) to avoid junk; then
`H⁰` is literally the global sections `L(D)`, proved by a rigidified per-point normal form.
⚠ The `H⁰=L(D)` gluing needs a *rigidified* normal form; a naive patch fails at cover boundaries.
**Builds on:** meromorphic-and-divisors

### form-trace-tower  (`FormTrace/`)
Fibrewise trace tower for pair forms `h·ω₀` along `f : X → ℙ¹`: fibre traces, branch handling,
coherent selection, globalization, and **rationality of the traced form**. This is the Gate-A
reduction machinery feeding the residue theorem and Serre. Read: Forster §17; Miranda Ch. VI.
Strategy: push a meromorphic 1-form down to `ℙ¹` as an honest rational form; its residues are the
ones you sum.
**Builds on:** meromorphic-trace

### dbar-solvability  (`Dbar/`)
The intrinsic **`∂̄` operator** on the surface and its local solvability: the planar **Dolbeault
lemma on disks (Forster 13.2)** — `∂̄u = f` solvable on a disk — plus disk acyclicity for the Čech
complex and holomorphic representatives of `∂̄`-closed germs. Read: Forster §13, §15.
Strategy: solve ∂̄ on the open disk by the Cauchy-transform / convolution formula; this single atom
powers all of finiteness and the comparison. Define ∂̄ intrinsically as `proj^{0,1} ∘ d`.
⚠ The `restrictScalars ℂ→ℝ` diamond on tangent spaces breaks definitional equality; you must control
transparency. Build the J/almost-complex smoothness API yourself — Mathlib has none.
**Builds on:** cech-cohomology

### dolbeault-comparison  (`DolbeaultComparison/`)
The **PDE-free** comparison `Čech H¹(X, 𝒪) ≅ H^{0,1}_∂̄(X)`, local realization of cocycles,
Mittag-Leffler gluing, and existence of **Leray covers**. Read: Forster §15 (Dolbeault), §12 (Leray).
Strategy: globalize the disk ∂̄-solution with a partition of unity and patch the discrepancy as a
Čech cocycle. This is the bridge that lets finiteness on the Čech side give finiteness of `H^{0,1}`.
⚠ Do **not** route through Weyl's lemma / elliptic regularity — unnecessary and unformalizable here.
The comparison is the right, PDE-free substitute.
**Builds on:** dbar-solvability

### planar-stokes-atoms  (`PlanarStokes/`)
Planar integration atoms: compact-support **Stokes in the plane**, annulus residue integrals,
holomorphic change of variables for contour integrals. Read: any analysis text; this is the green/
rectangle Green's-theorem seed (portable from tangentstorm's attempt). Strategy: prove the one honest
2-dimensional Stokes you need on rectangles/disks; everything global reduces to it via PoU.
**Builds on:** dbar-solvability, residue-calculus

### finiteness-and-chi  (`Finiteness/`)
**Finite-dimensionality of `H¹(X, 𝒪_D)`** (Forster §14: the Schwartz finiteness theorem via a
compact perturbation, with **Montel** compactness as the functional-analysis input), and the
Euler-characteristic `χ(D)` bookkeeping via skyscraper sequences. Read: Forster §14; Schwartz's
lemma (a compact operator perturbation of an iso has finite-dim cokernel). Strategy: realize `H¹`
as a quotient `Z/B`, exhibit the inclusion of two cover-refinement copies as identity + compact
(Montel), apply Schwartz. Then `χ(D) − χ(D−P) = 1` gives the skyscraper ledger.
⚠ This is the load-bearing analytic unit. The compact operator is `restriction between nested
disk covers`; Montel = bounded holomorphic families are relatively compact in sup-norm.
**Builds on:** dolbeault-comparison

### canonical-forms  (`CanonicalForms/`)
Meromorphic 1-form systems and the **canonical divisor `K`**: removable singularities, differentials
of canonical forms, and — via the χ ledger — **existence of a nonconstant meromorphic function** and
a nonzero `ω₀`. Read: Forster §16, §17.4. Strategy: `χ(D) → ∞` with `deg D` forces `L(D)` nonzero,
giving the first nonconstant meromorphic function; its differential seeds `K`.
⚠ Existence of `ω₀`/nonconstant `f` is a *consequence of finiteness + χ*, not an assumption; this is
where finiteness pays off.
**Builds on:** finiteness-and-chi, residue-calculus

### laurent-tails  (`LaurentTail/`)
Miranda Ch. VI **Laurent-tail calculus**: tail spaces `T[D]`, truncation maps, tail finiteness, and
the **tail form of Riemann–Roch**. Read: Miranda Ch. VI §2 (esp. Lemmas 2.3, 2.6). Strategy: present
`H¹(D)` concretely as Laurent tails modulo global principal parts; RR becomes a dimension count of
truncations. This concrete model is what makes Serre duality provable.
**Builds on:** canonical-forms, meromorphic-trace

### monodromy  (`Monodromy/`)
Global primitives on a simply-connected surface by **discrete analytic continuation** along chains
(no integration): local primitive frames, chain values, homotopy invariance. Read: Forster §10.4;
Miranda Ch. IV §1. Strategy: the monodromy theorem replaces line-integral primitives with a
chain-of-charts continuation, avoiding a manifold integration theory you don't have.
⚠ Prefer this discrete route to anything requiring ∫ over paths on `X` as a primitive.
**Builds on:** canonical-forms, sphere-topology

### residue-theorem  (`ResidueTheorem/`)
The **unconditional residue theorem `∑_p Res_p(h·dg₀) = 0`** for meromorphic pair forms on a compact
`X`, any genus, via partition of unity + planar Stokes. Read: Forster §10 (Thm 10.21);
Miranda Ch. VI pp. 186–188. Strategy: cover `X`, write the form as a sum of locally-supported pieces,
apply planar Stokes to each; the boundary terms cancel and what survives is `∑ Res`.
⚠ Crucial distinction: the residue **theorem** (`∑Res=0`) is genuinely Stokes-only and genus-agnostic.
The residue **functional** `H¹(Ω) → ℂ` of Serre duality is a *different* object that *does* need an
integration atom — the "Stokes-free" shortcut to it is circular (`H¹(ℳ)=0 ← Serre`). Don't conflate.
**Builds on:** canonical-forms, planar-stokes-atoms

### serre-duality-cech  (`SerrePairing/`)
The Serre pairing at the Čech level: the **dimension-counting surjectivity core** and the duality
bookkeeping consumed by the tail route. Read: Forster §16–17. Strategy: this is the interface that
the Laurent-tail unit discharges concretely; keep it a clean dimension statement.
**Builds on:** canonical-forms

### abel-weak-solutions  (`AbelWeak/`)
Weak/planar solution steps for the Abel engine: chain decompositions and piecewise-planar solutions.
Read: Forster §20.1–20.4. Strategy: build the path-integral / chain data that the two-point Abel
nonvanishing will consume, staying in planar pieces glued by monodromy.
**Builds on:** form-trace-tower, monodromy, planar-stokes-atoms

### proper-map-degree  (`ProperDegree/`)
Degree of a global meromorphic map: `ContMDiff.degree`, sheet counting, multiplicity patching,
**`deg(div f) = 0`**, and **degree-1 maps to `S²` are homeomorphisms**. Read: Forster §4, §17.9.
Strategy: get `deg(div f)=0` from the **argument-principle / degree** route (count zeros = count
poles = degree), *not* from a general manifold Stokes theorem. Degree-1 ⇒ injective ⇒ (compact,
proper) homeomorphism is the forward-headline finisher.
⚠ The general-Stokes route to `deg∘div=0` is a dead end; use the degree counting on a regular value.
**Builds on:** monodromy

### serre-duality-tails  (`TailDuality/`)
**Serre duality through Laurent tails (Miranda VI.3)**: the multiplication action on `H¹`-tails,
surjectivity, the order downgrade (Miranda Lemma 3.6), and **`h¹(D) = l(K−D)`**. Read: Miranda Ch. VI
§3. Strategy: pair tails against holomorphic forms; surjectivity of the pairing + a finrank count
gives `h¹(D)=l(K−D)`. This is the **make-or-break** unit.
⚠ Use Miranda's concrete tail duality, **not** Hodge symmetry `H^{0,1}≅\overline{H^{1,0}}`. The Hodge
route needs harmonic theory you should not build. This is *the* key routing decision of the project.
**Builds on:** laurent-tails, proper-map-degree, residue-theorem, serre-duality-cech

### cech-h1-genus  (`H1Genus/`)
**`dim H¹(X, 𝒪) = g`**: cup-product kill, monotonicity, effective-divisor vanishing comparison.
Read: Forster §17.4–17.5; Miranda Ch. X §2. Strategy: with `D=0`, tail duality gives
`h¹(0)=l(K)=g`. Anchors the numerical genus to the cohomological one.
**Builds on:** serre-duality-tails

### riemann-roch  (`RiemannRoch/`)
**Riemann–Roch**: `l(D) − l(K−D) = deg D + 1 − g`, with `deg K = 2g−2`, `l(K) = g`, and the
genus-0 **single-simple-pole** consequence. Read: Miranda Ch. VI; Forster §16. Strategy: combine the
tail-form RR (`l(D) − h¹(D) = deg D + 1 − g`) with tail Serre duality (`h¹(D)=l(K−D)`). The forward
headline only consumes the **inequality** `l(D) ≥ deg D + 1 − g` at a single point of genus 0.
**Builds on:** serre-duality-tails

### abel-theorem  (`Abel/`)
**Abel's theorem (Forster 20.7, dissection-free)**: the two-point Abel–Jacobi value is nonzero for
distinct points on `g ≥ 1`, hence `ofCurve` is **injective**. Read: Forster §20. Strategy: if
`AJ(P)=AJ(Q)` then there is a meromorphic function with divisor `P−Q`, i.e. a degree-1 map ⇒ `g=0`,
contradiction. Use Forster's dissection-free formulation (no fundamental-polygon machinery).
⚠ Avoid the cut-surface/dissection route; it forces a `∃ cutSurface` obligation that is hard and
unnecessary. Forster 20.7 routes around it.
**Builds on:** abel-weak-solutions, cech-h1-genus

### genus-zero-headline  (`GenusSphereHeadline/`)
The **headline** `genus X = 0 ↔ X ≃ₜ S²`, assembled from RR (forward: single simple pole ⇒ degree-1
map to `ℙ¹` ⇒ homeo) and sphere-topology (backward). Read: Forster §16.
⚠ The forward map's smoothness/`ContMDiff` is delicate: a germ-only `toFun` is not `ContMDiff`; you
must hand it a holomorphic representative (`holoRepr`), or the genus-0 ⇒ sphere direction stalls on a
junk-value gap.
**Builds on:** riemann-roch

### period-lattice-rank  (`PeriodLattice/`)
The period lattice has a **real basis of rank `2g`** (Forster 21.3–21.4, dissection-free):
discreteness via the local Jacobi map, nondegeneracy, and the real basis — completing the
`Jacobian = ℂ^g/Λ` torus. Read: Forster §21; G–H Ch. 2 for intuition. Strategy: discreteness from a
local injectivity (local Jacobi inverse) argument; full rank from nondegeneracy of the period matrix.
⚠ Cheapest formal path is the **Riemann cut-surface + Green's-theorem** flavor of period
nondegeneracy, **not** Hodge / de Rham. Again: stay off the Hodge route.
**Builds on:** abel-theorem

---

## The three routing decisions that make this feasible (the real "modulo" content)

1. **Serre duality via Laurent tails (Miranda VI.3), never Hodge symmetry.** The Hodge route demands
   harmonic theory / elliptic regularity. Miranda's tail pairing closes it with finite-dimensional
   linear algebra over the finiteness theorem.
2. **The residue theorem (`∑Res=0`) and the residue functional are different problems.** The theorem
   is Stokes-only; the Serre functional needs one honest integration atom. Every "Stokes-free Serre"
   shortcut is circular. Budget for the integration atom; don't chase the shortcut.
3. **Cohomology-first, PDE-light.** Finiteness of `H¹` (Schwartz + Montel) plus the *PDE-free*
   Dolbeault comparison replaces the entire harmonic-forms / Hodge apparatus. The only PDE you solve
   is ∂̄ on a disk (Forster 13.2). Everything global is a partition-of-unity reduction to planar
   Stokes and that one disk lemma.

One cross-cutting hazard, independent of the DAG: the genus definition, the `L(D)` model, and the
multiplicity normal form must all be junk-free representations. Those three choices are where a
clean-room attempt most easily goes silently wrong (a `toFun`-junk `L(D)` makes `l(D)≡0` and RR
false, etc.).
