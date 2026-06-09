# Closing Riemann–Roch: route decision and plan (2026-06-09)

Research pass: re-read Forster §17 and Miranda Ch. VI from the repo PDFs, recon of
tangentstorm/JacobianChallenge and mrdouglasny/jacobian-challenge, and a name-by-name audit of the
repo assets each route would consume. **No code changed in this pass.**

## Where RR stands

`exists_riemannRoch_divisor` (`Jacobians/RiemannRoch.lean`) is gated on **exactly one** sorry:
`exists_serreDualityData` (`SerreDualityPairing.lean`) — verified by axiom check this session.
Everything else under it is proven and axiom-clean: finiteness (`exists_cechModel`), the skyscraper
LES + χ-machinery (`cohomological_riemannRoch`, hypothesis-form), `h0Dim_eq_lDim`,
`exists_realizableLerayCover`, the degree theorem (`deg_div`), and — as of today — the
**unconditional 1-form residue theorem** `∑Res(ω₀·g) = 0` (`residueTheorem_unconditional`,
ω₀ holomorphic, g meromorphic) wired into representative-independence
(`MittagLefflerForm.res_eq_of_globalMeromorphic_diff`).

The statement of `exists_riemannRoch_divisor` mentions only `lDim`, `deg`, `genus`
(= `finrank ℂ (HolomorphicOneForms X)`). **No cohomology appears in the statement** — the Čech
tower is internal scaffolding, so any sound proof of the statement closes the wall.

## The three candidate routes

### Route S (status quo): build `exists_serreDualityData` directly (Forster §17 on Čech H¹)

What §17 actually needs (from the re-read, Forster pp. 132–139):

* `Res : H¹(X,Ω) → ℂ` is **defined by integration** (17.1): via the soft resolution
  `0 → Ω → ℰ^{1,0} →d→ ℰ^(2) → 0`, a class is represented by a smooth 2-form τ and
  `Res(ξ) := (1/2πi)∬_X τ`. Well-definedness = Forster **(10.20)** (`∬_X dσ = 0`, X compact).
  The Mittag–Leffler/`∑res` picture enters only through the compatibility theorem **17.3**
  (`Res([δμ]) = ∑res(μ)`), whose proof is a bump-function computation using (10.20) twice and the
  local integral-residue identity **(10.21)**.
* Crucially, **no Cousin solve / no "every class is Mittag–Leffler-realizable" is ever needed**:
  the smooth split always exists (partition of unity, soft sheaf), and the 17.6 witness is an ML
  distribution *by construction*. The previously-feared realization wall (`H¹(ℳ)=0`, circular per
  the 2026-06-09 books verdict) is simply not on Forster's path.
* 17.9 surjectivity = the pigeonhole already proven abstractly
  (`SerreDuality.serre_surjectivity_dim_core`, axiom-clean) + dimension estimates 17.4/17.8 that are
  RR-χ bookkeeping over the proven skyscraper machinery.

Cost: the integration atoms (below) **plus** a chart-data 2-form structure, the Ω-cocycle smooth-split
realization, the 17.3 bump computation on cocycles, and the 17.4–17.9 instantiation. ≈ 3–5k LoC.
Keeps the Čech ladder as the consumer. This is the most faithful-to-current-architecture route but
strictly the largest.

### Route M (recommended): Miranda Ch. VI — adelic / Laurent-tail RR + Serre duality

Miranda proves RR **and Serre duality with no cohomology and no integration** (Ch. VI, pp. 169–193),
given (a) a uniform bound `deg A − dim L(A) ≤ M`, and (b) the residue theorem `∑Res(fω) = 0` for
meromorphic 1-forms ω. The objects:

* **Laurent tail divisors** `𝒯[D](X)`: finitely many points, at each a Laurent *polynomial* tail in
  the (canonically pinned) coordinate, all terms of degree < −D(p). Truncations `t^{D₁}_{D₂}`,
  multiplication isos `μ_f : 𝒯[D] ≅ 𝒯[D − div f]`, truncation-of-Laurent-series map
  `α_D : ℳ(X) → 𝒯[D](X)` with `L(D) = ker α_D`.
* **`H¹(D) := coker(α_D)`** — the Mittag–Leffler obstruction space. Lemma 2.3: for `D₁ ≤ D₂`,
  `dim H¹(D₁/D₂) = [deg D₂ − dim L(D₂)] − [deg D₁ − dim L(D₁)]` (pure monomial counting).
* **Finite-dimensionality** (2.5–2.7): from the M-bound, pick `A₀` maximizing `deg − dim L`; then
  `H¹(A₀) = 0` and everything else is finite by Lemma 2.3. **RR-I**: `dim L(D) − dim H¹(D) =
  deg D + 1 − dim H¹(0)` (bookkeeping).
* **Residue map** (p. 186–187): for ω with `div ω ≥ D`,
  `Res_ω(∑ r_p·p) := ∑_p Res_p(r_p ω)` — a *finite sum of local residues of (tail polynomial ×
  meromorphic germ)*, i.e. **Laurent-coefficient algebra, zero integration**. It descends to
  `H¹(D) → ℂ` **exactly because `∑Res(fω) = 0`** — the theorem we proved today (for the
  ω₀-factorable case).
* **Serre duality** (Thm 3.3, pp. 188–191): `Res : L^(1)(−D) → H¹(D)*` iso. Injectivity = an
  explicit `z^{−1−k}` tail witness (≅ our proven `dz/z` witness style). Surjectivity = Lemma 3.4
  (pull any functional back along `μ_f` far enough — a growth-rate pigeonhole identical in shape to
  our proven dim core) + Lemma 3.6 (order bookkeeping).
* **Three genera + RR-II** (pp. 191–192): `dim H¹(0) = dim L(K) = dim Ω(X)` and
  `deg K = 2g−2` **come out** of duality + RR-I (our `deg_canonical`/`lDim_canonical_eq_genus` are
  already proven in exactly this conditional form). RR-II is verbatim `exists_riemannRoch_divisor`.

**The two inputs, in repo terms:**

1. **M-bound.** Miranda gets it from algebraicity (his Lemmas 1.18/1.20/1.21/2.4–2.5 — the only
   place Ch. VI uses the "algebraic curve" hypothesis). **We replace all of it** with the proven
   `riemannRoch_inequality` (`SerreOmega0.lean`, axiom-clean, `hR` supplied by the proven
   `exists_realizableLerayCover`): `deg A − lDim A ≤ h¹_Čech(0) − 1 =: M`, uniformly. *This is where
   the Čech-tower investment pays — it is the bridge between the towers, and it is already proven.*
2. **`∑Res(fω) = 0` for ω meromorphic.** Our `residueTheorem_unconditional` takes ω₀ *holomorphic*.
   Split by genus:
   * **genus ≥ 1**: pick `0 ≠ ω₀ ∈ Ω(X)` (exists by `genus` = finrank Ω ≥ 1). Any meromorphic ω
     in pair representation has `ω = h·ω₀` with `h` a meromorphic function (chart-wise quotient of
     coefficients; `MeromorphicAt.div` + identity theorem). Then `∑Res(f·ω) =
     ∑Res((f·h)·ω₀) = 0` **by the proven theorem as-is**. ~200–400 LoC of reduction, no surgery on
     the 28k-LoC Gate-A chain (whose `HolomorphicOneForms` typing is pervasive — direct
     generalization rejected).
   * **genus 0**: no ω₀ exists; needs the integration atoms (Phase 6) *or* lives without RR until
     they land. Note the genus-0 case is exactly the forward-headline consumer
     (`genus_eq_zero_iff_homeo` forward), so it is needed eventually; Abel (#3) only needs
     genus > 0.

**Form spaces without a new sheaf type:** represent `L^(1)(−D)` as `L(K−D)` for
`K := div(dg₀)` (`g₀` any nonconstant meromorphic function — `exists_nonconstant_meromorphic`,
proven), where `div(dg₀)` is defined chart-wise by `ord(g₀′)` (chart-invariant via
`transition_deriv_ne_zero`, proven). This is the already-validated "gate C elimination" device; no
meromorphic-1-form bundle is built. All residues are computed on pair data
`(tail r_p) · (coefficient germ)` via the existing `resAt` / principal-part APIs
(`FormTracePrincipalPart.exists_principalPart_meromorphicAt`, proven).

Cost: ≈ 2.5–4k LoC, of which ~80% is finsupp/finite-dimension/order bookkeeping (fast-elaborating,
low-risk, Mathlib-style) and the rest the factorization reduction. **Strictly dominates Route S for
closing RR**: no 2-form cochain plumbing, no Ω-cocycle realization, no 17.3 bump computation, no
Čech-Ω anything.

### Route H (the integration atoms — genus-0 completer and #7 infrastructure)

The minimal unavoidable integration content (per both books, confirming the 2026-06-09 verdict),
all Mathlib-scaffolded, **no manifold Stokes, no triangulation, no 2-form bundle**:

1. **Planar compact-support Stokes** (Forster 10.20 engine): `∫_ℂ ∂̄(φ) = 0` (and the dx/dy forms)
   for smooth compactly-supported φ — Fubini + interval FTC. ~150–300 LoC. Seed available:
   tangentstorm's MIT, sorry-free rectangle Green's theorem (`stokes_local_euclidean`, see recon).
2. **Local integral-residue identity** (10.21): radial bump χ at a pole,
   `∬ d(χ·ω) = −2πi·res(ω)` — `polarCoord` Fubini + `circleIntegral` of `zpow` (Mathlib) +
   finite principal part (repo, proven) + Cauchy–Goursat for the analytic remainder (Mathlib).
   ~400–700 LoC.
3. **Classical Stokes proof of `∑Res(η) = 0` for an arbitrary meromorphic pair-form η** (uniform in
   genus): PoU off the poles + (1) + (2). ~300–600 LoC. Supersedes the genus-split of Route M's
   input 2 and cross-checks Gate A.

These atoms are also the entry ticket for wall #7's Riemann bilinear relations (independently
confirmed: mrdouglasny axiomatize exactly this as `AX_RBR1/RBR2` "to avoid 2-form integration") —
permanent infrastructure, not a detour.

## Recon verdicts (external repos)

* **mrdouglasny/jacobian-challenge** (re-recon at HEAD `894e192`, ~685 new commits since 2026-06-08):
  RR + Serre are now *theorem wrappers over 7 new opaque axioms* (`Layer3/Cohomology.lean`: opaque
  `H1coh` + finiteness + skyscraper-LES + `h¹(0) = g` + `serreDuality_equiv`) — the trust boundary
  moved, no analytic content added. **Their axiom list is exactly our proven-vs-open frontier, and we
  are ahead on every node** (their finiteness/LES axioms = our proven theorems; their two duality
  axioms = our one sorry; their `AX_RBR1/2` = our Route-H atoms). Zero residue/integration/∂̄/Čech
  content (grep-verified); they consume *our* vendored Montel code for Ω-finiteness. A dormant
  honest adelic `H¹` (Weil repartitions, 3 sorries) confirms the Route-M shape independently.
  Genuinely proven and worth noting as a reference (not a port): an elementary Montel-free
  `ℓ(D) ≤ 1 + deg D⁺` finiteness (`Cohomology/RiemannRochFinite.lean`).
* **tangentstorm/JacobianChallenge** (HEAD `e94a1a2`, MIT, ~81.6k LoC, targets v0.3): **states no
  Riemann–Roch and no Serre duality at all** — their `RiemannRoch.lean` proves vacuous existentials
  (`∃ a b, a − b = 2` by `⟨2,0⟩`), the 2-form/Stokes umbrella is a literal `:= 0` stub, the period
  pairing is a documented zero placeholder, and "genus 0 ⇒ simple pole" is derived from a sorried
  uniformization (the theorem itself). Two independent validations of our design: they
  found-and-removed the same unsound pointwise `Module ℂ` instance on meromorphic functions that our
  germ-quotient fixed, and they hit the same Hodge/Weyl wall our route avoids (2 sorried PDE
  leaves). **Two portable, MIT, inspection-verified sorry-free nuggets:** (i) Green's theorem on an
  axis-aligned rectangle (`stokes_local_euclidean`, ~250 LoC self-contained, Mathlib-only FTC/Fubini)
  — a direct seed for Route H atoms 1–2; (ii) the multi-chart path-integral refinement-invariance
  design (`pathIntegralViaCoverWith_refinement_invariant'`) — #7 period-integral prior art.

## Decision and phase plan

**Adopt Route M as the RR-closing path, with Route H as the genus-0 completer (and #7 bank).**
Route S is kept as documented fallback; nothing built for M/H is wasted if S is ever revived (S
consumes H's atoms wholesale).

| Phase | Content | Size | Risk |
|---|---|---|---|
| M1 | `𝒯[D]` tail algebra: finsupp-of-tails, truncations `t`, `μ_f`, `α_D` (via principal parts), `L(D) = ker α_D ↔ lSysModule`, the SES | ~800–1200 | LOW (pure algebra; design care: per-point support constraint, canonical-chart pinning) |
| M2 | Lemma 2.3 dimension counts; M-bound from `riemannRoch_inequality`; finite-dimensionality (2.6/2.7); **RR-I** | ~400–700 | LOW |
| M3 | Residue map on tails (`resAt` of tail×germ products); `∑Res_p(fω) = Res_ω(α_D f)` (order arithmetic); descent to `H¹(D)` via the genus≥1 factorization of `∑Res = 0`; `K := div(dg₀)` | ~600–1000 | LOW-MED |
| M4 | Duality: injectivity witness; `Res∘μ_f = Res_{fω}`; Lemma 3.4 pigeonhole; Lemma 3.6; surjectivity assembly | ~800–1400 | MED (longest proofs; shapes all match proven repo patterns) |
| M5 | Three genera, RR-II, **re-point `exists_riemannRoch_divisor`**; deprecate/prune the bypassed `exists_serreDualityData` subtree per repo convention (the Čech tower *below* it stays — `riemannRoch_inequality` is load-bearing) | ~300–500 | LOW |
| H1–H3 | Integration atoms + uniform `∑Res = 0` → genus-0 RR; banks #7 infrastructure | ~1200–2000 | MED (new analysis domain, every Mathlib dependency identified) |

Sequencing: M1→M2→(M3∥M4)→M5 gives **RR for genus ≥ 1** (unblocks Abel #3, which assumes
`0 < genus`); H1–H3 then closes genus 0 (the forward headline's case). Estimated 3–4 focused
sessions for M, 2–3 for H.

**Soundness guards** (per repo discipline): every structure gets a non-vacuity witness; the
residue-descent genuinely consumes `∑Res = 0` (no junk functionals — the `z^{−1−k}` witness forces
nondegeneracy); `lake build` + `#print axioms` per commit; statements cross-checked against the book
pages cited above (Miranda pp. 178–192; Forster pp. 132–139).

## What this changes about the standing architecture

* `exists_serreDualityData` stops being the RR gate; the §17 Čech-pairing program
  (`SerreResiduePairing` / `GlobalResidueConstruct` / cup product / `SerreDualityPairing` ladder
  leaves) becomes banked material — prune the sorry-carrying leaves once M5 re-points, per the
  dead-code convention.
* The Čech cohomology tower below (finiteness, skyscraper LES, `h0Dim_eq_lDim`, comparison,
  `riemannRoch_inequality`) remains live and load-bearing.
* Gate A's `residueTheorem_unconditional` becomes the duality engine (genus ≥ 1) — today's
  unconditional close was the prerequisite for this whole plan.
