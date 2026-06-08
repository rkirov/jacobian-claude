# Implementation plan — closing `exists_serreDualityData` (Serre duality, Forster §17)

**Target.** `Jacobians.Dolbeault.exists_serreDualityData`
(`Jacobians/Dolbeault/SerreDualityPairing.lean:129`):

```lean
theorem exists_serreDualityData (𝔘 : FiniteCover X) (hL : 𝔘.IsLeray) :
    Nonempty (SerreDualityData 𝔘) := sorry
```

This single `sorry` is the **last big wall of the Riemann–Roch wiring**. It bundles the geometric
instantiation of Forster §17 into one structure; discharging it makes `arithmeticGenus_eq_genus`,
`serre_h1_eq`, and (downstream) `riemannRoch_equality_of_ladder` / `exists_riemannRoch_divisor`
sorry-free, which feeds the forward headline `genus_eq_zero_iff_homeo`.

This is a **planning** document. It is written against a fresh read of Forster GTM 81 §16–17 (book
pp. 126–139, PDF pp. 132–145) and a verification pass over the repo (2026-06-08). It **supersedes**
`docs/serre_17_build_plan.md` and the EXECUTION-PLAN portion of `docs/hodge_bridge_research.md`; see
"What is now out of date" at the end.

Verification convention below: ✅ PROVEN = read off the source AND `lean_verify` reports axioms
`[propext, Classical.choice, Quot.sound]` this session (noted where checked); 🟡 partial /
scaffolded; 🔴 greenfield / sorry.

---

## 0. The structure to build, field by field

`SerreDualityData 𝔘` (`SerreDualityPairing.lean:72`) has six fields. The whole plan is "produce one
inhabitant of this structure for a general compact connected Riemann surface `X` with a Leray cover
`𝔘`." Downstream (`serre_eq`, `lDim_le_h1Dim`, `arithmeticGenus`, `serreH1`) is **already proven**
from the structure — nothing downstream needs touching.

| Field | Type | Forster | Repo status of the ingredient |
|---|---|---|---|
| `finH1` | `∀ D, FiniteDimensional ℂ (𝔘.cechH1 D)` | §14.9 + §16 | ✅ **PROVEN** `finiteDimensional_cechH1_general` (axiom-clean, verified). **FREE** — plug in directly. |
| `K` | `Divisor X` | 17.4 (`K = div ω₀`) | 🟡 needs a canonical divisor of a nonzero meromorphic 1-form `ω₀` (gate D). |
| `hKgenus` | `lDim K = genus X` | 17.4@D=0 + 17.12 | 🔴 needs the iso `𝒪_K ≅ Ω` ⇒ `lDim K = dim H⁰(Ω) = genus`. Hardest "definitional" node. |
| `ι` | `∀ D, lSysModule (K−D) →ₗ[ℂ] Dual ℂ (cechH1 D)` | 17.5 | 🔴 the residue pairing; needs global `Res` (gate A) + assembly. |
| `ι_inj` | `∀ D, Injective (ι D)` | 17.6 | 🟡 abstract core ✅ `finrank_le_of_injective_to_dual`; local witness ✅ `exists_formFnResidue_eq_one_of_localRep_ne_zero`; needs `ι` + the residue-1 → nonzero-functional wiring. |
| `ι_surj` | `∀ D, Surjective (ι D)` | 17.9 | 🟡 abstract core ✅ `serre_surjectivity_dim_core`; needs instantiation with `Λ n`, `I n = Im ι_{D−nP}`, and the three RR dim bounds (now reachable via `cohomological_riemannRoch`). |

**Key architectural note.** The structure phrases the pairing on the **junk-free linear-system
module** `lSysModule (K−D)` (= `H⁰(𝒪_{K−D})`, `SerreDualityPairing.lean:66`), NOT on a separate
meromorphic-1-form space. Via Forster 17.4 (`𝒪_{D+K} ≅ Ω_D`, mult by `ω₀`) this is legitimate and it
means **gate (C) of the old plan — "build the `Ω_D` space" — is NOT needed as a separate type.** This
is a real simplification baked into the already-committed structure. We work with meromorphic
*functions* (`MeromorphicFunction X`, already in the repo) throughout; the 1-form `ω₀` enters only as
a fixed multiplier turning `f ∈ L(K−D)` into the meromorphic 1-form `ω₀·f ∈ Ω_{−D}`.

---

## 1. The Forster §17 theorem chain → concrete Lean obligations

Verbatim structure of Forster §17 (corrected against the PDF). "Lean obligation" names are
*proposed* (new theorems to create) unless marked ✅/🟡 with an existing name.

| Forster | Statement (as in the book) | Proposed Lean obligation | Status |
|---|---|---|---|
| **17.1** | `Res : H¹(X,Ω) → ℂ` via `H¹(X,Ω) ≅ ℰ⁽²⁾/dℰ^{1,0}`, `Res(ξ)=(2πi)⁻¹∬_X ω`. | — (NOT used; needs `∬_X`/Stokes). | ⛔ avoided |
| **17.2** | Mittag–Leffler distribution `μ=(ωᵢ)` of merom. 1-forms, `δμ∈Z¹(Ω)`; `Res_a(μ):=Res_a(ωᵢ)`, `Res(μ):=∑_a Res_a(μ)` (finite on compact `X`). | `MittagLefflerForm` + `residueSum` + `MittagLefflerForm.res`. | ✅ **PROVEN** (`MittagLeffler.lean`): the structure, `res`, `res_add`/`res_smul`/`res_holomorphic`/`res_combine`, all linearity, axiom-clean. |
| **17.3** | `Res(μ) = Res([δμ])` (Forster proof = Stokes). | We need only **well-definedness of `Res` on classes**, i.e. `[δμ]=0 ⟹ Res(μ)=0`, i.e. a globally-holomorphic distribution (a global merom. 1-form `α`) has total residue 0. **= the 1-form residue theorem `∑Res α = 0` (GATE A).** | 🔴 see §4 |
| **17.4** | `ω₀·: 𝒪_{D+K} ≅ Ω_D` (`K = div ω₀`); **Lemma**: `dim H⁰(Ω_D) ≥ deg D + k₀` (`k₀ = 1−g+deg K`), from RR. | `serre_iso_17_4 : lSysModule (D+K) ≃ₗ[ℂ] (Ω_{-(-D)})` collapsed to working with `lSysModule (K−D)`; the dim lemma `lDim_omega_lower_bound : deg D + k₀ ≤ (lDim (D+K) : ℤ)`. Since we represent `H⁰(Ω_D)` AS `lSysModule (D+K)`, the iso is **by definition / `rfl`-adjacent**, and the lemma is `cohomological_riemannRoch` + `lDim_eq_zero_of_deg_neg`. | 🟡 lemma reachable now |
| **17.5** | pairing `⟨ω,ξ⟩ := Res(ω·ξ)`; `ι_D : H⁰(Ω_{−D}) → H¹(𝒪_D)*` linear. | `serreDualityPairing D : lSysModule (K−D) →ₗ[ℂ] Dual ℂ (cechH1 D)` = the field `ι`. Needs the **global `Res` functional on `cechH1` classes** + the product `ω₀f · ξ` producing a 1-form distribution. | 🔴 needs gate A |
| **17.6** | `ι_D` **injective** (EASY) — local witness: for `ω≠0` pick `a` with `D(a)=0`, write `ω=f dz`, take `η=((zf)⁻¹,0)`, then `ωη=(dz/z,0)` is an M–L distribution with `Res(ωη)=1`, so `⟨ω,[δη]⟩=1≠0`. | `serreDualityPairing_injective`. Plug into ✅ `finrank_le_of_injective_to_dual`. Local heart ✅ `exists_formFnResidue_eq_one_of_localRep_ne_zero` (verified axiom-clean). | 🟡 |
| **17.7** | naturality square `ι_{D'} ∘ (incl)* = (incl)* ∘ ι_D` for `D'≤D`; **Lemma**: if `i^{D}_{D'}(λ)=ι_{D'}(ω)` then `ω∈H⁰(Ω_{-D})` and `λ=ι_D(ω)`. | `serreDualityPairing_naturality` + `serreDualityPairing_restrict_lemma`. Bookkeeping over the restriction maps `cechH1 D → cechH1 D'`. | 🔴 (needed only for 17.9) |
| **17.8** | mult-by-ψ diagram; **Lemma**: `ψ ∈ H⁰(𝒪_B)\{0} ⟹ ψ: H¹(𝒪_D)* → H¹(𝒪_{D−B})*` injective. | `mulPsi_dual_injective`. Uses 16.8 epimorphism `H¹(𝒪_{D−B})↠H¹(𝒪_D)` (have ✅ via `SkyscraperLESBase`) + dual of epi = mono. | 🔴 (needed only for 17.9) |
| **17.9** | `ι_D` **surjective** (HARD): with `D_n=D−nP`, `dim Λ_n + dim Im ι_{D_n} > dim H¹(𝒪_{D_n})*` for large `n` forces `Λ_n ∩ Im ι_{D_n} ≠ 0`, giving the witness `ω₀=(1/ψ)ω ∈ H⁰(Ω_{−D})` with `λ=ι_D(ω₀)`. | `serreDualityPairing_surjective`. Plug into ✅ `serre_surjectivity_dim_core`. Needs: `Λ n`, `I n`, and `hΛ/hI/hV` from RR (now reachable). | 🟡 |
| **17.10/17.11** | `dim H¹(𝒪_D)=dim H⁰(Ω_{−D})`; at `D=0`: `g=h¹(0)=dim H⁰(Ω)`. | `serre_eq` ✅ **already proven** from the structure (`SerreDualityPairing.lean:93`). | ✅ downstream |
| **17.12** | `deg(ω₀) = 2g−2` (for `K=div ω₀`). | needed for `hKgenus` (`lDim K = genus`), see node K2. | 🔴 |

---

## 2. The dependency DAG for `exists_serreDualityData`

```
exists_serreDualityData 𝔘 hL                                                  [ASSEMBLY]
 │
 ├─ finH1 := finiteDimensional_cechH1_general            ✅ PROVEN (FREE)
 │
 ├─ ω₀ : a nonzero meromorphic 1-form on X               [GATE D]  🔴
 │    └─ exists_nonconstant_meromorphic_of_RR_ineq  ← cohomological_riemannRoch ✅
 │         (deg D ≥ g+1 ⟹ lDim D ≥ 2 ⟹ ∃ nonconstant f;  ω₀ := df)
 │
 ├─ K := div ω₀                                          [node K1]  🟡 (needs Divisor.of-1-form)
 │
 ├─ hKgenus : lDim K = genus X                           [node K2]  🔴
 │    ├─ serre_iso_17_4 : lSysModule K ≅ HolomorphicOneForms X   (ω₀· iso at D=0)
 │    └─ (alt) deg K = 2g−2 (17.12) + RR — but the iso route is cleaner; see §5 decision
 │
 ├─ ι := serreDualityPairing                             [node P]  🔴
 │    ├─ globalRes : cechH1 𝔘 Ω →ₗ[ℂ] ℂ  (the global residue functional)   [GATE A core]
 │    │    └─ residueSum descends to classes  ⟸  ∑Res α = 0   [GATE A]  🔴 (§4)
 │    ├─ pairingForm : lSysModule (K−D) → cechH1 D → MittagLefflerForm   (ω₀f·ξ)   🔴
 │    └─ bilinearity / well-defined-on-quotient wiring (uses res_add/res_smul ✅)
 │
 ├─ ι_inj := serreDualityPairing_injective               [node INJ]  🟡
 │    ├─ finrank_le_of_injective_to_dual                 ✅ PROVEN (for the ≤ corollary)
 │    ├─ exists_formFnResidue_eq_one_of_localRep_ne_zero ✅ PROVEN (residue-1 witness)
 │    ├─ exists_localRep_self_ne_zero                     ✅ PROVEN (nonzero coeff somewhere)
 │    └─ "residue-1 ⟹ ι(ω)≠0" + the M–L class [δη] construction               🔴
 │
 └─ ι_surj := serreDualityPairing_surjective             [node SURJ]  🟡
      ├─ serre_surjectivity_dim_core                     ✅ PROVEN (pigeonhole count)
      ├─ Λ n, I n  (the two subspaces)                                          🔴
      ├─ hΛ : dim Λ n ≥ 1−g+n   ⟸ 17.8 (Λ≅H⁰(𝒪_{nP})) + RR (cohomological_RR ✅)
      ├─ hI : dim Im ι_{D_n} ≥ n+k₀−d  ⟸ 17.4 + 17.6 (mulPsi_dual_injective)
      ├─ hV : dim H¹(𝒪_{D_n})* = n+g−1−d (n>d) ⟸ RR (cohomological_RR ✅)
      └─ 17.7 lemma (witness lands in H⁰(Ω_{−D}))                               🔴
```

### THE foundational gates everything reduces to

Re-verified against Forster and current repo state. The OLD plan listed (A) residue theorem, (B)
finiteness, (C) the `Ω_D` space, (D) ω₀-existence. **Corrected decomposition for 2026-06-08:**

- **(B) finiteness — ✅ DONE.** `finiteDimensional_cechH1_general` is proven axiom-clean. Removed
  from the gate list entirely.
- **(C) the `Ω_D` space — ELIMINATED.** The committed structure represents `H⁰(Ω_{−D})` as
  `lSysModule (K−D)` (meromorphic *functions*). No separate meromorphic-1-form type is built. Gate C
  is gone.
- **(D) ω₀-existence — NOW REACHABLE (small).** Falls out of the RR **inequality**
  `lDim D ≥ deg D + 1 − g` (a one-line corollary of the now-proven `cohomological_riemannRoch` once
  `h1Dim ≥ 0`). For `deg D ≥ g+1`, `lDim D ≥ 2`, giving a nonconstant meromorphic `f`; set `ω₀ = df`.
  This is the **only** new analytic-existence input and it is small. (Caveat: `df ≠ 0` because `f`
  nonconstant — needs a "nonconstant ⟹ `df` not identically 0" lemma, standard.)
- **(A) the 1-form residue theorem `∑Res α = 0` — THE remaining hard atom.** Makes `Res`
  well-defined on `cechH1` classes (17.3 well-definedness, NOT the Stokes value). Still the wall.
  Detailed in §4.

**So the genuine remaining foundational atoms are exactly TWO** (plus assembly):
1. **GATE A**: `∑_a Res_a α = 0` for a global meromorphic 1-form `α` on `X` (the *general*,
   higher-order-pole case). — *the hard atom.*
2. **GATE D**: a nonzero meromorphic 1-form `ω₀` exists. — *small, from the now-proven RR inequality.*

Plus the **assembly** (the pairing, the two injectivity/surjectivity instantiations, the `K`/`hKgenus`
nodes). The assembly is substantial but bottoms out in already-proven cores.

**There is no third hidden wall** — confirmed: Forster §16–17 are PDE-free (harmonic forms first
appear in §19, which §16–17 never invoke). No Hodge / Weyl / elliptic anywhere on this path.

---

## 3. Critical path + effort per node + maximal-reuse notes

Effort scale: trivial (<50 LoC) / small (50–200) / medium (200–500) / large (500–1500) / research.

**Critical path** (longest chain of 🔴 nodes), in build order:

| # | Node | Effort | Plugs into / reuses |
|---|---|---|---|
| 1 | `exists_nonconstant_meromorphic` (gate D) | small | `cohomological_riemannRoch` ✅, `lDim_eq_zero_of_deg_neg` ✅, `lDim_zero_eq_one` ✅ |
| 2 | `divOf1Form : HolomorphicOneForms/merom-1-form → Divisor X` + `K := div ω₀` (node K1) | small–medium | mirror `MeromorphicFunction.div` (`LinearSystem.lean`); `coeffAt`/`orderAtPoint` infra ✅ |
| 3 | **GATE A**: `∑Res α = 0` (general) | **research** | trace scaffold `MeromorphicTrace`/`TraceResidue` 🟡 (§4), W2 fibre apparatus |
| 4 | `globalRes : cechH1 𝔘 Ω →ₗ[ℂ] ℂ` (gate A core / descent) | medium | `residueSum`/`res_combine`/`res_holomorphic` ✅ + gate A for well-defined-on-quotient |
| 5 | `serreDualityPairing` (node P, the field `ι`) | medium–large | `MittagLefflerForm` ✅ for `ω₀f·ξ`; `Submodule.Quotient.lift`; `Module.Dual` |
| 6 | `serreDualityPairing_injective` (node INJ) | medium | ✅ witness + ✅ `finrank_le_of_injective_to_dual`; the `[δη]` class build 🔴 |
| 7 | `serre_iso_17_4` + `hKgenus` (node K2) | medium | `cohomological_riemannRoch` ✅, 17.12 `deg K = 2g−2`, or the direct `ω₀·` iso at D=0 |
| 8 | 17.7 + 17.8 lemmas (`naturality`, `mulPsi_dual_injective`) | medium | 16.8 epi ✅ (`SkyscraperLESBase`), dual-of-epi-is-mono (Mathlib) |
| 9 | `serreDualityPairing_surjective` (node SURJ) | medium | ✅ `serre_surjectivity_dim_core`; `Λ n`/`I n` build; `hΛ/hI/hV` from RR ✅ |
| 10 | `exists_serreDualityData` (final assembly) | small | bundles 1–9 |

**The critical path is 1 → 3 → 4 → 5 → {6,9} → 10.** Node 3 (GATE A) dominates; everything else is
assembly over proven cores. Nodes 7, 8, 2, K2 can proceed in parallel once gate A is in flight.

**Earliest sorry-free partial results** (build these first for momentum, they don't need gate A's
*class-level* `Res` if stated carefully):
- `exists_nonconstant_meromorphic` (node 1) — immediately, no gate A. Independently useful.
- The **EASY half of 17.6 at D=0** as a *conditional* `genus ≤ h1Dim 0` GIVEN a global `Res`:
  `genus_le_h1Dim_of_globalRes`. Wires ✅ witness + ✅ `finrank_le_of_injective_to_dual`. Becomes
  unconditional once node 4 lands. (This is the litmus the old plan stopped at — now finiteness is
  free, so only `Res` gates it.)

---

## 4. GATE (A) deep-dive — the 1-form residue theorem `∑_a Res_a α = 0`

This is the single hardest remaining atom and the make-or-break of the whole node. **The repo is much
further along here than the stale docs claim.** Two routes; the repo has firmly chosen the
**Miranda trace-to-ℙ¹ route** (NOT Forster's §17.3 Stokes, which needs `∬_X`).

### 4.1 What is ALREADY proven (verified this session)

The ℙ¹ side and the trace algebra are essentially complete (`Jacobians/TraceResidue.lean`,
`Jacobians/MeromorphicTrace.lean`):

- ✅ **ℙ¹ residue theorem** `LaurentForm.finiteResidueSum_add_resAtInfty_eq_zero`
  (`TraceResidue.lean:336`): `∑_{finite poles} Res + Res_∞ = 0` for a rational 1-form on ℂℙ¹, via the
  multi-pole Cauchy residue theorem `largeCircleIntegral_eq` + partial fractions. **The entire ℙ¹
  pillar is done.**
- ✅ **`resAt_finsum`** (`TraceResidue.lean:268`): residue of a finite sum = sum of residues.
- ✅ **Lemma 3.2 simple-pole** `FibreTrace.resAt_traceCoeff_of_simplePole` (`MeromorphicTrace.lean:382`)
  — *unconditional*. And the **general** `FibreTrace.resAt_traceCoeff` (`:363`) gated on one atom
  `ResidueChangeOfVariables`.
- ✅ **The combine** `finiteResidueSum_trace_eq_zero` (`:447`) and its fibre forms
  `finiteResidueSum_trace_eq_zero_of_fibres` (`:463`, general, gated on `ResidueChangeOfVariables`)
  and `..._of_simplePole_fibres` (`:483`, unconditional). These assemble
  `(∑_{centers} fibre-residue) + Res_∞(Tr α) = 0` from the ℙ¹ theorem + Lemma 3.2.

So the residue theorem on `X` is **structurally assembled**; what's missing is two precise inputs.

### 4.2 The TWO remaining inputs for gate A

**(A-i) `ResidueChangeOfVariables`** (`MeromorphicTrace.lean:297`), a *clean self-contained 1-variable
complex-analysis atom*:
```lean
def ResidueChangeOfVariables : Prop :=
  ∀ (s g : ℂ → ℂ) (b : ℂ), AnalyticAt ℂ s b → deriv s b ≠ 0 → MeromorphicAt g (s b) →
    resAt (fun w => g (s w) * deriv s w) b = resAt g (s b)
```
"Residue is invariant under an analytic change of variables." The **simple-pole instance is fully
proved** (`resAt_changeOfVariables_of_simplePole`, `:416`). The general case is a standard fact
(residue = `(2πi)⁻¹∮`, contour reparametrization), but Mathlib has no residue API, so it is a
genuine new ~**medium** atom. *Effort: medium (200–400 LoC), pure 1-var ℂ analysis, NO manifold.*
Routes: (a) Laurent-coefficient pushforward (the `c_{-1}` coefficient is change-of-variables
invariant for biholomorphic `s`); (b) contour-integral reparametrization
`∮_{s∘γ} g = ∮_γ (g∘s)·s'`. Mathlib has `circleIntegral`, Cauchy–Goursat, and
`meromorphicTrailingCoeffAt` — (b) via the repo's `resAt_eq_smul_circleIntegral` + a
change-of-variables-in-circleIntegral lemma is probably the most direct.

**(A-ii) The manifold trace assembly** — produce, from a global meromorphic 1-form `α` on `X` and a
branched cover `F : X → ℂℙ¹`, the data `(L : LaurentForm, fibre : ℂ → FibreTrace)` and the proof
`hL32` that "`L` IS the trace of `α`" (each center's fibre-residue sum = `resAt L.R p`, and `L.R` is
the trace coefficient). **This is the W2-intertwined part.** It needs:
  - `F = toRiemannSphere` of a chosen nonconstant meromorphic `f` (gate D gives `f`; the cover to ℙ¹
    is the repo's `ToSphereGeneral`/`ProjectiveLine` machinery).
  - the **fibre structure** over each base point: the finite preimage set, local biholomorphic
    sections (sheets), and the form coefficient on each sheet. **This is exactly the W2 fibre
    apparatus**: `ProperMapDegreeSheets`, `LocalMultiplicitySheets`, `fibres_finite`,
    `Discharge/Manifold/LocalSheetDataAtRegularValue`, `LocalNormalForm`.
  - that the only base points with poles/branching are finitely many (so the `Finset.image L.a` of
    centers is the right finite set) — reuses W2 `CriticalValuesFiniteGeneral`,
    `fibres_finite_statement_unconditional`.

### 4.3 How intertwined with W2

**Tightly, on input (A-ii); not at all on (A-i).** The fibre/sheet/branched-cover bookkeeping is
*the same apparatus* as `exists_properMapDegree` (`DegDivResidue.lean:265`, still 🔴). Two
consequences:
- Finishing W2 (`exists_properMapDegree`) hands gate A its fibre apparatus **and a worked template**:
  the `..._of_simplePole_fibres` combine is the `df/f` special case that `deg_div` uses, so the
  general assembly is "the same plumbing with general coefficients + (A-i) instead of the simple-pole
  shortcut."
- Conversely, gate A is **strictly more general** than `deg_div`: `deg_div` is the case
  `α = df/f` (residues = integer orders, simple poles only, so it dodges (A-i)). The
  `MittagLeffler.lean` docstring (lines 43–52) makes this correction explicit and correct: **gate A
  is NOT `deg_div`**; discharging `exists_properMapDegree` does not give gate A, but it de-risks the
  shared (A-ii) plumbing.

**Recommendation:** do (A-i) `ResidueChangeOfVariables` as an isolated 1-var atom *now* (it is the
clean, g-independent piece and unblocks the *general* fibre Lemma 3.2). Defer the full (A-ii)
assembly until the W2 fibre apparatus is consolidated, and build it as a generalization of the
`deg_div` assembly so the plumbing is shared.

---

## 5. Risks / uncertainties / decision points

1. **[DECISION — resolved by the committed structure] `Ω_D` as a meromorphic-1-form type vs.
   `𝒪_{K−D}` via `ω₀·`.** The structure already commits to **`lSysModule (K−D)`** (functions). Keep
   it. Do NOT build a `MeromorphicOneForm` type. The 1-form `ω₀` is only a fixed multiplier; the
   pairing's "form" `ω₀·f·ξ` is fed to `MittagLefflerForm` as `α = (a holomorphic 1-form), g = (f·ξ
   as a function)` — **but note** `ω₀` is *meromorphic*, while `MittagLefflerForm.α` is typed as
   `HolomorphicOneForms X`. **RISK:** the pairing integrand is `ω₀·f·ξ` with `ω₀` meromorphic, not
   holomorphic. **Resolution options:** (a) generalize `MittagLefflerForm.α` to a meromorphic 1-form
   coefficient (the residue calculus `resAt`/`coeffAt` only needs `MeromorphicAt`, so this is a
   typeclass-footprint widening, not new math); or (b) absorb `ω₀`'s poles/zeros into `g` and keep
   `α` a *fixed reference holomorphic form* (e.g. work chart-locally where `ω₀ = h·dz` and put `h`
   into `g`). **(a) is cleaner and likely necessary** — flag for the implementer; it touches
   `FormCoeff.coeffAt` (currently typed for `HolomorphicOneForms`). This is the single most likely
   place the current local infra needs widening.

2. **[DECISION] Does 17.9 need the full RR *equality* or just the *inequality*?** Forster 17.9 uses:
   `hΛ` (≥, from RR inequality + 17.8), `hI` (≥, from 17.4 inequality), and `hV` (**=**, the *exact*
   `dim H¹(𝒪_{D_n})* = n+g−1−deg D` for `n>deg D`). The `hV` equality is `cohomological_riemannRoch`
   rearranged (`h0Dim − h1Dim = deg + 1 − h1Dim 0`) **with `h0Dim(D_n)=0` for `deg D_n<0`** (via
   `lDim_eq_zero_of_deg_neg` + `h0Dim_eq_lDim` ✅). So `hV` IS reachable from the now-proven
   cohomological RR. **No circularity:** `cohomological_riemannRoch` does not depend on Serre. ✅ The
   abstract core `serre_surjectivity_dim_core` already takes `hV` as an `=` hypothesis, matching.

3. **[RISK — circularity check on `hKgenus`] `lDim K = genus`.** Two routes:
   (a) **direct iso** `serre_iso_17_4` at D=0: `lSysModule K ≅ HolomorphicOneForms X` (mult by `ω₀`
   maps `f ↦ ω₀·f`, a holomorphic 1-form iff `f ∈ L(K)`); then `lDim K = genus` by `finrank` of an
   iso. Clean, **no RR, no Serre** — *preferred*.
   (b) via 17.12 `deg K = 2g−2` + RR. **AVOID (b):** Forster derives 17.12 *from* Serre duality
   (`17.12` uses `Ω ≅ 𝒪_K` which is 17.4, fine, but its `deg` computation uses
   `dim H¹(X,Ω)=g−1` which is Serre@K) — **circular** if used to prove `hKgenus`. Route (a) is
   self-contained. Flag: ensure the implementer uses (a).

4. **[RISK] `globalRes` well-defined on `cechH1` classes (node 4).** A `cechH1` class is a coset in
   `cocycles1/coboundaries1` where cochains are **`Filter.Germ (codiscreteWithin)`** of functions
   (`CechSection.MGerm`). To define `Res` on a class one must: (i) lift a 1-cocycle germ-cochain to a
   genuine M–L distribution of 1-forms (the `ωᵢ` on overlaps) — i.e. realize the abstract germ
   cochain as honest local meromorphic forms with the right poles; (ii) show `residueSum` is
   independent of (a) the cocycle representative within the class [needs gate A on coboundaries] and
   (b) the germ representative [should be automatic — `resAt_congr` ✅ is germ-invariant]. **The germ
   → honest-form realization (i) is unglamorous but real plumbing.** It parallels the
   `cechRestrictL_surjective` realization (✅ done for H⁰, `CechH0.lean:545`) and should reuse its
   choice/realization pattern (`OmegaD` membership ⟹ honest representative). *Effort folded into
   nodes 4–5.*

5. **[UNCERTAINTY] Mathlib residue API gap.** Mathlib has **no** residue function (only
   `meromorphicTrailingCoeffAt` = leading Laurent coeff). The repo built `resAt` from scratch on
   `circleIntegral`. (A-i) `ResidueChangeOfVariables` therefore has no upstream lemma to cite; it is a
   genuine sub-build. *No other Mathlib gap forces a sub-build on this node* — the linear algebra
   (`Module.Dual`, `Subspace.dual_finrank_eq`, `finrank_sup_add_finrank_inf_eq`, `LinearEquiv`,
   `Submodule.Quotient.lift`/`mapQ`) is all present and is what the proven cores already use.

6. **[UNCERTAINTY] `IsLeray` is now a *single* simply-connected conjunct** (`CechComplex.lean:63`,
   `IsLeray 𝔘 := ∀ i, SimplyConnectedSpace (U i)`), and `GoodCover.lean` records that the proven
   comparison never consumes the overlap conjunct. The `hL : 𝔘.IsLeray` argument to
   `exists_serreDualityData` is needed only so `cechH1` computes the *true* `H¹` (so that 17.x's RR
   identities hold). **Verify** while building that the §17 dim counts only use `cechH1`'s computed
   `H¹` (they do — everything is phrased via `h1Dim`/`cechH1`), so `hL` threads through cleanly. Low
   risk.

7. **[RISK] `ω₀ = df` and "`df ≠ 0`".** Gate D produces a nonconstant meromorphic `f`; `ω₀ := df`.
   Need `df ≢ 0` (else `K` ill-defined / iso fails). Standard (nonconstant ⟹ `f'` not identically 0
   on a connected manifold), but needs a small lemma. The repo has `MeromorphicFunction`/`orderAtPoint`
   infra; check `Abel.lean`/`LineIntegral.lean` for an existing "`d` of nonconstant ≠ 0."

---

## 6. Honest scope, sequencing, no-axioms constraint

### Total LoC estimate
- Gate D + node K1 (ω₀, K): ~200–400 LoC. *Small.*
- Gate A — (A-i) `ResidueChangeOfVariables`: ~200–400 LoC. *Medium, isolated.*
- Gate A — (A-ii) manifold trace assembly: ~800–1500 LoC, **shared with / built on W2**. *Large.*
- `globalRes` descent (node 4): ~300–500 LoC. *Medium.*
- Pairing `ι` (node 5): ~300–600 LoC. *Medium–large.*
- Injectivity (node 6) + `[δη]` class: ~200–400 LoC. *Medium.*
- `hKgenus` / `serre_iso_17_4` (K2): ~200–400 LoC. *Medium.*
- 17.7 + 17.8 (nodes 8): ~200–400 LoC. *Medium.*
- Surjectivity instantiation (node 9): ~300–500 LoC. *Medium.*
- Final assembly (node 10): ~50–150 LoC. *Small.*

**Total: ~3–5k LoC**, dominated by gate A (A-ii) and the pairing/injectivity/surjectivity assembly.
This matches the old "~3–5k" estimate, but the *risk profile is much better*: finiteness and
cohomological RR are now proven, so the count flows from real lemmas, and the §17 cores
(injectivity/surjectivity/pigeonhole) and the ℙ¹/trace residue scaffold are already axiom-clean.

### Recommended sequencing (earliest sorry-free wins first)

1. **Node 1 (gate D)** `exists_nonconstant_meromorphic` — immediate, no gate A, independently useful.
   Sorry-free win.
2. **Node K1** `divOf1Form` / `K := div ω₀` — small, parallel.
3. **(A-i)** `ResidueChangeOfVariables` — isolated 1-var atom; unblocks the *general* fibre Lemma 3.2.
   Sorry-free win (a real theorem), and the cleanest hard piece.
4. **EASY-half conditional** `genus_le_h1Dim_of_globalRes` — wires the ✅ witness + ✅
   `finrank_le_of_injective_to_dual`; sorry-free *given* a `Res` functional. The first genuinely-Serre
   sorry-free statement.
5. **Node 4** `globalRes` descent — needs gate A on coboundaries. Once landed, step 4 becomes
   unconditional (`genus ≤ h1Dim 0` axiom-clean).
6. **Nodes 5, 6** pairing + injectivity (full `ι`, `ι_inj`).
7. **Nodes K2, 7, 8** `hKgenus`, naturality, mult-by-ψ.
8. **(A-ii)** full manifold trace assembly (the big W2-shared piece) — makes gate A unconditional.
9. **Node 9** surjectivity instantiation.
10. **Node 10** assemble `exists_serreDualityData` ⟹ `arithmeticGenus_eq_genus` / `serre_h1_eq`
    sorry-free ⟹ RR ladder ⟹ forward headline.

### No-axioms constraint
Every node must end `#print axioms` = `[propext, Classical.choice, Quot.sound]`. All ✅ cores already
satisfy this (verified: `finiteDimensional_cechH1_general`, `cohomological_riemannRoch`,
`serre_surjectivity_dim_core`, `exists_formFnResidue_eq_one_of_localRep_ne_zero`). Watch points: the
`Submodule.Quotient.lift` descent (node 4/5) and the `Filter.Germ` realization (risk #4) must not
introduce `sorryAx`; build one module at a time, `lean_verify` each leaf (note: `lean_verify`/LSP can
falsely report `sorryAx` when an imported file changed mid-session — trust `lake build` with no "uses
sorry" warning + `#print axioms`).

---

## What is now out of date (reconciliation)

`docs/serre_17_build_plan.md` and `docs/hodge_bridge_research.md` EXECUTION PLAN are **superseded** by
this doc. Specifically:

- **STALE: "(B) finiteness is open / `exists_cechModel` general needs STEP B ~1.5k LoC."**
  WRONG NOW — `finiteDimensional_cechH1_general` and `exists_cechModel_general` are PROVEN sorry-free
  and axiom-clean (`CechFinitenessDtwist.lean`). Finiteness is **free**.
- **STALE: "(C) build the `Ω_D` meromorphic-1-form space (definitional, unbuilt)."**
  ELIMINATED — the committed `SerreDualityData` represents `H⁰(Ω_{−D})` as `lSysModule (K−D)`
  (functions). No such type is needed.
- **STALE: `cohomological_riemannRoch` "proven mod skyscraper sorry" / `exists_skyscraperLES` a sorry.**
  WRONG NOW — `exists_skyscraperLES` is a **theorem** (`CohomologicalRR.lean:156`), and
  `cohomological_riemannRoch` is PROVEN axiom-clean (gated only on the `LocallyRealizable`
  hypothesis, not a sorry). The RR inequality and `hV`/`hΛ` dim counts are therefore reachable now.
- **STALE: gate A "df/f case fully assembled but general higher-order pole is the new atom."**
  PARTLY SUPERSEDED — the *general* fibre Lemma 3.2 `resAt_traceCoeff` and the general combine
  `finiteResidueSum_trace_eq_zero_of_fibres` ARE assembled (gated on `ResidueChangeOfVariables`), and
  the ℙ¹ residue theorem is fully proven. The remaining gate-A work is precisely (A-i)
  `ResidueChangeOfVariables` + (A-ii) the manifold trace assembly — see §4.
- **STALE: the `hodge_bridge_research.md` §0–§5 "EASY/HARD = conjugation + L² positivity, HARD =
  Weyl/elliptic wall, multi-month-to-year."** SUPERSEDED by that file's own 2026-06-03 CORRECTION and
  by this doc: the route is the PDE-free Forster §17 residue pairing; there is no Weyl/elliptic
  content. Keep only the CORRECTION section of that file as historically accurate; the §2/§4/§5 Hodge
  discussion is moot for this route.
- **STILL ACCURATE:** the §17.9 pigeonhole is pure finite-dim linear algebra (✅ cores proven); the
  residue route avoids manifold 2-form integration; `deg_div` ≠ gate A; no third hidden wall.

---

## Report summary (the asks)

- **Critical path:** node 1 (ω₀ existence, small) → **node 3 GATE A** (`∑Res α = 0`, research) →
  node 4 (`globalRes` descent, medium) → node 5 (pairing `ι`, medium–large) → nodes 6 & 9
  (injectivity & surjectivity instantiations over proven cores, medium each) → node 10 (assembly).
- **Genuine remaining foundational atoms (2):**
  (A) the general 1-form residue theorem `∑Res α = 0` — splits into the clean 1-var atom
  `ResidueChangeOfVariables` (medium, isolated) + the W2-intertwined manifold trace assembly (large);
  (D) ω₀-existence — now small, from the proven cohomological-RR inequality.
  (Finiteness and the `Ω_D` space, listed as gates in the old plan, are respectively DONE and
  ELIMINATED.)
- **Highest-risk item:** GATE A's (A-ii) manifold trace assembly — it is the largest greenfield piece
  and is tightly intertwined with the still-open W2 `exists_properMapDegree` fibre apparatus; build it
  as a generalization of the `deg_div` simple-pole assembly to share plumbing. (Runner-up risk:
  the `MittagLefflerForm.α` holomorphic-vs-meromorphic typing mismatch, risk #1 — likely needs
  widening `coeffAt`/`MittagLefflerForm` to a meromorphic 1-form coefficient.)
