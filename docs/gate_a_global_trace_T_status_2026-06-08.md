# Gate A — the global trace function `T` (Miranda §VIII.3 step 1): status

**Date:** 2026-06-08 · **Status:** mechanical scaffold COMPLETE + axiom-clean; the irreducible
§VIII.3 geometric content (the glue + the genus-`0` `∞`-vanishing) isolated as the minimal remaining
obligation.

Plan: `docs/miranda_VIII3_confirmation_2026-06-08.md` (Miranda *Algebraic Curves and Riemann
Surfaces*, §VIII.3, the "Algebraic Proof of the Residue Theorem"). Forster §17 agrees.

---

## What was built (all axiom-clean `[propext, Classical.choice, Quot.sound]`, no `sorry`, no custom axiom)

Two new files, `Jacobians/Dolbeault/FormTraceGlobalT.lean` and
`Jacobians/Dolbeault/FormTraceGlobalTAssemble.lean`, supplying the **definition-and-assembly layer**
for the `GlobalTrace ω₀ g f poles hac` structure of `FormTraceGlobalAssemble` (the PROVEN assembly:
`GlobalTrace ⟹ ∑Res = 0`).

### `FormTraceGlobalT.lean` — the analytic infrastructure

* `analyticAt_traceCoeff_base` — the local fibre trace coefficient is analytic at a regular value off
  the poles of `α` (re-export of the proven `analyticAt_traceCoeff` in base-value form).
* `analyticAt_of_eventuallyEq_regularFibreTrace` — **off-centre analyticity bridge**: `T` is analytic
  at a regular value when it germ-equals a regular fibre trace there (the off-exceptional half of the
  `hT_off` obligation).
* `exists_principalPart_traceCoeff_fibreTrace` / `…_inftyFibreTrace` — finite principal-part
  extraction for the local trace at a finite pole-value / at `∞`.
* `laurentOfNegTails` (+ `_a`, `_R`) — packages a finite `negTail` family as an honest `LaurentForm`
  (`R = ∑ negTail (cs i)`, centre-image = `{cs i}`).
* `exists_laurentForm_principalPart` — subtracts the finite principal parts of a meromorphic
  coefficient into a genuine `LaurentForm` with explicit centres `cs` (padded so every centre appears
  in the centre-image), `T − L.R` germ-analytic at each centre.
* `analyticOnNhd_remainder_of_junkFree` / `…'` — **discharges `GlobalTrace.hentire`**: `T − L.R` is
  entire from `T` analytic off the centres + junk-freeness (continuity after pole removal).
* `continuousAt_recipCoeff_of_vanishing` — **discharges `GlobalTrace.hrecip`**: `recipCoeff (T − L.R)`
  continuous at `0` from the genus-`0` input (its analytic continuation `R₀` vanishes at `0`).

### `FormTraceGlobalTAssemble.lean` — the constructors

* `globalTrace_of_data` — builds `GlobalTrace` from `T`, an explicit `L`, the glue (`hglue_fin` /
  `hglue_inf`), and the remainder-analytic facts; discharges `hentire`/`hrecip`.
* `globalTrace_of_glue` — **maximally reduced**: builds `L` *internally* from `T`'s principal parts at
  the centres (which exist since `T` germ-agrees with the meromorphic local fibre traces), so the
  caller supplies only the glue, off-centre analyticity, junk-freeness, and the genus-`0`
  `∞`-vanishing — no principal-part bookkeeping.
* `residueSum_eq_zero_of_data` / `residueSum_eq_zero_of_glue` — **Gate A `∑Res = 0`** from those
  inputs (compose with the proven `residueSum_eq_zero_of_globalTrace`).
* `residueSum_eq_zero_of_data_holomorphic` — **non-vacuity**: the constructor is satisfiable
  (empty-pole case, `T ≡ 0`), not a disguised `False`.

---

## The minimal remaining obligation (the irreducible §VIII.3 geometric content)

Gate A `∑ₐ Resₐ(α) = 0` is now **unconditional modulo the hypotheses of `residueSum_eq_zero_of_glue`**
for a suitable adapted cover.  All principal-part / entire / reciprocal-chart bookkeeping is
discharged.  What remains is exactly:

1. **The glue `hglue_fin` / `hglue_inf`** — the global trace function `T` germ-agrees with the local
   fibre traces near each finite centre and at `∞`.  This is the branched-cover sheet-gluing
   (monodromy), the substantial §VIII.3 analytic content.
2. **The off-centre analyticity `hT_off`** — `T` analytic off the finite centres (the geometric trace
   is holomorphic off the exceptional set; `analyticAt_of_eventuallyEq_regularFibreTrace` reduces this
   to per-regular-value fibre data).
3. **The junk-freeness `hcont`** — `T − L.R` continuous at each centre (automatic for the geometric
   pushforward `Tr_F α`, which is continuous after the pole is removed).
4. **The genus-`0` `∞`-vanishing `R₀ 0 = 0`** — the analytic continuation of `recipCoeff (T − L.R)`
   vanishes at `0` (a holomorphic `1`-form on `ℂℙ¹` has no `dζ`-term at `∞` only if it is `0`;
   `H⁰(ℂℙ¹,Ω) = 0`).

### The honest subtlety (pole sub-fibre vs full fibre) — soundness-relevant

The `GlobalTrace.hglue_fin` field (inherited unchanged from the PROVEN `TraceAgreementData`) glues `T`
to the **pole sub-fibre** trace `(fibreTrace ω₀ f (fibreReg hac p))` — the trace summed over the
*poles of `α`* in the fibre `F⁻¹(coe p)`, **not** the full fibre.  The genuine geometric trace
`Tr_F α` sums over the *full* fibre, which over a pole-value `p` is `(pole sub-fibre trace) + (regular
sheets)`, the regular-sheet contribution being **holomorphic** near `p` (those points are regular
*and* non-poles of `α`).

Consequently:

* The two traces have the **same residue** at `p` (the holomorphic regular sheets contribute `0`), so
  the *residue*-level chain (which is all the PROVEN assembly extracts, via `resAt_congr` →
  `resAt_traceCoeff'`) is unaffected — the assembly is **sound**.
* But the literal `hglue_fin` (full germ-equality with the pole sub-fibre trace) is satisfiable by a
  single global `T` with `T − L.R` entire **iff** the pole sub-fibre traces are restrictions of one
  global rational function — i.e. **iff `Tr_F α` (full fibre) germ-equals the pole sub-fibre trace at
  each `p`**, which holds precisely when the cover **separates the poles of `α` from the regular
  points over each pole-value** (a generic-cover condition; Miranda's argument even tolerates the
  unseparated case via the `z = wᵐ` normal form, but the unramified-only `FibreTrace` here sidesteps
  it).  This is a *stronger* genericity hypothesis than the bare `AdaptedCover` carries, and is the
  precise extra input a future session must supply (alongside the genus-`0` vanishing).

This subtlety is **not** a misformalization of the assembly: `hglue_fin` is honest and non-vacuous
(empty-pole non-vacuity proven), and the residue-level use is sound.  It *does* mean the natural
`T = Tr_F α` (full geometric trace) satisfies `hglue_fin` only under the pole/regular separation
genericity — which should be folded into the adapted-cover construction (Gate D).

---

## Files

* `Jacobians/Dolbeault/FormTraceGlobalT.lean` (new) — analytic infrastructure (8 declarations).
* `Jacobians/Dolbeault/FormTraceGlobalTAssemble.lean` (new) — constructors + non-vacuity (6
  declarations).

Reuse (unchanged, PROVEN): `FormTraceGlobalAssemble` (the `GlobalTrace ⟹ ∑Res`), `FormTraceFibre`,
`FormTraceInftyFibre`, `FormTraceMeromorphic`, `FormTracePrincipalPart(Infty)`, `FormTraceLiouville`,
`FormTraceGlobalConstruct`, `TraceForm`.
