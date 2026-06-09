# Gate A residual #5 — genus-`0` `∞`-vanishing DISCHARGED (non-circular, Cauchy at `∞`) — 2026-06-09

**Status:** The genus-`0` `∞`-vanishing field-group `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq` (residual #5 of the
Gate A `DirectTraceGeometry` assembly) is **discharged for the general nonempty-pole trace**,
axiom-clean `[propext, Classical.choice, Quot.sound]`, *without circularity*.  Two new files:
`Jacobians/Dolbeault/SerreResidueDirectGenus0.lean` and `…Genus0Assemble.lean`.

## The circularity finding (`R₀ 0 = 0` was the residue theorem in disguise)

With the **finite-only** principal-part `LaurentForm L` (from `exists_laurentForm_principalPart`, all
exponents `< 0`, centres the finite pole-values `cs`), the field `hR₀0 : R₀ 0 = 0` is — via
`continuousAt_recipCoeff_of_vanishing` — equivalent to

> `ContinuousAt (recipCoeff (T − L.R)) 0`  with the value `0`  (i.e. `T − L.R = o(z⁻²)` at `∞`),

where `T := valueChartTracePatched ω₀ f Φ br`.  Now `recipCoeff L.R` has a **simple pole** at `0` whose
residue is `resAtInfty L.R` (`resAtInfty_eq_resAt_recipCoeff`), and `recipCoeff T` has a simple pole at
`0` whose residue is `∑_{F a = ∞} formFnResidue` (the `∞`-fibre Lemma 3.2, via `hcoh_full`).  So
**continuity of `recipCoeff (T − L.R)` at `0` forces those simple-pole residues to cancel** — which is
exactly the `∞`-residue identity `infty_eq`, and `infty_eq` + the finite Lemma 3.2 + the `ℂℙ¹` residue
theorem **is** Gate A `∑Res = 0`.  Hence discharging `R₀ 0 = 0` for a *nonempty* trace through the
global `T = L.R` route is **circular** with the theorem.

This is the same fact the repo records at `FormTraceGlobalConstruct.lean:51-60` (the "`infty_eq`
circularity": fabricating `L` from fibre residues makes `infty_eq` demand `∑Res = 0`).

## The non-circular fix (the `∞`-residue, not the full vanishing)

The §VIII.3 close does **not** need the full vanishing `R₀ 0 = 0`.  It needs only the **residue** of
`recipCoeff (T − L.R)` at `0` to vanish:

> `resAt (recipCoeff (T − L.R)) 0 = 0`.

This is **strictly weaker** (the `ζ⁻¹`-coefficient, not the value at `0`) and is **non-circular**: it is
*Cauchy's theorem at infinity* — the residue at infinity of an **entire** `1`-form coefficient vanishes.
The proof (`resAt_recipCoeff_eq_zero_of_entire`): for entire `h`, take a global primitive `H`
(`Differentiable.isExactOn_univ`); then on any circle `C(0, r)`,

> `recipCoeff h (ζ) = −h(ζ⁻¹)·ζ⁻² = d/dζ [H(ζ⁻¹)]`,

so `∮_{C(0,r)} recipCoeff h` is the integral of a derivative around a closed loop avoiding `0`, hence
`0` (`circleIntegral.integral_eq_zero_of_hasDerivWithinAt`); thus the residue is `0`.

The entire-ness of `T − L.R` is the **finite** junk-freeness `hcont_int` (genuinely about the finite
centres, *not* `∞`) — already an input — through `analyticOnNhd_remainder_of_junkFree'`.

## What is proved (axiom-clean)

In `SerreResidueDirectGenus0.lean` (namespace `Jacobians.Dolbeault.SerreResidueTheorem`):

- `resAt_recipCoeff_eq_zero_of_entire` — **Cauchy at `∞`** (the non-circular replacement of `R₀ 0 = 0`).
- `holoPunctured_recipCoeff_entire` / `meromorphicAt_recipCoeff_laurent` — `HoloPunctured`/meromorphy
  inputs of `resAt` additivity at `0`.
- `resAt_eq_laurentR_of_principalPart` — the **finite residue match** `resAt T (cs i) = resAt L.R (cs i)`,
  *free* from `exists_laurentForm_principalPart`'s punctured-analytic remainder (no `R₀`, no `T = L.R`).
- `infty_eq_of_remainderResZero` — the **`∞`-residue identity** `resAtInfty L.R L.ρ = ∑_{F a = ∞}
  formFnResidue` from `resAt (recipCoeff (T − L.R)) 0 = 0` (Cauchy) + `hcoh_full` (#6).
- `globalTraceData_of_genus0` / `residueTheorem_of_directGeometry_genus0` (+ non-vacuity witness
  `…_holomorphic`) — Gate A `∑Res = 0` from the residue-level geometry **without** the
  `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq` field-group.

In `SerreResidueDirectGenus0Assemble.lean`:

- `residueTheorem_ofAdapted_genus0` / `…SimpleInfty_genus0` / `…ofCanonicalSimpleInfty_genus0` — the
  adapted-cover / canonical-selection capstones (reusing the proven `poleSubfibre`/`poleSubEnum` /
  finite-pole-value / simple-`∞`-fibre / canonical-`Φ` combinatorics), R₀-group dropped.

## Net effect on the Gate A residual map

The genus-`0` `∞`-vanishing `R₀`/`hR₀_an`/`hR₀0`/`hR₀_eq` is **eliminated**.  Residual group #6 is now
just `hcont_int` (the **finite** junk-freeness, non-circular) + `hcoh_full` (#7, the `∞`-coherence).

Because the `DirectTraceGeometry` **structure** still carries the `R₀`/`hR₀_*` fields, the
residual-#5-free constructors return the residue theorem `∑Res = 0` directly rather than the structure
(the honest "drops these from the hypothesis list" form).

The remaining `hcont_int` is genuine and not free: at a pole-centre `cs i`, `T − L.R` has a removable
singularity (punctured limit exists, `exists_laurentForm_principalPart`), and `hcont_int` is the claim
that the trace's *literal value* there equals that removable limit.  This is the finite junk-freeness;
it is non-circular (purely finite-chart continuity) but a genuine property of `valueChartTracePatched`.

## References

- Miranda, *Algebraic Curves and Riemann Surfaces* (1995), §VIII.3.
- `Jacobians/Dolbeault/FormTraceGlobalConstruct.lean` (the "`infty_eq` circularity" note).
- `Mathlib.Analysis.Complex.HasPrimitives` (`Differentiable.isExactOn_univ`).
- `docs/gate_a_sound_patched_close_2026-06-09.md` (the sound branch-patched close).
