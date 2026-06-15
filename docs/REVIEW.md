# Reviewer's guide

This repository claims a complete, sorry-free solution of Kevin Buzzard's Jacobians challenge.
Every proof is checked by Lean's kernel, so **proof correctness is not the thing to review** —
what needs human eyes is whether the *statements* say what the informal mathematics claims
(misformalization was the main failure mode during development, and the only one the kernel
cannot catch).

## What the machine already guarantees

```bash
lake exe cache get && lake build          # all modules, zero warnings (CI-gated)
./verify.sh                               # THE authoritative check: the real
                                          # leanprover/comparator (statements + permitted
                                          # axioms + kernel replay) vs lean-eval's exact
                                          # jacobian_challenge_diffgeo. CI-gated (comparator.yml).
lake env lean ChallengeConformance.lean   # human-readable conformance (drives the docs table)
python3 scripts/unit_design.py            # unit-DAG strict-deps gate (CI-gated)
```

`./verify.sh` runs the same comparator lean-eval runs, against the same toolchain
(`v4.30.0`) and Mathlib (`c5ea003`) and the verbatim `Challenge.lean`/`Solution.lean`/`config.json`
from lean-eval's `generated/jacobian_challenge_diffgeo/`. A local **"Your solution is okay!"**
should therefore mean a green lean-eval leaderboard run. It supersedes the former local
approximations (`AxiomCheck.lean`, `scripts/comparator_replica.py`), which have been removed.

## Where to read

- **The literate site** (Verso `:literateHtml`, rendered to Pages): every module as a
  literate page — highlighted code with docstrings as prose, search included. The unit
  umbrella files (`Jacobians/<Unit>.lean`) render as the per-unit overview pages.
- **The unit dependency graph**: `docs/units.html` (interactive; edge thickness = kernel-level
  declaration references) or `docs/UNITS_PROPOSAL.md` (same data as text).
- The code itself: one directory per unit under `Jacobians/`, each with an umbrella
  docstring file (`Jacobians/<Unit>.lean`).

## What to review: the statement crosswalk

For each item: read the formal statement, ask "is this the classical theorem?", and check the
listed subtleties.

### The challenge API (the external contract)

| Lean | Informal claim | Subtleties to check |
|---|---|---|
| `genus X` (`Jacobians/Forms/Genus.lean`) | the genus, as `dim_ℂ Ω(X)` (space of global holomorphic 1-forms) | `HolomorphicOneForms` is a `ContMDiffSection` bundle type — check it really is the space of holomorphic 1-forms |
| `genus_eq_zero_iff_homeo` (`Jacobians/GenusSphereHeadline.lean`) | genus 0 ⟺ homeomorphic to S² | the sphere is the metric sphere in `EuclideanSpace ℝ (Fin 3)`; homeomorphism, not biholomorphism |
| `Jacobian X` + 7 instances (`Jacobians.lean`) | the complex torus `ℂ^g / Λ` with its manifold/Lie structure | `Jacobian` is an `ULift` of the concrete `Type 0` torus to `Type u`; the lattice `Λ` is the ℤ-span of period vectors of smooth loops — check `truePeriodLattice` (`Jacobians/JacobianConstruction/PeriodLattice.lean`) |
| `ofCurve P` + `_self`/`_contMDiff`/`_inj` | the Abel–Jacobi map `Q ↦ ∫_P^Q (ω₁…ω_g) mod Λ` | the path integral is `periodVec ∘ smoothPath`; injectivity requires `0 < genus` |
| `pushforward`/`pullback` + functoriality | the induced maps on Jacobians | bundled as continuous additive homs `→ₜ+` |
| `ContMDiff.degree` (`Jacobians/MappingDegree/Degree.lean`) | mapping degree (0 for constants) | defined via fibre counting over regular values |
| `pushforward_pullback` | `f_* ∘ f^* = deg f` | — |

### The five main internal theorems

| Lean | Informal claim | Subtleties to check |
|---|---|---|
| `Jacobians.exists_riemannRoch_divisor` (`Jacobians/RiemannRoch.lean`) | ∃ canonical divisor `K`, ∀ divisors `D`: `l(D) − l(K−D) = deg D + 1 − g` | `lDim` is the dimension of the *germ-quotient* linear system `L(D)/germ-zero` — check the quotient kills only junk (`toFun` values off the defining germ); divisors are finsupps. Proven via Laurent tails (Miranda Ch. VI): `LaurentTail/` + `TailDuality/` |
| `residueSum_pairForm_eq_zero_unconditional` (`Jacobians/ResidueTheorem/ResidueTheoremStokes.lean`) | `∑_p Res_p(h · dg₀) = 0` for meromorphic `g₀, h`, any genus | a meromorphic 1-form is represented as a *pair* `(g₀, h)` meaning `h·dg₀`; residues are chart `resAt` of the pair integrand — check `pairFormResidue` reads the classical residue. The `g·ω₀` variant `residueTheorem_formFn_unconditional` (`ResidueTheorem/ResidueTheoremFormFn.lean`) is derived from it by ω₀-factorization |
| `Jacobians.abelJacobi_twoPoint_ne_zero` (`Jacobians/Abel/AbelFinal.lean`) | on genus ≥ 1, `AJ(P − Q) ≠ 0` for `P ≠ Q` (Abel ⟹ `ofCurve` injective) | check `abelJacobi` (`Jacobians/Meromorphic/Abel.lean`) is the honest path-integral map and `twoPointDivisor` is `P − Q` |
| `Jacobians.hasHolomorphicPrimitives` (`Jacobians/Monodromy/HolomorphicPrimitives.lean`) | on a simply connected surface every holomorphic 1-form has a global primitive | "primitive" is value-wise: `∀ x v, η x v = mfderiv F x v` — check this captures `dF = η` |
| `Jacobians.exists_periodLattice_realBasis` (`Jacobians/PeriodLattice/PeriodLatticeBasis.lean`) | the period lattice has a real basis of rank 2g (so `ℂ^g/Λ` is a torus) | check `closedLoopPeriods` captures all periods and the basis claim gives `IsZLattice` |

### Known deliberate design choices (not bugs)

- **Junk-value conventions**: meromorphic functions are germs; `toFun` carries arbitrary values
  at poles/off-germ points. Statements quotient by `germZero` or use order/germ language. When a
  statement looks weaker than the textbook's, this is usually why — check it is *equivalent*.
- **Pair representation of 1-forms**: no meromorphic-1-form bundle type; forms are `h·dg₀` pairs
  or `h·ω₀` with `ω₀ : HolomorphicOneForms`. The `MeromorphicOneForm` layer
  (`CanonicalForms/`) exists for the canonical-divisor theory only.
- **The submission shim (`SubmissionShimTest.lean`)** uses honest `noncomputable` delegations
  with challenge-exact binders (PR #1, by the lean-eval author); the in-repo theorems use the
  honest definitions throughout.
- **No integration in the monodromy theorem**: primitives are built by discrete continuation
  along chains; `pathPrimValue` plays the role of `∫_γ η`. Equivalence with `lineIntegral` is
  proven where consumed (`Jacobians/AbelWeak/AbelChains.lean`).
- **`backward.isDefEq.respectTransparency false`** appears in ~36 files: an elaboration-time
  workaround for the `restrictScalars ℝ/ℂ` instance diamond at the manifold layer. It affects
  only elaboration; the kernel rechecks every proof without it.

## Suggested review order

1. `Jacobian_challenge.lean` (the verbatim spec) and `ChallengeConformance.lean` — convince
   yourself the contract is the real challenge.
2. The crosswalk statements above, in order; for each, also read its unit's chapter on the
   exposition site (or the umbrella docstring `Jacobians/<Unit>.lean`).
3. The definitions feeding them: `Divisor`, `MeromorphicFunction`/`orderW`,
   `linearSystem`/`lDim` (`Jacobians/Meromorphic/`), `HolomorphicOneForms`
   (`Jacobians/Forms/`), `periodVec`/`lineIntegral` (`Jacobians/Path/`,
   `Jacobians/JacobianConstruction/`).
4. Anything that surprises you: `git log -p <file>` carries the development history, and
   `docs/RETRO.md` the project's honest self-assessment.
