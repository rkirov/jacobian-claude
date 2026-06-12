# Reviewer's guide

This repository claims a complete, sorry-free solution of Kevin Buzzard's Jacobians challenge.
Every proof is checked by Lean's kernel, so **proof correctness is not the thing to review** —
what needs human eyes is whether the *statements* say what the informal mathematics claims
(misformalization was the main failure mode during development, and the only one the kernel
cannot catch).

## What the machine already guarantees

```bash
lake exe cache get && lake build          # all ~8.6k jobs, no sorry warnings
lake env lean ChallengeConformance.lean   # exit 0: every v0.4 spec signature, verbatim
lake env lean ChallengeLeaderboard.lean   # exit 0: the lean-eval leaderboard form
lake env lean scripts/axiom_check_final.lean   # axiom audit of the headliners
```

Every declaration reports `#print axioms` = `[propext, Classical.choice, Quot.sound]`.
The lean-eval comparator (independent third-party checker) has accepted the submission.

## What to review: the statement crosswalk

For each item: read the formal statement, ask "is this the classical theorem?", and check the
listed subtleties. File paths are clickable from the repo root.

### The challenge API (the external contract)

| Lean | Informal claim | Subtleties to check |
|---|---|---|
| `genus X` (`Jacobians/Genus.lean`) | the genus, as `dim_ℂ Ω(X)` (space of global holomorphic 1-forms) | `HolomorphicOneForms` is a `ContMDiffSection` bundle type — check it really is the space of holomorphic 1-forms |
| `genus_eq_zero_iff_homeo` (`Jacobians/GenusSphereHeadline.lean`) | genus 0 ⟺ homeomorphic to S² | the sphere is the metric sphere in `EuclideanSpace ℝ (Fin 3)`; homeomorphism, not biholomorphism |
| `Jacobian X` + 7 instances (`Jacobians.lean`) | the complex torus `ℂ^g / Λ` with its manifold/Lie structure | `Jacobian` is an `ULift` of the concrete `Type 0` torus to `Type u`; the lattice `Λ` is the ℤ-span of period vectors of smooth loops — check `truePeriodLattice` |
| `ofCurve P` + `_self`/`_contMDiff`/`_inj` | the Abel–Jacobi map `Q ↦ ∫_P^Q (ω₁…ω_g) mod Λ` | the path integral is `periodVec ∘ smoothPath`; injectivity requires `0 < genus` |
| `pushforward`/`pullback` + functoriality | the induced maps on Jacobians | bundled as continuous additive homs `→ₜ+` |
| `ContMDiff.degree` | mapping degree (0 for constants) | defined via fibre counting over regular values |
| `pushforward_pullback` | `f_* ∘ f^* = deg f` | — |

### The five main internal theorems

| Lean | Informal claim | Subtleties to check |
|---|---|---|
| `Jacobians.exists_riemannRoch_divisor` (`Jacobians/RiemannRoch.lean`) | ∃ canonical divisor `K`, ∀ divisors `D`: `l(D) − l(K−D) = deg D + 1 − g` | `lDim` is the dimension of the *germ-quotient* linear system `L(D)/germ-zero` — check the quotient kills only junk (`toFun` values off the defining germ); divisors are finsupps |
| `residueSum_pairForm_eq_zero_unconditional` (`Jacobians/Dolbeault/ResidueTheoremStokes.lean`) | `∑_p Res_p(h · dg₀) = 0` for meromorphic `g₀, h`, any genus | a meromorphic 1-form is represented as a *pair* `(g₀, h)` meaning `h·dg₀`; residues are chart `resAt` of the pair integrand — check `pairFormResidue` reads the classical residue |
| `Jacobians.abelJacobi_twoPoint_ne_zero` (`Jacobians/Abel.lean`) | on genus ≥ 1, `AJ(P − Q) ≠ 0` for `P ≠ Q` (Abel ⟹ `ofCurve` injective) | check `abelJacobi` is the honest path-integral map and `twoPointDivisor` is `P − Q` |
| `Jacobians.hasHolomorphicPrimitives` (`Jacobians/HolomorphicPrimitives.lean`) | on a simply connected surface every holomorphic 1-form has a global primitive | "primitive" is value-wise: `∀ x v, η x v = mfderiv F x v` — check this captures `dF = η` |
| `Jacobians.exists_periodLattice_realBasis` (`Jacobians/PeriodLattice.lean`) | the period lattice has a real basis of rank 2g (so `ℂ^g/Λ` is a torus) | check `closedLoopPeriods` captures all periods and the basis claim gives `IsZLattice` |

### Known deliberate design choices (not bugs)

- **Junk-value conventions**: meromorphic functions are germs; `toFun` carries arbitrary values
  at poles/off-germ points. Statements quotient by `germZero` or use order/germ language. When a
  statement looks weaker than the textbook's, this is usually why — check it is *equivalent*.
- **Pair representation of 1-forms**: no meromorphic-1-form bundle type; forms are `h·dg₀` pairs
  or `h·ω₀` with `ω₀ : HolomorphicOneForms`. The two `MeromorphicOneForm` layers exist for the
  canonical-divisor theory only.
- **The degree shim in `SubmissionShimTest.lean`** carries a deliberately weak signature with a
  classical case split — it matches the benchmark's elaborated hole and delegates to the honest
  `ContMDiff.degree`; the in-repo theorems use the honest one.
- **No integration in the monodromy theorem**: primitives are built by discrete continuation
  along chains; `pathPrimValue` plays the role of `∫_γ η`. Equivalence with `lineIntegral` is
  proven where consumed (`AbelChains.lean`).

## Suggested review order

1. `Jacobian_challenge.lean` (the verbatim spec) and `ChallengeConformance.lean` — convince
   yourself the contract is the real challenge.
2. The crosswalk statements above, in order; for each, also skim the module docstring of its file.
3. The definitions feeding them: `Divisor`, `MeromorphicFunction`/`orderW`, `linearSystem`/`lDim`
   (`Jacobians/Abel.lean`, `Jacobians/LinearSystem.lean`), `HolomorphicOneForms`
   (`Jacobians/HolomorphicForms.lean`), `periodVec`/`lineIntegral` (`Jacobians/LineIntegral.lean`).
4. Anything that surprises you: `git log -p <file>` carries the development history, and
   `docs/RETRO.md` the project's honest self-assessment.

## Repository map

See `docs/MODULE_MAP.md` (generated; regenerate with `python3 scripts/module_map.py`) for the
layered import structure with one-line summaries of all modules.
