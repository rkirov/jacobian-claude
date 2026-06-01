# Wiring `genus_eq_zero_iff_homeo` to the DegreeOneSphere endgame

**Goal.** Discharge the `→` (forward) direction of the challenge theorem
`Jacobians.genus_eq_zero_iff_homeo` (`Genus.lean:81`, currently `sorry`) using the proven-modulo
endgame `Jacobians.nonempty_homeo_sphere_of_singleSimplePole` (`DegreeOneSphere.lean:256`).

## Two blockers (why this is a refactor, not a one-line edit)

1. **Import cycle.** `DegreeOneSphere` imports `ProjectiveLine`, which imports `Genus`. So
   `Genus.lean` **cannot** `import Jacobians.DegreeOneSphere` to fill its sorry — that's circular.
   The forward implication must be assembled in a module **downstream of both** Genus and
   DegreeOneSphere.

2. **Typeclass gap.** `genus_eq_zero_iff_homeo` is stated with
   `[TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X] [ChartedSpace ℂ X]
   [IsManifold 𝓘(ℂ) ω X]` — **no `[Nonempty X]`**. The DegreeOneSphere endgame variable block
   **requires `[Nonempty X]`** (used by `exists_ne_of_chartedSpace_complex` etc.). `[ConnectedSpace X]`
   does NOT give `[Nonempty X]` in Lean. Either add `[Nonempty X]` to the challenge lemma (check the
   challenge spec `Jacobian_challenge.lean` allows it — the conformance file pins the exact signature)
   OR derive nonemptiness another way (e.g. a compact connected manifold modelled on ℂ is nonempty iff
   the type is — but `genus X = 0` side may give a point).

## Recommended path

- **Do NOT edit Genus.lean's statement-site proof inline.** Keep `genus_eq_zero_iff_homeo`'s sorry
  where it is, OR convert it to consume a new downstream lemma.
- Create/extend a module **downstream of both** (e.g. a new `Jacobians/GenusSphere.lean`, or extend
  `DegreeOneSphere.lean` itself since it already imports the needed pieces) that proves:
  `genus_eq_zero_forward : genus X = 0 → Nonempty (X ≃ₜ S²)` by
  `exists_simplePole_of_genus_zero (RR input, still sorry) ▸ nonempty_homeo_sphere_of_singleSimplePole`.
- The **backward** direction `Nonempty (X ≃ₜ S²) → genus X = 0` is `genus_zero_of_homeo_sphere`
  (was a Roadmap input, now needs a real home — Ω(ℂℙ¹)=0 content).
- Then discharge `Genus.genus_eq_zero_iff_homeo` by having it **import the downstream module** — but
  that re-introduces the cycle (Genus ← downstream ← Genus). RESOLUTION: the challenge entry point is
  `ChallengeConformance.lean` (imports `Jacobians`), which is ABOVE everything. The clean fix is to
  state the iff in a top-level module that is NOT imported by ProjectiveLine — i.e. **move the
  `genus_eq_zero_iff_homeo` statement out of Genus.lean** into a leaf module that imports both Genus
  and DegreeOneSphere, and have ChallengeConformance pick it up from there. Verify the conformance file
  resolves the name (`Jacobians.genus_eq_zero_iff_homeo`) regardless of which module defines it.

## Remaining sorries this still rests on (NOT closed by wiring — the real math)
- `exists_simplePole_of_genus_zero` (Riemann–Roch consequence `l(P)=2`; Dolbeault/Serre wall).
- `genus_zero_of_homeo_sphere` (Ω(ℂℙ¹)=0).
- DegreeOneSphere's own 3: `contMDiff_toSphere`, `toSphere_regular_at_pole`, `degreeOne_homeo`.

So wiring is **plumbing that connects the reduction**, making the dependency real-in-code; it does NOT
reduce the count of genuine analytic gaps. Worth doing for structure, but it's not a sorry-closing step.
See `project_loop_off_branch_6_leftover.md`, `feedback_verify_agent_commits.md`.
