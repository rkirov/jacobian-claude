# Project status (auto-maintained)

One-page current state. Read this first before a session.

## Headline

**Challenge sorry count: 24 → 14.** The headline `pushforward_pullback`
theorem and all four functoriality lemmas (`pushforward_id_apply`,
`pullback_id_apply`, `pushforward_comp_apply`, `pullback_comp_apply`)
are **closed in the challenge file**, contingent on content sorries in
`FormsToJacobian.lean` and `HolomorphicForms.lean`.

## Sorry count by file

| File                          | Sorries | Kind                          |
|-------------------------------|---------|-------------------------------|
| `Jacobians.lean`              | 14      | content-gated (challenge file) |
| `ZLatticeQuotient.lean`       | 2       | IsManifold + LieAddGroup stubs |
| `HolomorphicForms.lean`       | 10      | content skeleton              |
| `FormsToJacobian.lean`        | 8       | bridge (iso + duals + ambient functoriality) |
| `Architecture.lean`           | 0       | *architecture de-risked*      |
| `ChartedSpaceOfLocalHomeomorph.lean` | 0 | manifold general-purpose     |
| `JacobianValidate.lean`       | 0       | instance regression test      |
| **Total**                     | **34**  |                               |

## Remaining Jacobians.lean sorries (14)

1. `periodLattice X` definition
2. `DiscreteTopology (periodLattice X)`
3. `IsZLattice ℝ (periodLattice X)`
4. `genus X` definition
5. `genus_eq_zero_iff_homeo`
6. `ofCurve`
7. `ofCurve_contMDiff`
8. `ofCurve_self`
9. `ofCurve_inj` (Abel's theorem)
10. `pushforward_contMDiff`
11. `pullback_contMDiff`
12. `ambientPhi_preserves_lattice` (wire-up dependency)
13. `ambientPsi_preserves_lattice` (wire-up dependency)
14. `ContMDiff.degree`

## Content sorries by layer

**`HolomorphicForms.lean` (10 sorries):** define the type, structural
instances, `pullbackForm`/`pushforwardForm` operations, their
functoriality, and the degree identity `f_* ∘ f^* = d • id` on forms.

**`FormsToJacobian.lean` (8 sorries):** bridge — basis iso, `ambientPhi`,
`ambientPsi`, `ambientPhi_ambientPsi_eq` (degree identity on ambient),
`ambientPhi_id`, `ambientPhi_comp`, `ambientPsi_id`, `ambientPsi_comp`.

## Build performance

- `Jacobians.lean` clean rebuild: 51 s (was 5 min before `#min_imports`).
- Support files: 7–35 s each with narrow imports.
- Full project incremental: 9–20 s.
- `@[reducible]` on `Jacobian X` does not regress build time because of
  the narrow imports.

## What's de-risked

- Period-lattice encoding of `Jacobian X` supports all challenge
  structural instances (`AddCommGroup`, `TopologicalSpace`, `T2Space`,
  `CompactSpace`, `ChartedSpace`). **Proven.**
- The headline `pushforward_pullback = deg • id` descends from the
  ambient degree identity. **Proven abstractly in `Architecture.lean`
  and applied in `Jacobians.lean`.**
- Functoriality: `pushforward/pullback` identity and composition. **Proven.**
- The content pipeline (`HolomorphicForms` → `FormsToJacobian` →
  `Architecture` → challenge `pushforward_pullback`) is connected
  end-to-end. Filling content sorries closes the whole cascade.
- `ChartedSpace`-from-surjective-local-homeomorphism as a general
  constructor (Mathlib candidate).

## What's NOT yet touched

- Actual construction of `HolomorphicOneForms X` as a concrete type.
- The content-level degree identity `f_* ∘ f^* = d • id` on forms
  (integration-over-fibres).
- `IsManifold` and `LieAddGroup` instances on `E ⧸ Λ` — proof sketches
  documented, both sorried.
- `ContMDiff.degree` definition.
- `genus` definition and `genus_eq_zero_iff_homeo`.
- `ofCurve` and `ofCurve_inj` (Abel's theorem).
- Period lattice construction and `IsZLattice ℝ`.
- Universe polymorphism `Type u` for `Jacobian`.

## Directory map

```
/home/rado/jacobian/
├── Jacobians.lean              -- challenge file, 14 sorries
├── Jacobians/
│   ├── Architecture.lean       -- headline-identity descent (0 sorries)
│   ├── ChartedSpaceOfLocalHomeomorph.lean  -- mathlib candidate (0 sorries)
│   ├── ZLatticeQuotient.lean   -- quotient Lie-group scaffold (2 sorries)
│   ├── HolomorphicForms.lean   -- content skeleton (10 sorries)
│   ├── FormsToJacobian.lean    -- bridge (8 sorries)
│   └── JacobianValidate.lean   -- instance regression
├── docs/
│   ├── DESIGN.md
│   ├── recon.md
│   ├── REFERENCES.md
│   └── STATUS.md               (this file)
├── human_input.md              -- steering log
├── lakefile.lean
├── lean-toolchain
└── README.md
```

## Recommended next steps

1. **`pushforwardForm_pullbackForm_eq`** — content-level degree identity
   on forms. Dualizes to `ambientPhi_ambientPsi_eq`, which is the
   hypothesis used by the headline theorem. Classical
   integration-over-fibres argument. Hardest remaining piece but
   highest payoff.
2. **Define `HolomorphicOneForms X`** — concrete type. Unlocks the
   rest of the content.
3. **`IsManifold` / `LieAddGroup` on quotient** — pure Lean technical,
   tractable with the documented proof sketch.
4. **`ContMDiff.degree`** definition — medium effort, unblocks the
   degree parameter at the wire-up.
5. **`ofCurve_inj`** / **`genus_eq_zero_iff_homeo`** — headline
   classical theorems, substantial content.
