# Project status (auto-maintained)

One-page current state. Read this first before a session.

## Commits tonight (reverse chronological)

```
0810304  Bridge HolomorphicForms to Architecture via dualization
0e5ed58  Start holomorphic 1-forms API skeleton
1b429c8  De-risk the headline architecture
79480d3  Update recon.md
f0288f2  Narrow imports in Jacobians.lean --- 5m -> 51s
e9368c2  Add learning-from-scratch ladder to REFERENCES.md
87c3f2f  Move IsManifold / LieAddGroup sorries into ZLatticeQuotient stubs
6aff0e8  Wire ZLattice quotient into Jacobians.lean --- 3 net sorries closed
aab21f6  Prototype Jacobian via period-lattice quotient
5d17208  Validate architecture on the C target (not R shortcut)
2ad473e  Build ChartedSpace E (E / Lambda) from surjective local homeomorph
0222c80  Narrow imports, add covering-map/local-homeomorph theorems
5d54a1a  First implementation: CompactSpace on E / Lambda
```

## Sorry count

| File                          | Sorries | Kind                          |
|-------------------------------|---------|-------------------------------|
| `Jacobians.lean`              | 19      | content-gated (challenge file) |
| `ZLatticeQuotient.lean`       | 2       | IsManifold + LieAddGroup stubs |
| `HolomorphicForms.lean`       | 9       | content skeleton              |
| `FormsToJacobian.lean`        | 8       | bridge: isos + duals + ambient functoriality |
| `Architecture.lean`           | 0       | *architecture de-risked*      |
| `ChartedSpaceOfLocalHomeomorph.lean` | 0 | manifold general-purpose     |
| `JacobianValidate.lean`       | 0       | instance regression test      |
| **Total**                     | **38**  |                               |

Note: `Jacobians.lean` only imports `ZLatticeQuotient` and
`ChartedSpaceOfLocalHomeomorph` so a bare `lake build` shows 21
sorries. `HolomorphicForms` and `FormsToJacobian` are built via
`lake build Jacobians.HolomorphicForms Jacobians.FormsToJacobian`.

## Build performance

- `Jacobians.lean` clean rebuild: **51 s** (was 5 min before `#min_imports`).
- Support files: 7–35 s each with narrow imports.
- Full project incremental: 9–20 s.

## What's de-risked

- Period-lattice encoding of `Jacobian X` supports all challenge
  structural instances (`AddCommGroup`, `TopologicalSpace`, `T2Space`,
  `CompactSpace`, `ChartedSpace`). Proven.
- The headline `pushforward_pullback = deg • id` will descend from the
  ambient degree identity, proved abstractly in `Architecture.lean`.
- The content pipeline (`HolomorphicForms` → `FormsToJacobian` →
  `Architecture` → challenge `Jacobian.pushforward_pullback`) sketched
  end-to-end; filling in 4 sorries at the bridge + 9 at the content
  layer closes the whole cascade.

## What's NOT yet touched

- Actual construction of `HolomorphicOneForms X` as a type (currently `sorry`).
- The content-level degree identity `f_* ∘ f^* = d • id` on forms.
- `IsManifold` and `LieAddGroup` instances on `E ⧸ Λ` — have documented
  proof sketches but both are `sorry`.
- `ContMDiff.degree` definition.
- `genus` definition and `genus_eq_zero_iff_homeo`.
- `ofCurve` and `ofCurve_inj` (Abel's theorem).
- Period lattice construction and `IsZLattice ℝ` for it.
- Universe polymorphism `Type u` for `Jacobian`. Dropped to `Type`;
  explicit TODO pending a `ChartedSpace`-over-`ULift` constructor that
  Mathlib doesn't have.

## Directory map

```
/home/rado/jacobian/
├── Jacobians.lean              -- challenge file, 19 sorries
├── Jacobians/
│   ├── Architecture.lean       -- headline-identity descent (0 sorries)
│   ├── ChartedSpaceOfLocalHomeomorph.lean  -- mathlib candidate (0 sorries)
│   ├── ZLatticeQuotient.lean   -- quotient Lie-group scaffold (2 sorries)
│   ├── HolomorphicForms.lean   -- content skeleton (9 sorries)
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

## Recommended next steps (ranked by likelihood-of-failure, per user directive)

All remaining risk is in **content** now, not architecture. Candidates:

1. **Content degree identity**: fill in `pushforwardForm_pullbackForm_eq`
   in `HolomorphicForms.lean` — the integration-over-fibres calculation.
   Hardest because it needs the full definition of pushforward of 1-forms
   and a Fubini-style argument. Biggest payoff: plugging this in with the
   bridge closes the challenge's headline identity.
2. **Actual `HolomorphicOneForms X` construction** — building the sheaf
   of holomorphic 1-forms or sections of the cotangent bundle. Big new
   Mathlib theory.
3. **`ofCurve_inj` (Abel's theorem)** — headline theorem; needs
   meromorphic functions + divisor theory + Riemann–Roch.
4. **`genus_eq_zero_iff_homeo`** (uniformization for genus 0) — the
   single hardest theorem in the challenge. Needs either PDE or 2D
   surface classification.
5. **`IsManifold` on `E ⧸ Λ`** — not content-risky; pure Lean technical
   using "transitions are locally translations by lattice elements".
6. **Universe polymorphism ULift** — blocked on a Mathlib contribution.

