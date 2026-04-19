import Jacobians.Architecture
import Jacobians.HolomorphicForms

/-!
# Bridge: `HolomorphicForms` to `Architecture`

Shows how the content-level pushforward/pullback of holomorphic 1-forms
(with their degree identity `f_* ∘ f^* = d • id` on forms) supplies the
ambient linear maps `Φ`, `Ψ` and the ambient degree identity that
`Architecture.pushforward_pullback_of_ambient` needs.

This file **is a sketch**. It documents the chain of steps required; the
concrete constructions (basis choice, dualization, transpose) are
sorried. What it demonstrates is that the architecture plugs into the
content, so filling in HolomorphicForms' sorries + choosing a basis iso
gets us to the challenge's headline identity.

## The bridge (one line)

```
Jacobian's (Φ, Ψ) = (ambientIso ⁻¹) ∘ dualize(pullback/pushforward of 1-forms) ∘ ambientIso
```

## The identity (one line)

```
pushforwardForm_pullbackForm_eq f hf d  ⟹  Architecture.pushforward_pullback_of_ambient
```

(dualization preserves the scalar on the identity.)

## What plays what role

|Jacobian side (Architecture.lean)   |Forms side (HolomorphicForms.lean)  |
|------------------------------------|------------------------------------|
|`Φ : (Fin gX → ℂ) →L[ℝ] (Fin gY → ℂ)` |dual of `pullbackForm f hf`         |
|`Ψ : (Fin gY → ℂ) →L[ℝ] (Fin gX → ℂ)` |dual of `pushforwardForm f hf`      |
|`d` (ambient scalar)                |`ContMDiff.degree f hf`             |
|`Φ (Ψ y) = d • y`                   |`pushforwardForm_pullbackForm_eq`   |

-/

namespace Jacobians.Bridge

open scoped Manifold ContDiff

variable {X Y : Type*}
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
  [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

/-! ### TODO(math): choice of basis iso -/

/-- **TODO(math)**: a linear isomorphism identifying `Fin (genus X) → ℂ`
with `HolomorphicOneForms X` (via a choice of basis). In practice this
will come from `Basis.ofFinrankEq` once we know
`finrank ℂ (HolomorphicOneForms X) = genus X`. -/
noncomputable def ambientIso (X : Type*) [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] (g : ℕ) :
    (Fin g → ℂ) ≃ₗ[ℂ] HolomorphicOneForms X := sorry

/-! ### TODO(math): from Forms to Ambient linear maps

The steps:

1. Start with `pullbackForm f hf : H⁰(Y, Ω¹) →L[ℂ] H⁰(X, Ω¹)`.
2. Dualize to get `(pullbackForm f hf)^T : H⁰(X, Ω¹)ᵛ →L[ℂ] H⁰(Y, Ω¹)ᵛ`.
3. Compose with `ambientIso` isos to get
   `Φ : (Fin gX → ℂ) →L[ℝ] (Fin gY → ℂ)` (restrict scalars ℂ → ℝ).
4. Dually for pushforwardForm → Ψ.

Each step is clean linear algebra; the composition is just the stacking.
Sorried as a single definition below. -/

/-- **TODO(math)**: the ambient ℝ-linear map `Φ` induced by the pullback
of forms along `f : X → Y`. -/
noncomputable def ambientPhi {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin gX → ℂ) →L[ℝ] (Fin gY → ℂ) := sorry

/-- **TODO(math)**: the ambient ℝ-linear map `Ψ` induced by the pushforward
of forms along `f : X → Y`. -/
noncomputable def ambientPsi {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    (Fin gY → ℂ) →L[ℝ] (Fin gX → ℂ) := sorry

/-- **TODO(math)**: the ambient degree identity, dualized from
`pushforwardForm_pullbackForm_eq`. -/
theorem ambientPhi_ambientPsi_eq {gX gY : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (d : ℕ)
    (y : Fin gY → ℂ) :
    ambientPhi (gX := gX) (gY := gY) f hf (ambientPsi f hf y) = (d : ℕ) • y := sorry

/-! ### Functoriality on the ambient (dualizes `pullbackForm` functoriality) -/

/-- **TODO(math)**: `ambientPhi id = id`. Dualizes `pullbackForm_id`. -/
theorem ambientPhi_id {g : ℕ} (x : Fin g → ℂ) :
    ambientPhi (X := X) (Y := X) (gX := g) (gY := g) id contMDiff_id x = x := sorry

/-- **TODO(math)**: `ambientPhi (g ∘ f) = ambientPhi g ∘ ambientPhi f`.
Dualizes `pullbackForm_comp` (contravariance-of-dual). -/
theorem ambientPhi_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    {gX gY gZ : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f))
    (x : Fin gX → ℂ) :
    ambientPhi (gX := gX) (gY := gZ) (g ∘ f) hgf x =
      ambientPhi (gX := gY) (gY := gZ) g hg
        (ambientPhi (gX := gX) (gY := gY) f hf x) := sorry

/-- **TODO(math)**: `ambientPsi id = id`. -/
theorem ambientPsi_id {g : ℕ} (y : Fin g → ℂ) :
    ambientPsi (X := X) (Y := X) (gX := g) (gY := g) id contMDiff_id y = y := sorry

/-- **TODO(math)**: `ambientPsi (g ∘ f) = ambientPsi f ∘ ambientPsi g`. -/
theorem ambientPsi_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z]
    [ConnectedSpace Z] [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    {gX gY gZ : ℕ}
    (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g)
    (hgf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (g ∘ f))
    (z : Fin gZ → ℂ) :
    ambientPsi (gX := gX) (gY := gZ) (g ∘ f) hgf z =
      ambientPsi (gX := gX) (gY := gY) f hf
        (ambientPsi (gX := gY) (gY := gZ) g hg z) := sorry

/-! ### How to plug into Architecture

Given the ambient maps above and a (future) lattice-preservation proof,
`Architecture.pushforward_pullback_of_ambient` supplies the final
identity on the Jacobian quotient. Spelled out as a theorem once the
content is filled:

```
theorem Jacobian_pushforward_pullback
    (f : X → Y) (hf : …) (d : ℕ) (hd : d = ContMDiff.degree f hf)
    (ΛX ΛY …) (hΦΛ : …) (hΨΛ : …)
    (P : Jacobian Y) :
    Jacobian.pushforward f hf (Jacobian.pullback f hf P) = d • P := by
  -- Construct Φ = ambientPhi, Ψ = ambientPsi; apply
  -- Architecture.pushforward_pullback_of_ambient with
  -- hΦΨ = ambientPhi_ambientPsi_eq.
  sorry
```
-/

end Jacobians.Bridge
