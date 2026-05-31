/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Compactification.OnePoint.Sphere
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Complex.Basic
import Jacobians.Genus

/-!
# The complex Riemann sphere `ℂℙ¹` as a compact complex 1-manifold

We model `ℂℙ¹` as the Alexandroff one-point compactification `OnePoint ℂ = ℂ ∪ {∞}`
(`RiemannSphere`). Mathlib provides the topology and all the point-set instances
(`CompactSpace`, `T2Space`, `ConnectedSpace`) for free, since `ℂ` is a proper —
hence weakly-locally-compact — Hausdorff, preconnected, noncompact space.

On top of that we build, by hand, the structure required by the Jacobians challenge
vocabulary (mirroring `Jacobians.Roadmap`):

* `ChartedSpace ℂ RiemannSphere` from the two standard charts
  `U₀` (the `ℂ`-affine chart, identity on `ℂ`, source `{∞}ᶜ`) and
  `U∞` (the chart at `∞`, the inversion `z ↦ 1/z`, source `{0}ᶜ`);
* `IsManifold 𝓘(ℂ) ω RiemannSphere` — the transition map between the two charts is
  the holomorphic inversion `z ↦ 1/z` on `ℂˣ`;
* a homeomorphism `RiemannSphere ≃ₜ S²` to the Euclidean 2-sphere (via Mathlib's
  `onePointEquivSphereOfFinrankEq`, since `ℂ ≃ ℝ²` has real dimension `2`);
* `genus RiemannSphere = 0` (the space of global holomorphic 1-forms is `⊥`), by
  Liouville: a global holomorphic 1-form pulls back to an entire function on the
  affine chart that extends holomorphically over `∞`, hence is bounded, hence
  constant, and the value at `∞` forces it to vanish.

## References

Forster, *Lectures on Riemann Surfaces*, §1, §5, §10 (`ℂℙ¹`, charts, `Ω(ℂℙ¹) = 0`).
Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. I.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open OnePoint Complex

namespace Jacobians

/-- The **Riemann sphere** `ℂℙ¹`, modelled as the one-point compactification
`OnePoint ℂ = ℂ ∪ {∞}`. -/
abbrev RiemannSphere : Type := OnePoint ℂ

namespace RiemannSphere

/-! ### Milestone 1 — the free point-set instances

All of these are found by `inferInstance` from Mathlib's `OnePoint` development;
we record them explicitly so the manifold vocabulary downstream can rely on them
being present (and to document that the model has them). -/

instance : TopologicalSpace RiemannSphere := inferInstance
instance : CompactSpace RiemannSphere := inferInstance
instance : T2Space RiemannSphere := inferInstance
instance : ConnectedSpace RiemannSphere := inferInstance
instance : Nonempty RiemannSphere := inferInstance

end RiemannSphere

end Jacobians
