/-
  Dolbeault ladder — the concrete Čech layer (G3 scaffold).

  This is the first rung of the sorry-free Riemann–Roch build, following the representation
  decided in `docs/dolbeault_ladder_derisk.md`:

    * sections of the sheaf `𝒪_D` over an open `U ⊆ X` are modelled **intrinsically on the open
      submanifold `↥U`** (Mathlib gives `↥U` a `ChartedSpace ℂ` + `IsManifold 𝓘(ℂ) ω` structure
      automatically), as a `Submodule ℂ` of the bare function space `↥U → ℂ`;
    * the membership predicate bundles meromorphy-on-`↥U` with the order bound `-D x ≤ ord_x f`;
    * because sections are genuine functions on `↥U`, the Čech differential is plain **restriction**
      (precomposition with `Set.inclusion`), with no chart-transition cocycle data.

  NOTE (measured during the de-risk spike): the repo's `MeromorphicFunction` ℂ-module instances and
  `IsMeromorphic.zero` carry spurious `CompactSpace`/`ConnectedSpace`/`Nonempty` hypotheses, so the
  alternative encoding `Submodule ℂ (MeromorphicFunction ↥U)` does NOT type-check for a (non-compact)
  open `↥U`. The bare-function encoding here sidesteps that; a clean follow-up is to generalise those
  instances' typeclass footprint (they only use `[ChartedSpace ℂ]`). The `.add/.neg/.const_smul/…`
  predicate lemmas are already generalised (under an `omit` in `RiemannRoch.lean`); only
  `IsMeromorphic.zero` is inlined below.
-/
import Jacobians.RiemannRoch

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

-- The meromorphy algebra here uses only `[ChartedSpace ℂ]`; the ambient compactness/connectedness
-- carried by the consumers is genuinely unused (see the generalisation note in the header).
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- Order of a bare function on the open submanifold `↥U`, read in `U`'s own chart at `x`.
(Chart-invariant; intrinsic to `↥U`.) -/
noncomputable def ordU {U : Opens X} (f : U → ℂ) (x : U) : WithTop ℤ :=
  meromorphicOrderAt (f ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)

/-- The zero function is meromorphic on `↥U` (inlined from `IsMeromorphic.zero`, which carries a
spurious `CompactSpace` hypothesis). -/
theorem isMeromorphic_zero_opens (U : Opens X) : IsMeromorphic (U : Type _) (fun _ => 0) := by
  intro x
  show MeromorphicAt (fun _ => (0 : ℂ)) ((chartAt (H := ℂ) x) x)
  exact MeromorphicAt.const 0 _

/-- The order of the zero function on `↥U` is `⊤`. -/
theorem ordU_zero {U : Opens X} (x : U) : ordU (0 : U → ℂ) x = ⊤ := by
  rw [ordU, show ((0 : U → ℂ) ∘ (chartAt (H := ℂ) x).symm) = (fun _ => (0 : ℂ)) from rfl,
    meromorphicOrderAt_eq_top_iff]
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- **Sections of `𝒪_D` over an open `U`** (Forster's `𝒪_D(U)`): functions meromorphic on the open
submanifold `↥U` whose order is `≥ −D` at every point of `U`. A `Submodule ℂ` of `↥U → ℂ`. -/
noncomputable def OmegaD (D : Divisor X) (U : Opens X) : Submodule ℂ (U → ℂ) where
  carrier := {f | IsMeromorphic (U : Type _) f ∧ ∀ x : U, (-(D x.1) : WithTop ℤ) ≤ ordU f x}
  add_mem' {f g} hf hg :=
    ⟨hf.1.add hg.1, fun x => le_trans (le_min (hf.2 x) (hg.2 x))
      (meromorphicOrderAt_add (hf.1 x) (hg.1 x))⟩
  zero_mem' := ⟨isMeromorphic_zero_opens U, fun x => by rw [ordU_zero]; exact le_top⟩
  smul_mem' c f hf := ⟨hf.1.const_smul c, fun x => by
    rcases eq_or_ne c 0 with hc | hc
    · simpa only [hc, zero_smul, ordU_zero] using le_top
    · refine le_trans (hf.2 x) (le_of_eq ?_)
      show ordU f x = ordU (c • f) x
      rw [ordU, ordU]
      exact (meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using hc)).symm⟩

@[simp] theorem mem_OmegaD {D : Divisor X} {U : Opens X} {f : U → ℂ} :
    f ∈ OmegaD D U ↔ IsMeromorphic (U : Type _) f ∧ ∀ x : U, (-(D x.1) : WithTop ℤ) ≤ ordU f x :=
  Iff.rfl

end Jacobians.Dolbeault
