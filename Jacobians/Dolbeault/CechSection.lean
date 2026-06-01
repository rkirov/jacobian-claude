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

  NOTE: the meromorphy infrastructure's typeclass footprint was generalised (commit doing the
  "IsMeromorphic cleanup"): `IsMeromorphic.zero` (Abel) and the `MeromorphicFunction` ℂ-module
  instances (RiemannRoch) now require only `[ChartedSpace ℂ]`, so they apply to the non-compact
  open submanifold `↥U`. We keep the bare-function encoding `Submodule ℂ (↥U → ℂ)` here because it
  makes the Čech differential plain restriction; the `Submodule ℂ (MeromorphicFunction ↥U)` encoding
  is now also available should it prove cleaner downstream.
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
  zero_mem' := ⟨IsMeromorphic.zero _, fun x => by rw [ordU_zero]; exact le_top⟩
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

/-! ### Sheaf restriction — the building block of the Čech differential

For `V ≤ U` (opens), restriction `𝒪_D(U) → 𝒪_D(V)` is plain precomposition with the open inclusion
`↥V → ↥U`. Both `↥V`- and `↥U`-charts are `OpenPartialHomeomorph.subtypeRestr`s of the *same* ambient
chart `chartAt ℂ v.1` (`TopologicalSpace.Opens.chartAt_eq`), so meromorphy and order are preserved. -/

section Restriction
variable {D : Divisor X} {U V : Opens X}

/-- The open inclusion `↥V → ↥U` for `V ≤ U`. -/
def openIncl (h : V ≤ U) : V → U := fun v => ⟨v.1, h v.2⟩

@[simp] theorem openIncl_val (h : V ≤ U) (v : V) : (openIncl h v).1 = v.1 := rfl

/-- **Mechanical leaf** (chart bookkeeping; to be discharged in the bottom-out pass): the order is
preserved under restriction to a smaller open. Both charts are `subtypeRestr`s of the same ambient
chart (`Opens.chartAt_eq`), so the chart pullbacks agree near the chart point and `meromorphicOrderAt`
is unchanged (`MeromorphicAt.congr`). NOT a deep analytic gap. -/
theorem ordU_comp_openIncl (h : V ≤ U) (f : U → ℂ) (v : V) :
    ordU (f ∘ openIncl h) v = ordU f (openIncl h v) := sorry

/-- **Mechanical leaf** (companion to `ordU_comp_openIncl`): meromorphy on `↥U` restricts to the open
sub-submanifold `↥V`. -/
theorem isMeromorphic_comp_openIncl (h : V ≤ U) {f : U → ℂ}
    (hf : IsMeromorphic (U : Type _) f) : IsMeromorphic (V : Type _) (f ∘ openIncl h) := sorry

/-- Restriction of sections `𝒪_D(U) → 𝒪_D(V)` for `V ≤ U`. -/
noncomputable def OmegaD.restrict (h : V ≤ U) : OmegaD D U →ₗ[ℂ] OmegaD D V :=
  ((LinearMap.funLeft ℂ ℂ (openIncl h)).domRestrict (OmegaD D U)).codRestrict (OmegaD D V)
    fun f => ⟨isMeromorphic_comp_openIncl h f.2.1, fun v => by
      show (-(D v.1) : WithTop ℤ) ≤ ordU ((f : U → ℂ) ∘ openIncl h) v
      rw [ordU_comp_openIncl h]; exact f.2.2 (openIncl h v)⟩

@[simp] theorem OmegaD.restrict_coe (h : V ≤ U) (f : OmegaD D U) :
    ((OmegaD.restrict h f : V → ℂ)) = (f : U → ℂ) ∘ openIncl h := rfl

end Restriction

end Jacobians.Dolbeault
