/-
  Dolbeault ladder — Čech finiteness (Forster 14.9), STEP 1.

  The Banach space `BddHol U` of bounded holomorphic functions on an open `U ⊆ ℂ`, and the fact
  that restriction to a relatively-compact convex inner set `K ⋐ U` is a COMPACT operator
  `BddHol U →L[ℂ] (K →ᵇ ℂ)`. This is the Montel-compactness input to the abstract Schwartz
  finiteness lemma (Forster 14.8), which forces `H¹(X, 𝒪_D)` finite-dimensional.

  The compact-operator statement reduces, via the standard characterization
  `isCompactOperator_iff_isCompact_closure_image_closedBall`, to the proven Montel atom
  `Jacobians.Dolbeault.CechFiniteness.isCompact_closure_restrict_bddHolo`.

  Encoding: `BddHol U` is the `ℂ`-subspace of `ℂ → ℂ` of functions that are analytic on `U`, vanish
  off `U` (a canonical normal form pinning junk values, making the sup-`U` seminorm a genuine norm
  and the bcf-embedding injective), and bounded on `U`. The norm `‖f‖ = ⨆ z, ‖f z‖` over `↥U` is
  induced by the isometric embedding into the Banach space `↥U →ᵇ ℂ`; completeness comes from
  closedness of the holomorphic subspace under `analyticOn_of_tendstoLocallyUniformlyOn`.
-/
import Jacobians.Dolbeault.CechFiniteness

open Metric Topology BoundedContinuousFunction
open Jacobians.Montel

namespace Jacobians.Dolbeault

variable {U : Set ℂ}

/-! ### The carrier submodule -/

/-- The `ℂ`-submodule of `ℂ → ℂ` consisting of functions analytic on `U`, vanishing off `U`, and
bounded on `U`. The "vanishing off `U`" clause is a canonical normal form: it does not affect the
analytic/bounded content (which only sees `U`) but makes the sup-`U` seminorm definite and the
embedding into `↥U →ᵇ ℂ` injective. -/
def BddHolCarrier (U : Set ℂ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {g | AnalyticOn ℂ g U ∧ (∀ z ∉ U, g z = 0) ∧ ∃ C, ∀ z ∈ U, ‖g z‖ ≤ C}
  add_mem' := by
    rintro f g ⟨hfa, hf0, Cf, hfb⟩ ⟨hga, hg0, Cg, hgb⟩
    refine ⟨hfa.add hga, fun z hz => ?_, Cf + Cg, fun z hz => ?_⟩
    · rw [Pi.add_apply, hf0 z hz, hg0 z hz, add_zero]
    · calc ‖(f + g) z‖ = ‖f z + g z‖ := rfl
        _ ≤ ‖f z‖ + ‖g z‖ := norm_add_le _ _
        _ ≤ Cf + Cg := add_le_add (hfb z hz) (hgb z hz)
  zero_mem' := ⟨analyticOn_const, fun _ _ => rfl, 0, fun z _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hfa, hf0, Cf, hfb⟩
    refine ⟨?_, fun z hz => ?_, ‖c‖ * Cf, fun z hz => ?_⟩
    · exact (analyticOn_const (v := c)).smul hfa
    · rw [Pi.smul_apply, hf0 z hz, smul_zero]
    · calc ‖(c • f) z‖ = ‖c‖ * ‖f z‖ := by rw [Pi.smul_apply, norm_smul]
        _ ≤ ‖c‖ * Cf := by gcongr; exact hfb z hz

/-- The Banach space of bounded holomorphic functions on the open set `U ⊆ ℂ`.

Implemented as the subtype `↥(BddHolCarrier U)`, but kept *opaque* (non-`reducible`) so that the
ambient subtype `UniformSpace`/`TopologicalSpace` instances do not leak and clash with the
sup-`U`-norm `NormedAddCommGroup` we install below. -/
def BddHol (U : Set ℂ) : Type := ↥(BddHolCarrier U)

namespace BddHol

noncomputable instance : AddCommGroup (BddHol U) :=
  inferInstanceAs (AddCommGroup ↥(BddHolCarrier U))
noncomputable instance : Module ℂ (BddHol U) := inferInstanceAs (Module ℂ ↥(BddHolCarrier U))

/-- Reinterpret `f : BddHol U` as the underlying subtype element. Definitional identity. -/
def toCarrier (f : BddHol U) : ↥(BddHolCarrier U) := f

@[simp] theorem toCarrier_add (f g : BddHol U) : (f + g).toCarrier = f.toCarrier + g.toCarrier := rfl
@[simp] theorem toCarrier_smul (c : ℂ) (f : BddHol U) : (c • f).toCarrier = c • f.toCarrier := rfl

/-- The underlying `ℂ → ℂ` function of an element of `BddHol U`. -/
def toFun (f : BddHol U) : ℂ → ℂ := (f.toCarrier : ℂ → ℂ)

@[simp] theorem toFun_coe (f : BddHol U) : f.toFun = (f.toCarrier : ℂ → ℂ) := rfl

theorem analyticOn (f : BddHol U) : AnalyticOn ℂ f.toFun U := f.toCarrier.2.1

theorem zero_off (f : BddHol U) : ∀ z ∉ U, f.toFun z = 0 := f.toCarrier.2.2.1

theorem bddOn (f : BddHol U) : ∃ C, ∀ z ∈ U, ‖f.toFun z‖ ≤ C := f.toCarrier.2.2.2

@[simp] theorem toFun_add (f g : BddHol U) : (f + g).toFun = f.toFun + g.toFun := rfl
@[simp] theorem toFun_smul (c : ℂ) (f : BddHol U) : (c • f).toFun = c • f.toFun := rfl
@[simp] theorem toFun_zero : (0 : BddHol U).toFun = 0 := rfl

theorem toFun_injective : Function.Injective (toFun : BddHol U → (ℂ → ℂ)) :=
  fun _ _ h => Subtype.ext h

/-! ### The isometric embedding into `↥U →ᵇ ℂ` and the induced norm

An element of `BddHol U`, restricted to the subtype `↥U`, is a bounded continuous function. The
embedding `f ↦ U.restrict f.toFun` is `ℂ`-linear and injective (thanks to the vanishing-off-`U`
normal form), so it induces a `NormedAddCommGroup`/`NormedSpace` on `BddHol U`, with norm
`‖f‖ = ⨆ z : ↥U, ‖f z‖` (the bcf sup norm). Completeness then follows from closedness of the
holomorphic subspace in the Banach space `↥U →ᵇ ℂ`. -/

/-- The restriction of `f : BddHol U` to `↥U`, as a bounded continuous function. -/
noncomputable def toBcf (f : BddHol U) : ↥U →ᵇ ℂ :=
  ⟨⟨fun z => f.toFun z.1, f.analyticOn.continuousOn.restrict⟩,
    2 * f.bddOn.choose, fun x y => by
      have hC := f.bddOn.choose_spec
      calc dist (f.toFun x.1) (f.toFun y.1) ≤ ‖f.toFun x.1‖ + ‖f.toFun y.1‖ :=
            dist_le_norm_add_norm _ _
        _ ≤ f.bddOn.choose + f.bddOn.choose := add_le_add (hC x.1 x.2) (hC y.1 y.2)
        _ = 2 * f.bddOn.choose := by ring⟩

@[simp] theorem toBcf_apply (f : BddHol U) (z : ↥U) : f.toBcf z = f.toFun z.1 := rfl

/-- The bcf embedding as a `ℂ`-linear map. -/
noncomputable def toBcfₗ : BddHol U →ₗ[ℂ] (↥U →ᵇ ℂ) where
  toFun := toBcf
  map_add' f g := by
    ext z
    show (f + g).toFun z.1 = f.toFun z.1 + g.toFun z.1
    rw [toFun_add]; rfl
  map_smul' c f := by
    ext z
    show (c • f).toFun z.1 = c • f.toFun z.1
    rw [toFun_smul]; rfl

@[simp] theorem toBcfₗ_apply (f : BddHol U) : toBcfₗ f = f.toBcf := rfl

theorem toBcf_injective : Function.Injective (toBcf : BddHol U → (↥U →ᵇ ℂ)) := by
  intro f g h
  apply toFun_injective
  funext z
  by_cases hz : z ∈ U
  · have := congrArg (fun φ => φ (⟨z, hz⟩ : ↥U)) h
    simpa [toBcf_apply] using this
  · rw [f.zero_off z hz, g.zero_off z hz]

/-- The `NormedAddCommGroup` on `BddHol U` induced by the bcf embedding: `‖f‖ = ‖f.toBcf‖`. -/
noncomputable instance : NormedAddCommGroup (BddHol U) :=
  NormedAddCommGroup.induced (BddHol U) (↥U →ᵇ ℂ) toBcfₗ toBcf_injective

/-- `BddHol U` is a normed `ℂ`-space (induced from the bcf embedding). -/
noncomputable instance : NormedSpace ℂ (BddHol U) :=
  NormedSpace.induced ℂ (BddHol U) (↥U →ᵇ ℂ) toBcfₗ

theorem norm_def (f : BddHol U) : ‖f‖ = ‖f.toBcf‖ := rfl

theorem norm_eq_iSup (f : BddHol U) : ‖f‖ = ⨆ z : ↥U, ‖f.toFun z.1‖ := by
  rw [norm_def, BoundedContinuousFunction.norm_eq_iSup_norm]
  rfl

/-! ### Completeness

`toBcf` is an isometry into the Banach space `↥U →ᵇ ℂ`; `BddHol U` is therefore complete once we
know its image is closed. Closedness uses that a uniform limit of functions analytic on `U` is
analytic on `U` (`analyticOn_of_tendstoLocallyUniformlyOn`). -/

theorem toBcf_sub (f g : BddHol U) : (f - g).toBcf = f.toBcf - g.toBcf :=
  map_sub toBcfₗ f g

theorem isometry_toBcf : Isometry (toBcf : BddHol U → (↥U →ᵇ ℂ)) := by
  rw [isometry_iff_dist_eq]
  intro f g
  rw [dist_eq_norm, dist_eq_norm, norm_def, ← toBcf_sub]

theorem isUniformInducing_toBcf : IsUniformInducing (toBcf : BddHol U → (↥U →ᵇ ℂ)) :=
  isometry_toBcf.isUniformInducing

end BddHol

end Jacobians.Dolbeault
