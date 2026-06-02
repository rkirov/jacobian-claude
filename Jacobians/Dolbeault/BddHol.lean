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

/-- The Banach space of bounded holomorphic functions on the open set `U ⊆ ℂ`. -/
@[reducible] def BddHol (U : Set ℂ) : Type := ↥(BddHolCarrier U)

namespace BddHol

/-- The underlying `ℂ → ℂ` function of an element of `BddHol U`. -/
def toFun (f : BddHol U) : ℂ → ℂ := (f : ℂ → ℂ)

@[simp] theorem toFun_coe (f : BddHol U) : f.toFun = (f : ℂ → ℂ) := rfl

theorem analyticOn (f : BddHol U) : AnalyticOn ℂ f.toFun U := f.2.1

theorem zero_off (f : BddHol U) : ∀ z ∉ U, f.toFun z = 0 := f.2.2.1

theorem bddOn (f : BddHol U) : ∃ C, ∀ z ∈ U, ‖f.toFun z‖ ≤ C := f.2.2.2

@[simp] theorem toFun_add (f g : BddHol U) : (f + g).toFun = f.toFun + g.toFun := rfl
@[simp] theorem toFun_smul (c : ℂ) (f : BddHol U) : (c • f).toFun = c • f.toFun := rfl
@[simp] theorem toFun_zero : (0 : BddHol U).toFun = 0 := rfl

theorem toFun_injective : Function.Injective (toFun : BddHol U → (ℂ → ℂ)) :=
  fun _ _ h => Subtype.ext h

end BddHol

end Jacobians.Dolbeault
