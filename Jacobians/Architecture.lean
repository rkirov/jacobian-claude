import Jacobians.ZLatticeQuotient
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Geometry.Manifold.ContMDiff.Defs

/-!
# Architecture de-risk: pushforward / pullback / degree on a period-lattice Jacobian

Axiomatizes the ambient linear maps that induce pushforward and pullback
on the Jacobian-as-quotient, and proves that the functorial identities
(*esp.* `pushforward ∘ pullback = deg • id`) *descend* cleanly from the
ambient to the quotient.

If this compiles, the period-lattice encoding of `Jacobian X` can support
the challenge's headline identity — content becomes plug-in.
-/

namespace Jacobians.Architecture

noncomputable section

/-- The descended pushforward map on Jacobian quotients, from a
lattice-respecting ambient linear map. -/
def pushforward {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) (ΛY : Submodule ℤ (Fin gY → ℂ))
    (Φ : (Fin gX → ℂ) →L[ℝ] (Fin gY → ℂ))
    (hΦ : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ.toAddMonoidHom) :
    ((Fin gX → ℂ) ⧸ ΛX.toAddSubgroup) →ₜ+ ((Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) where
  toFun := QuotientAddGroup.map _ _ Φ.toAddMonoidHom hΦ
  map_zero' := (QuotientAddGroup.map _ _ Φ.toAddMonoidHom hΦ).map_zero
  map_add' := (QuotientAddGroup.map _ _ Φ.toAddMonoidHom hΦ).map_add
  continuous_toFun :=
    continuous_quot_lift _ (QuotientAddGroup.continuous_mk.comp Φ.continuous)

/-- The descended pullback map on Jacobian quotients. -/
def pullback {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) (ΛY : Submodule ℤ (Fin gY → ℂ))
    (Ψ : (Fin gY → ℂ) →L[ℝ] (Fin gX → ℂ))
    (hΨ : ΛY.toAddSubgroup ≤ ΛX.toAddSubgroup.comap Ψ.toAddMonoidHom) :
    ((Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) →ₜ+ ((Fin gX → ℂ) ⧸ ΛX.toAddSubgroup) :=
  pushforward ΛY ΛX Ψ hΨ

/-! ### Degree identity on the quotient, descended from the ambient. -/

/-- Headline: if `Φ ∘ Ψ = d • id` on the ambient, then the same holds for
the descended pushforward ∘ pullback on the quotient. -/
theorem pushforward_pullback_of_ambient
    {gX gY : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) (ΛY : Submodule ℤ (Fin gY → ℂ))
    (Φ : (Fin gX → ℂ) →L[ℝ] (Fin gY → ℂ))
    (Ψ : (Fin gY → ℂ) →L[ℝ] (Fin gX → ℂ))
    (hΦ : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ.toAddMonoidHom)
    (hΨ : ΛY.toAddSubgroup ≤ ΛX.toAddSubgroup.comap Ψ.toAddMonoidHom)
    (d : ℕ)
    (hΦΨ : ∀ y : (Fin gY → ℂ), Φ (Ψ y) = (d : ℕ) • y)
    (P : (Fin gY → ℂ) ⧸ ΛY.toAddSubgroup) :
    pushforward ΛX ΛY Φ hΦ (pullback ΛX ΛY Ψ hΨ P) = d • P := by
  induction P using QuotientAddGroup.induction_on with
  | H y =>
    show (QuotientAddGroup.mk (Φ (Ψ y)) : _) = d • (QuotientAddGroup.mk y : _)
    rw [hΦΨ y]
    simp

/-! ### Functoriality (identity case). -/

/-- If the ambient `Φ` is the identity, descended pushforward is identity. -/
theorem pushforward_id_of_ambient
    {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (Φ : (Fin g → ℂ) →L[ℝ] (Fin g → ℂ))
    (hΦΛ : Λ.toAddSubgroup ≤ Λ.toAddSubgroup.comap Φ.toAddMonoidHom)
    (hΦid : ∀ x : (Fin g → ℂ), Φ x = x)
    (P : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) :
    pushforward Λ Λ Φ hΦΛ P = P := by
  induction P using QuotientAddGroup.induction_on with
  | H x =>
    show (QuotientAddGroup.mk (Φ x) : _) = _
    rw [hΦid]

/-! ### Functoriality (composition case). -/

/-- Composition: the ambient composition induces the composed pushforward. -/
theorem pushforward_comp_of_ambient
    {gX gY gZ : ℕ}
    (ΛX : Submodule ℤ (Fin gX → ℂ)) (ΛY : Submodule ℤ (Fin gY → ℂ))
    (ΛZ : Submodule ℤ (Fin gZ → ℂ))
    (Φ₁ : (Fin gX → ℂ) →L[ℝ] (Fin gY → ℂ))
    (Φ₂ : (Fin gY → ℂ) →L[ℝ] (Fin gZ → ℂ))
    (hΦ₁ : ΛX.toAddSubgroup ≤ ΛY.toAddSubgroup.comap Φ₁.toAddMonoidHom)
    (hΦ₂ : ΛY.toAddSubgroup ≤ ΛZ.toAddSubgroup.comap Φ₂.toAddMonoidHom)
    (hΦ₁₂ : ΛX.toAddSubgroup ≤ ΛZ.toAddSubgroup.comap (Φ₂.comp Φ₁).toAddMonoidHom)
    (P : (Fin gX → ℂ) ⧸ ΛX.toAddSubgroup) :
    pushforward ΛX ΛZ (Φ₂.comp Φ₁) hΦ₁₂ P =
      pushforward ΛY ΛZ Φ₂ hΦ₂ (pushforward ΛX ΛY Φ₁ hΦ₁ P) := by
  induction P using QuotientAddGroup.induction_on with
  | H x => rfl

end

end Jacobians.Architecture
