/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Serre duality for the tail `H¹`, the surjectivity assembly (Miranda Thm 3.3, pp. 189–191)

The pigeonhole half of Serre duality, Forster 17.9's count on Miranda's tail spaces.  Given
`0 ≠ φ : H¹(D)* `, fix a base point `P` and compare, inside `V_n := H¹(D − nP)*`, the two
subspaces

* `Λ_n` — the functionals `φ ∘ T̄_ψ` for `ψ ∈ L(nP)` (the multiplication action of
  `TailMultiplicationH1`); `Λ_n ≅ L(nP)/germ0` since `φ ∘ T̄_ψ ≠ 0` for surviving `ψ`
  (`comp_tailMulH1_ne_zero`), so `dim Λ_n ≥ n + 1 − h¹(0)` by RR-I;
* `I_n` — the residue functionals `Res_{h·ω₀}`, `h ∈ L(K − (D − nP))` (the range of
  `omegaDualMap` at `D − nP`); `dim I_n = l(K − D + nP) ≥ deg K − deg D + n + 1 − h¹(0)` by RR-I.

For `n > deg D` RR-I pins `dim V_n = n − deg D − 1 + h¹(0)` (negative degree kills `l`), so for
`n` large the two subspaces meet in a nonzero functional `φ ∘ T̄_ψ = Res_{h·ω₀}`.  The recovery
step (Miranda pp. 190–191) then pulls `φ` back along `μ_{ψ⁻¹}`: the composite identity turns
`T̄_ψ ∘ μ̄_{ψ⁻¹}` into the truncation, W1 turns `Res_{h·ω₀} ∘ μ_{ψ⁻¹}` into `Res_{(ψ⁻¹h)·ω₀}`,
and Miranda Lemma 3.6 (`omegaOrderBounded_of_vanishing`) downgrades the order bound of
`ψ⁻¹h` from the fine level to `D` — exhibiting `φ = Res_{(ψ⁻¹h)·ω₀}` with `ψ⁻¹h ∈ L(K − D)`.

Headlines: `omegaDualMap_surjective` and the dimension identity
`h1TailDim_eq_lDim_canonical_sub : h¹(D) = l(K − D)`.
-/
import Jacobians.LaurentTail.TailDualitySurjective
import Jacobians.RiemannRoch

open scoped Manifold ContDiff Topology
open Filter Set Module
open Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace

set_option linter.unusedSectionVars false

namespace Jacobians.LaurentTail

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §1 The multiplication operator is linear in the multiplier -/

/-- `μ_ψ(Z)` is **additive in the multiplier** `ψ`: the Laurent coefficients of
`(ψ₁ + ψ₂)·(tail polynomial)` split (`laurentCoeff_add`). -/
theorem tailMul_add_multiplier (ψ₁ ψ₂ : MeromorphicFunction X) (E : Divisor X)
    (Z : TailSpace X) :
    tailMul (ψ₁ + ψ₂) E Z = tailMul ψ₁ E Z + tailMul ψ₂ E Z := by
  classical
  ext q
  rw [Finsupp.add_apply, tailMul_apply, tailMul_apply, tailMul_apply]
  split_ifs with hlt
  · have hfun : (fun z => (ψ₁ + ψ₂).toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
        = (fun z => ψ₁.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
          + (fun z => ψ₂.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z) := by
      funext z
      show (ψ₁ + ψ₂).toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z
        = ψ₁.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z
          + ψ₂.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z
      rw [MeromorphicFunction.add_toFun, Pi.add_apply]
      ring
    rw [hfun, laurentCoeff_add (meromorphicAt_psi_mul_tailFnAt ψ₁ Z q.1)
      (meromorphicAt_psi_mul_tailFnAt ψ₂ Z q.1)]
  · rw [add_zero]

/-- `μ_ψ(Z)` is **homogeneous in the multiplier** `ψ`. -/
theorem tailMul_smul_multiplier (a : ℂ) (ψ : MeromorphicFunction X) (E : Divisor X)
    (Z : TailSpace X) :
    tailMul (a • ψ) E Z = a • tailMul ψ E Z := by
  classical
  ext q
  rw [Finsupp.smul_apply, tailMul_apply, tailMul_apply]
  split_ifs with hlt
  · have hfun : (fun z => (a • ψ).toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
        = a • fun z => ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z := by
      funext z
      show (a • ψ).toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z
        = a * (ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
      rw [MeromorphicFunction.smul_toFun, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hfun, laurentCoeff_smul a (meromorphicAt_psi_mul_tailFnAt ψ Z q.1), smul_eq_mul]
  · rw [smul_zero]

/-- For a **germ-zero multiplier** the operator vanishes: `ψ·(tail polynomial)` is eventually `0`
on every punctured chart neighbourhood, so all its Laurent coefficients vanish. -/
theorem tailMul_eq_zero_of_germZero {ψ : MeromorphicFunction X}
    (hψ : ∀ x, ψ.orderW x = ⊤) (E : Divisor X) (Z : TailSpace X) :
    tailMul ψ E Z = 0 := by
  classical
  ext q
  rw [Finsupp.coe_zero, Pi.zero_apply, tailMul_apply]
  split_ifs with hlt
  · have h0 : (fun z => ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z)
        =ᶠ[𝓝[≠] ((chartAt (H := ℂ) q.1) q.1)] (0 : ℂ → ℂ) := by
      have hev := meromorphicOrderAt_eq_top_iff.mp (hψ q.1)
      filter_upwards [hev] with z hz
      show ψ.toFun ((chartAt (H := ℂ) q.1).symm z) * tailFnAt Z q.1 z = 0
      rw [show ψ.toFun ((chartAt (H := ℂ) q.1).symm z)
        = (ψ.toFun ∘ (chartAt (H := ℂ) q.1).symm) z from rfl, hz, zero_mul]
    rw [laurentCoeff_congr h0, laurentCoeff_zero]
  · rfl

/-! ### §2 The Λ-side dual map `ψ ↦ φ ∘ T̄_ψ` on `L(C)/germ0` -/

section LambdaSide

variable {B : Divisor X} (φ : Module.Dual ℂ (mittagLefflerH1 (X := X) B)) (C : Divisor X)

/-- The Λ-side assignment on representatives: `ψ ∈ L(C) ↦ φ ∘ T̄_ψ : H¹(B − C) → ℂ`
(`T̄_ψ : H¹(B − C) → H¹(B)` by the level condition `mulLevelLE_of_mem`).  Linear in `ψ`
because `μ_ψ` is (`tailMul_add_multiplier`/`tailMul_smul_multiplier`). -/
noncomputable def tailMulDual :
    ↥(linearSystem (X := X) C) →ₗ[ℂ] Module.Dual ℂ (mittagLefflerH1 (X := X) (B - C)) where
  toFun ψ := φ.comp (tailMulH1 (ψ : MeromorphicFunction X) (mulLevelLE_of_mem ψ.2 B))
  map_add' ψ₁ ψ₂ := by
    refine LinearMap.ext fun ξ => ?_
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    have hco : tailMulCo ((ψ₁ + ψ₂ : ↥(linearSystem (X := X) C)) : MeromorphicFunction X)
        (B - C) B Z
        = tailMulCo (ψ₁ : MeromorphicFunction X) (B - C) B Z
          + tailMulCo (ψ₂ : MeromorphicFunction X) (B - C) B Z := by
      refine Subtype.ext ?_
      simp only [AddMemClass.coe_add, tailMulCo_coe]
      exact tailMul_add_multiplier (ψ₁ : MeromorphicFunction X) (ψ₂ : MeromorphicFunction X)
        B (Z : TailSpace X)
    rw [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      tailMulH1_mk, tailMulH1_mk, tailMulH1_mk, hco, ← map_add φ, ← Submodule.Quotient.mk_add]
  map_smul' a ψ := by
    refine LinearMap.ext fun ξ => ?_
    obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
    have hco : tailMulCo ((a • ψ : ↥(linearSystem (X := X) C)) : MeromorphicFunction X)
        (B - C) B Z
        = a • tailMulCo (ψ : MeromorphicFunction X) (B - C) B Z := by
      refine Subtype.ext ?_
      simp only [SetLike.val_smul, tailMulCo_coe]
      exact tailMul_smul_multiplier a (ψ : MeromorphicFunction X) B (Z : TailSpace X)
    rw [RingHom.id_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      tailMulH1_mk, tailMulH1_mk, hco, ← map_smul φ, ← Submodule.Quotient.mk_smul]

@[simp] theorem tailMulDual_apply (ψ : ↥(linearSystem (X := X) C)) :
    tailMulDual φ C ψ
      = φ.comp (tailMulH1 (ψ : MeromorphicFunction X) (mulLevelLE_of_mem ψ.2 B)) := rfl

/-- A germ-zero multiplier is sent to the zero functional. -/
theorem tailMulDual_eq_zero_of_germZero (ψ : ↥(linearSystem (X := X) C))
    (hψ : ∀ x, (ψ : MeromorphicFunction X).orderW x = ⊤) :
    tailMulDual φ C ψ = 0 := by
  refine LinearMap.ext fun ξ => ?_
  obtain ⟨Z, rfl⟩ := Submodule.Quotient.mk_surjective _ ξ
  rw [tailMulDual_apply, LinearMap.comp_apply, tailMulH1_mk, LinearMap.zero_apply]
  have hco : tailMulCo (ψ : MeromorphicFunction X) (B - C) B Z = 0 := by
    refine Subtype.ext ?_
    rw [tailMulCo_coe, tailMul_eq_zero_of_germZero hψ B (Z : TailSpace X)]
    rfl
  rw [hco, Submodule.Quotient.mk_zero, map_zero]

/-- The Λ-side dual map **descended to the junk-free quotient** `L(C)/germ0` (the space whose
`finrank` is `lDim C`). -/
noncomputable def tailMulDualQ :
    lSysModule (X := X) C →ₗ[ℂ] Module.Dual ℂ (mittagLefflerH1 (X := X) (B - C)) :=
  Submodule.liftQ _ (tailMulDual φ C) (by
    intro ψ hψ
    rw [LinearMap.mem_ker]
    exact tailMulDual_eq_zero_of_germZero φ C ψ fun x => hψ x)

@[simp] theorem tailMulDualQ_mk (ψ : ↥(linearSystem (X := X) C)) :
    tailMulDualQ φ C (Submodule.Quotient.mk ψ) = tailMulDual φ C ψ :=
  Submodule.liftQ_apply _ _ ψ

/-- For `φ ≠ 0` the Λ-side dual map is **injective** (Forster 17.8: `φ ∘ T̄_ψ ≠ 0` whenever the
germ of `ψ` survives). -/
theorem tailMulDualQ_injective (hφ : φ ≠ 0) :
    Function.Injective (tailMulDualQ φ C) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero]
  by_contra hcon
  have hex : ∃ p : X, (ψ : MeromorphicFunction X).orderW p ≠ ⊤ := by
    by_contra hall
    push_neg at hall
    exact hcon fun x => hall x
  rw [tailMulDualQ_mk, tailMulDual_apply] at hx
  exact comp_tailMulH1_ne_zero φ hφ (ψ : MeromorphicFunction X) hex
    (mulLevelLE_of_mem ψ.2 B) hx

/-- `dim Λ = l(C)` for `φ ≠ 0`. -/
theorem finrank_range_tailMulDualQ (hφ : φ ≠ 0) :
    finrank ℂ ↥(LinearMap.range (tailMulDualQ φ C)) = lDim (X := X) C :=
  LinearMap.finrank_range_of_inj (tailMulDualQ_injective φ C hφ)

end LambdaSide

/-- `dim I = l(K − D)`: the range of the (injective) residue pairing has the dimension of its
source `L(K − D)/germ0`. -/
theorem finrank_range_omegaDualMap (ω₀ : HolomorphicOneForms X) (hω₀ : ω₀ ≠ 0)
    (D : Divisor X) :
    finrank ℂ ↥(LinearMap.range (omegaDualMap ω₀ hω₀ D))
      = lDim (X := X) (canonicalDivisorOf ω₀ hω₀ - D) :=
  LinearMap.finrank_range_of_inj (omegaDualMap_injective ω₀ hω₀ D)

end Jacobians.LaurentTail
