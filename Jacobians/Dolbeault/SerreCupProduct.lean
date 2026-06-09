/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.CechH0

/-!
# Forster §17.5 — the cup product `L(K−D) × H¹(𝒪_D) → H¹(𝒪_K)` (the residue-pairing's product)

This is the cochain-level **cup product** that the Forster §17.5 residue pairing
`⟨f, ξ⟩ = Res((f·ω₀)·ξ)` rests on, phrased after the Forster §17.4 isomorphism `ω₀· : 𝒪_K ≅ Ω`
(`Jacobians.Dolbeault.CanonicalFormIso`): under `α ↦ α/ω₀`, a *holomorphic* 1-form is exactly a
function with poles bounded by the canonical divisor `K = div ω₀`, so the holomorphic-1-form sheaf
`Ω` is identified with the structure sheaf `𝒪_K`, and **`H¹(X,Ω) ≅ 𝔘.cechH1 K`** — the *already-built*
structure-sheaf Čech `H¹`. The cup product `(f·ω₀)·ξ ↦ ((f·ω₀)·ξ)/ω₀ = f·ξ` then reduces to plain
multiplication of the function cocycle `ξ` by the global meromorphic function `f`:

  `cup f : 𝔘.cechH1 D → 𝔘.cechH1 K`,  `[ξ] ↦ [f·ξ]`,  for `f ∈ L(K−D)`.

The poles cancel exactly: `f ∈ L(K−D)` (`div f ≥ D−K`) times a `𝒪_D` germ (`div ξ ≥ −D`) lands in
`𝒪_K` (`div(f·ξ) ≥ (D−K)+(−D) = −K`), via the order additivity `meromorphicOrderAt_mul`. This is the
mechanical, sound part of the §17.5 descent (`MGerm` is a `Filter.Germ` `CommRing`, so germ
multiplication and its ℂ-linearity are available, and germ restriction is a ring hom, so multiplying
by `f` commutes with the Čech differential and preserves cocycles/coboundaries).

## What is built here (sorry-free, axiom-clean)

* `mulConstG f U` — left-multiplication of `MGerm U` by the germ of a *global* meromorphic function
  `f` on `↥U`, as an ℂ-linear map `MGerm U →ₗ[ℂ] MGerm U`.
* `mulConstG_omegaDGerm` — multiplying a `𝒪_D` germ by `f ∈ L(K−D)` lands in `𝒪_K` (order additivity).
* `cupCochain1 f` — the induced map on 1-cochains, commuting with `rawRestrictG` and `cechDelta1`.
* `cupCocycles1 f`, `cupCoboundaries1 f` — it maps `𝒪_D`-cocycles to `𝒪_K`-cocycles and
  `𝒪_D`-coboundaries to `𝒪_K`-coboundaries (so it descends to cohomology).
* `cupH1 f : 𝔘.cechH1 D →ₗ[ℂ] 𝔘.cechH1 K` — the descended cup product on cohomology classes.
* `cup f D : lSysModule (K − D) →ₗ[ℂ] (𝔘.cechH1 D →ₗ[ℂ] 𝔘.cechH1 K)` — ℂ-linearity in `f` too (the
  junk-free `lSysModule` source), bundled as a bilinear map; the input to the §17.5 residue pairing.

The remaining §17.5 piece — the global residue `Res : 𝔘.cechH1 K → ℂ` (Forster 17.3, via the
Mittag–Leffler connecting map, the genuinely-greenfield analytic descent) — is built separately; this
file supplies its cup-product argument. See `docs/serre_17_build_plan.md`, `SerreResiduePairing.lean`.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.4 (`ω₀· : 𝒪_K ≅ Ω`), §17.5 (pairing).
-/

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 1 — ℂ-linear multiplication of germ-classes by a fixed germ -/

/-- Multiplication of `MGerm U` by a fixed germ `a : MGerm U`, as an ℂ-linear map.  (`MGerm U` is a
`Filter.Germ` `CommRing`; multiplication is `ℂ`-bilinear because the scalar action `c • g` is the
pointwise `(c • ·)` — definitionally `↑(c • g)` — so `c • (a*b) = (c•a)*b`.) -/
noncomputable def mulLeftG {U : Opens X} (a : MGerm U) : MGerm U →ₗ[ℂ] MGerm U where
  toFun g := a * g
  map_add' g₁ g₂ := mul_add a g₁ g₂
  map_smul' c g := by
    induction a using Filter.Germ.inductionOn with | _ a =>
    induction g using Filter.Germ.inductionOn with | _ g =>
    show (↑(a * (c • g)) : MGerm U) = c • (↑(a * g) : MGerm U)
    rw [show c • (↑(a * g) : MGerm U) = (↑(c • (a * g)) : MGerm U) from rfl]
    congr 1; funext x; simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring

@[simp] theorem mulLeftG_apply {U : Opens X} (a g : MGerm U) : mulLeftG a g = a * g := rfl

/-- Germ restriction is a ring hom (`rawRestrictG (a*b) = rawRestrictG a * rawRestrictG b`): both
sides are the germ of the pointwise product precomposed with the open inclusion. -/
theorem rawRestrictG_mul {U V : Opens X} (h : V ≤ U) (a b : MGerm U) :
    rawRestrictG h (a * b) = rawRestrictG h a * rawRestrictG h b := by
  induction a using Filter.Germ.inductionOn with | _ a =>
  induction b using Filter.Germ.inductionOn with | _ b =>
  rfl

/-! ## Part 2 — the germ of a global meromorphic function on `↥U`, and the `𝒪_D → 𝒪_K` order law -/

/-- The germ-class on `↥U` of (the restriction of) a *global* meromorphic function `F`.  This is the
function-side avatar of `f·ω₀` after dividing by `ω₀`: the cup product multiplies a `𝒪_D` cochain by
this germ. -/
noncomputable def globalGerm (F : MeromorphicFunction X) (U : Opens X) : MGerm U :=
  toGerm U (F.toFun ∘ Subtype.val)

/-- Restriction of the global germ to a smaller open is the global germ there (`F` is the same global
function; restriction is precomposition with the open inclusion, and `(F∘val) ∘ openIncl = F∘val`). -/
theorem rawRestrictG_globalGerm (F : MeromorphicFunction X) {U V : Opens X} (h : V ≤ U) :
    rawRestrictG h (globalGerm F U) = globalGerm F V := by
  rw [globalGerm, rawRestrictG_coe]; rfl

/-- The order on `↥U` of `(F∘val)·g` is `orderW F` (corresponding point) plus the order of `g`.  The
key order-additivity (`meromorphicOrderAt_mul`) behind the poles-cancellation of the cup product. -/
theorem ordU_globalMul {U : Opens X} (F : MeromorphicFunction X) {g : U → ℂ}
    (hg : IsMeromorphic (U : Type _) g) (x : U) :
    ordU ((F.toFun ∘ Subtype.val) * g) x = F.orderW x.1 + ordU g x := by
  -- `ordU ((F∘val)·g) = meromorphicOrderAt (((F∘val)·g)∘chart.symm)`; the pullback factors as a
  -- product of the two chart pullbacks, so `meromorphicOrderAt_mul` applies, and the `F`-factor's
  -- order is `orderW F x.1` by the keystone `ordU_val_eq_orderW`.
  have hFmer : IsMeromorphic (U : Type _) (F.toFun ∘ Subtype.val) := isMeromorphic_val F
  have hsplit : (((F.toFun ∘ Subtype.val) * g) ∘ (chartAt (H := ℂ) x).symm)
      = ((F.toFun ∘ Subtype.val) ∘ (chartAt (H := ℂ) x).symm)
        * (g ∘ (chartAt (H := ℂ) x).symm) := by
    funext z; simp [Pi.mul_apply]
  rw [ordU, hsplit, meromorphicOrderAt_mul (hFmer x) (hg x)]
  congr 1
  rw [show meromorphicOrderAt ((F.toFun ∘ Subtype.val) ∘ (chartAt (H := ℂ) x).symm)
      ((chartAt (H := ℂ) x) x) = ordU (F.toFun ∘ Subtype.val) x from rfl]
  exact ordU_val_eq_orderW F x

/-- **Multiplying a `𝒪_D` germ by `f ∈ L(K−D)` lands in `𝒪_K`** (poles cancel).  If `f ∈ L(K−D)`
(`div f ≥ D−K`) and `s ∈ 𝒪_D(U)` (`div s ≥ −D`), then `f·s ∈ 𝒪_K(U)` (`div(f·s) ≥ −K`): the order
adds (`ordU_globalMul`), and `−(K x) ≤ orderW f x + ordU s` from `−((K−D) x) ≤ orderW f x` and
`−(D x) ≤ ordU s`. -/
theorem mulConstG_omegaDGerm {D K : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (K - D)) {U : Opens X} {s : MGerm U}
    (hs : s ∈ OmegaDGerm D U) :
    globalGerm f U * s ∈ OmegaDGerm K U := by
  -- represent `s` by an honest function `g ∈ 𝒪_D(U)`.
  obtain ⟨g, hgmem, hgs⟩ := hs
  refine ⟨(f.toFun ∘ Subtype.val) * g, ?_, ?_⟩
  · -- `(F∘val)·g ∈ 𝒪_K(U)`.
    refine ⟨fun u => ((isMeromorphic_val f) u).mul (hgmem.1 u), fun x => ?_⟩
    rw [ordU_globalMul f hgmem.1 x]
    -- `−(K x) ≤ orderW f x + ordU g x`.
    have h1 : (-((K - D) x.1) : WithTop ℤ) ≤ f.orderW x.1 := hf x.1
    have h2 : (-(D x.1) : WithTop ℤ) ≤ ordU g x := hgmem.2 x
    have hsum : (-((K - D) x.1) : WithTop ℤ) + (-(D x.1) : WithTop ℤ)
        ≤ f.orderW x.1 + ordU g x := add_le_add h1 h2
    have heq : (-(K x.1) : WithTop ℤ) = (-((K - D) x.1) : WithTop ℤ) + (-(D x.1) : WithTop ℤ) := by
      rw [Finsupp.sub_apply]; norm_cast; ring
    rw [heq]; exact hsum
  · -- `toGerm ((F∘val)·g) = globalGerm f U * s`.
    rw [globalGerm, ← hgs]
    rfl

/-! ## Part 3 — the cochain-level cup product and its commutation with the Čech differentials

`cupCochain0 f` / `cupCochain1 f` multiply each component of a cochain by the global germ of `f` on
that open.  Because germ restriction is a ring hom (`rawRestrictG_mul`) and `globalGerm f` restricts to
`globalGerm f` (`rawRestrictG_globalGerm`), these commute with `cechDelta0` and `cechDelta1`. -/

variable (𝔘 : FiniteFamily X)

/-- Multiply each component of a 0-cochain by the global germ of `f` on `U_i`. -/
noncomputable def cupCochain0 (f : MeromorphicFunction X) : 𝔘.Cochain0 →ₗ[ℂ] 𝔘.Cochain0 :=
  LinearMap.pi fun i => mulLeftG (globalGerm f (𝔘.U i)) ∘ₗ LinearMap.proj i

/-- Multiply each component of a 1-cochain by the global germ of `f` on `U_i ∩ U_j`. -/
noncomputable def cupCochain1 (f : MeromorphicFunction X) : 𝔘.Cochain1 →ₗ[ℂ] 𝔘.Cochain1 :=
  LinearMap.pi fun p => mulLeftG (globalGerm f (𝔘.U p.1 ⊓ 𝔘.U p.2)) ∘ₗ LinearMap.proj p

/-- Multiply each component of a 2-cochain by the global germ of `f` on the triple intersection. -/
noncomputable def cupCochain2 (f : MeromorphicFunction X) : 𝔘.Cochain2 →ₗ[ℂ] 𝔘.Cochain2 :=
  LinearMap.pi fun t => mulLeftG (globalGerm f (𝔘.U t.1 ⊓ 𝔘.U t.2.1 ⊓ 𝔘.U t.2.2)) ∘ₗ LinearMap.proj t

@[simp] theorem cupCochain0_apply (f : MeromorphicFunction X) (c : 𝔘.Cochain0) (i : 𝔘.ι) :
    cupCochain0 𝔘 f c i = globalGerm f (𝔘.U i) * c i := rfl

@[simp] theorem cupCochain1_apply (f : MeromorphicFunction X) (c : 𝔘.Cochain1) (p : 𝔘.ι × 𝔘.ι) :
    cupCochain1 𝔘 f c p = globalGerm f (𝔘.U p.1 ⊓ 𝔘.U p.2) * c p := rfl

@[simp] theorem cupCochain2_apply (f : MeromorphicFunction X) (c : 𝔘.Cochain2)
    (t : 𝔘.ι × 𝔘.ι × 𝔘.ι) :
    cupCochain2 𝔘 f c t = globalGerm f (𝔘.U t.1 ⊓ 𝔘.U t.2.1 ⊓ 𝔘.U t.2.2) * c t := rfl

/-- **Multiplying by `f` commutes with `δ⁰`** (`cup ∘ δ⁰ = δ⁰ ∘ cup`).  On each pair `(i,j)`, both
sides equal `globalGerm f (U_i∩U_j) · (g_j|_{ij} − g_i|_{ij})` — germ restriction is a ring hom and
`globalGerm f` restricts to `globalGerm f`. -/
theorem cupCochain1_comp_cechDelta0 (f : MeromorphicFunction X) :
    (cupCochain1 𝔘 f) ∘ₗ 𝔘.cechDelta0 = 𝔘.cechDelta0 ∘ₗ (cupCochain0 𝔘 f) := by
  refine LinearMap.ext fun c => ?_
  funext p
  obtain ⟨i, j⟩ := p
  simp only [LinearMap.comp_apply, cupCochain1_apply, FiniteFamily.cechDelta0, LinearMap.pi_apply,
    LinearMap.sub_apply, LinearMap.proj_apply, cupCochain0_apply, mul_sub,
    rawRestrictG_mul, rawRestrictG_globalGerm]

/-- **Multiplying by `f` commutes with `δ¹`** (`cup ∘ δ¹ = δ¹ ∘ cup`).  Termwise: germ restriction is
a ring hom, and `globalGerm f` restricts to `globalGerm f`, so the three alternating terms each carry
the `f`-factor through. -/
theorem cupCochain2_comp_cechDelta1 (f : MeromorphicFunction X) :
    (cupCochain2 𝔘 f) ∘ₗ 𝔘.cechDelta1 = 𝔘.cechDelta1 ∘ₗ (cupCochain1 𝔘 f) := by
  refine LinearMap.ext fun c => ?_
  funext t
  obtain ⟨i, j, k⟩ := t
  simp only [LinearMap.comp_apply, cupCochain2_apply, FiniteFamily.cechDelta1, LinearMap.pi_apply,
    LinearMap.add_apply, LinearMap.sub_apply, LinearMap.proj_apply,
    cupCochain1_apply, mul_add, mul_sub, rawRestrictG_mul, rawRestrictG_globalGerm]

/-! ## Part 4 — the cup product preserves the `𝒪_D → 𝒪_K` sheaf condition, cocycles, coboundaries -/

variable {𝔘}

/-- Multiplying a 0-cochain of `𝒪_D`-sections by `f ∈ L(K−D)` gives a 0-cochain of `𝒪_K`-sections. -/
theorem cupCochain0_sections0 {D K : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (K - D)) {c : 𝔘.Cochain0} (hc : c ∈ 𝔘.sections0 D) :
    cupCochain0 𝔘 f c ∈ 𝔘.sections0 K :=
  fun i => mulConstG_omegaDGerm hf (hc i)

/-- Multiplying a 1-cochain of `𝒪_D`-sections by `f ∈ L(K−D)` gives a 1-cochain of `𝒪_K`-sections. -/
theorem cupCochain1_sections1 {D K : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (K - D)) {c : 𝔘.Cochain1} (hc : c ∈ 𝔘.sections1 D) :
    cupCochain1 𝔘 f c ∈ 𝔘.sections1 K :=
  fun p => mulConstG_omegaDGerm hf (hc p)

/-- The cup product maps `𝒪_D`-cocycles to `𝒪_K`-cocycles: it preserves `ker δ¹` (commutation
`cup₂ ∘ δ¹ = δ¹ ∘ cup₁`) and the sheaf condition (`cupCochain1_sections1`). -/
theorem cupCochain1_cocycles1 {D K : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (K - D)) {c : 𝔘.Cochain1} (hc : c ∈ 𝔘.cocycles1 D) :
    cupCochain1 𝔘 f c ∈ 𝔘.cocycles1 K := by
  obtain ⟨hker, hsec⟩ := hc
  refine ⟨?_, cupCochain1_sections1 hf hsec⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker] at hker ⊢
  have hcomm := LinearMap.congr_fun (cupCochain2_comp_cechDelta1 𝔘 f) c
  simp only [LinearMap.comp_apply] at hcomm
  rw [← hcomm, hker, map_zero]

/-- The cup product maps `𝒪_D`-coboundaries to `𝒪_K`-coboundaries: `cup₁(δ⁰ s) = δ⁰(cup₀ s)`
(commutation) and `cup₀ s` is a `𝒪_K`-section (`cupCochain0_sections0`). -/
theorem cupCochain1_coboundaries1 {D K : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (K - D)) {c : 𝔘.Cochain1} (hc : c ∈ 𝔘.coboundaries1 D) :
    cupCochain1 𝔘 f c ∈ 𝔘.coboundaries1 K := by
  obtain ⟨s, hs, rfl⟩ := hc
  refine ⟨cupCochain0 𝔘 f s, cupCochain0_sections0 hf hs, ?_⟩
  have hcomm := LinearMap.congr_fun (cupCochain1_comp_cechDelta0 𝔘 f) s
  simp only [LinearMap.comp_apply] at hcomm
  exact hcomm.symm

/-! ## Part 5 — the descended cup product on cohomology `cupH1 f : cechH1 D →ₗ cechH1 K` -/

/-- The cup product as a linear map of cocycle submodules `cocycles1 D → cocycles1 K` (the restriction
of `cupCochain1 f`). -/
noncomputable def cupCocyclesMap {D K : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (K - D)) :
    ↥(𝔘.cocycles1 D) →ₗ[ℂ] ↥(𝔘.cocycles1 K) :=
  (cupCochain1 𝔘 f).restrict (fun _ hc => cupCochain1_cocycles1 hf hc)

@[simp] theorem cupCocyclesMap_coe {D K : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (K - D)) (c : ↥(𝔘.cocycles1 D)) :
    (cupCocyclesMap hf c : 𝔘.Cochain1) = cupCochain1 𝔘 f c := rfl

/-- **The descended cup product on cohomology** `[ξ] ↦ [f·ξ]`, `cechH1 D →ₗ[ℂ] cechH1 K`.  Well-defined
because the cup product maps `cocycles1 D → cocycles1 K` (`cupCochain1_cocycles1`) and
`coboundaries1 D → coboundaries1 K` (`cupCochain1_coboundaries1`), so it descends through the
`Z¹/B¹` quotient (`Submodule.mapQ`). -/
noncomputable def cupH1 {D K : Divisor X} {f : MeromorphicFunction X}
    (hf : f ∈ linearSystem (X := X) (K - D)) :
    𝔘.cechH1 D →ₗ[ℂ] 𝔘.cechH1 K :=
  Submodule.mapQ _ _ (cupCocyclesMap hf) (by
    -- the cocycle map sends `B¹(D)` (as a submodule of `Z¹(D)`) into `B¹(K)` (as a submodule of `Z¹(K)`).
    intro c hc
    rw [Submodule.mem_comap]
    -- `c ∈ (coboundaries1 D).submoduleOf (cocycles1 D)` means `c.1 ∈ coboundaries1 D`.
    rw [Submodule.submoduleOf, Submodule.mem_comap] at hc
    rw [Submodule.submoduleOf, Submodule.mem_comap]
    exact cupCochain1_coboundaries1 hf hc)

end Jacobians.Dolbeault
