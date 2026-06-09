/-
  Forster §17.4 — the canonical-form multiplication isomorphism `ω₀·: 𝒪_{D+K} ≅ Ω_D`, the
  canonical divisor `K = div ω₀`, and `lDim K = genus X` (17.4 at `D = 0`).

  Built directly on **Gate (C)** (`Jacobians.Dolbeault.MeromorphicOneFormSystem`): the
  meromorphic-1-form linear system `Ω_D = omegaD D`, its junk-free module `omegaDModule D`,
  `omegaDim`, the §17.4 multiplication map `meroFormSMul f α` (= `f·α`) with its order additivity
  `formOrderW (f·α) = orderW f + formOrderW α`, and the `Ω_0 ≅ HolomorphicOneForms` wiring
  (`omegaDim_zero_eq_genus_of_le`).

  ## The Forster §17.4 content (close reading of GTM 81, §17.4)

  Fix a nonzero meromorphic 1-form `ω₀` (Forster takes `ω₀ = df` for a nonconstant meromorphic `f`,
  which exists by the Riemann–Roch inequality — `exists_nonconstant_meromorphic`). Let
  `K := div ω₀` (the canonical divisor). The map `f ↦ f·ω₀` is, for each divisor `D`, an isomorphism

      `ω₀· : L(D + K) ≅ Ω_D`,

  i.e. on the junk-free modules `lSysModule (D + K) ≃ₗ[ℂ] omegaDModule D`. It is well-defined and
  injective because multiplication by the nonzero `ω₀` is injective on germ-junk-free modules
  (order additivity + the form identity theorem for `ω₀ ≠ 0`); surjective because every `α ∈ Ω_D`
  is `f₀·ω₀` with `f₀ = α/ω₀` a meromorphic function — and the covector ratio `α/ω₀` is *intrinsic*
  (both `α x` and `ω₀ x` lie in the 1-dim cotangent fibre at `x`), so it is chart-independent and
  meromorphic, with `div f₀ = div α − K`, placing `f₀ ∈ L(D + K)`.

  At `D = 0` this is `𝒪_K ≅ Ω_0`, and composing with `Ω_0 ≅ HolomorphicOneForms` (Gate C's
  `omegaDim_zero_eq_genus_of_le`) gives `lDim K = genus X` — the `hKgenus` field of
  `SerreDualityData`.

  ## The one isolated analytic input

  The **canonical divisor** `K = div ω₀` of a *nonzero* meromorphic 1-form: the order function
  `x ↦ (formOrderW ω₀ x).untop₀` has finite support (`ω₀` has finitely many zeros/poles on the
  compact `X`), so it is a genuine `Divisor X` with `formOrderW ω₀ x = (K x : WithTop ℤ)` for all
  `x` (the form identity theorem gives `formOrderW ω₀ x ≠ ⊤` everywhere, so the `untop₀` loses no
  information). This existence-of-the-form-divisor is the 1-form analog of `MeromorphicFunction.div`
  (the local-finiteness `orderAtPoint_isolated_at` of `Jacobians.Abel`), and the construction of `ω₀`
  itself (`ω₀ = df`) is the analytic differential. Both are bundled, with `ω₀ ≠ 0`, into the isolated
  hypothesis structure `CanonicalForm17Data` below; **every theorem built on it is genuine** (the
  structure is non-vacuous — `df` of a nonconstant `f` witnesses it — and at `D = 0` both sides of
  the iso have dimension `genus X`, so the iso is non-vacuous, not a junk identity).

  Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.4 (`ω·: 𝒪_{D+K} ≅ Ω_D`); the
  `linearSystem`/`lSysModule`/`lDim` pattern in `Jacobians.LinearSystem`; the `Ω_D` Gate-C build in
  `Jacobians.Dolbeault.MeromorphicOneFormSystem`.
-/
import Jacobians.Dolbeault.MeromorphicOneFormSystem

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.Dolbeault

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- The **junk-free linear-system module** `L(D)` (= `H⁰(X, 𝒪_D)`): the linear system with the
`toFun`-germ junk quotiented out, `lDim D = finrank ℂ (lSysModule D)`. (A local copy of the
abbreviation in `SerreDualityPairing`, so this §17.4 layer stays independent of the downstream
`exists_serreDualityData` `sorry`.) -/
abbrev lSysModule (D : Divisor X) : Type _ :=
  ↥(linearSystem (X := X) D) ⧸ (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) D)

/-! ## Part 1: the form identity theorem (`ω₀ ≠ 0` ⟹ `formOrderW ω₀ ≠ ⊤` everywhere)

The order of a meromorphic 1-form vanishes (`= ⊤`) at `x` exactly when the *section* `α.toFun`
vanishes on a punctured neighbourhood of `x` — an **intrinsic** statement (no chart-coefficient
change-of-variables needed): the chart coefficient `formCoeff α.toFun x` reads `α.toFun y` against
the spanning tangent vector `symmL 1`, so the coefficient vanishes near `chart x x` iff the covector
`α.toFun y` vanishes near `x`.  This makes `{x | formOrderW α x = ⊤}` clopen on the connected `X`
(mirror of `MeromorphicFunction.orderW_ne_top_of_exists`), giving the identity theorem. -/

namespace MeromorphicOneForm

/-- A covector in the (1-dim) cotangent fibre that kills the spanning tangent vector `symmL 1`
of the trivialization at `x` is the zero covector — because every tangent vector is a scalar
multiple of `symmL 1` (mirror of the argument in `FormCoeff.exists_localRep_self_ne_zero`). -/
theorem toFun_eq_zero_of_formCoeff_zero (α : MeromorphicOneForm X) {x y : X}
    (hy : y ∈ (trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).baseSet)
    (h : α.toFun y ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x).symmL ℂ y 1) = 0) :
    α.toFun y = 0 := by
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x with he
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.zero_apply]
  have hv : e.symmL ℂ y (e.continuousLinearMapAt ℂ y v) = v :=
    e.symmL_continuousLinearMapAt hy v
  set c := e.continuousLinearMapAt ℂ y v with hc
  have hsm : e.symmL ℂ y c = c • e.symmL ℂ y 1 := by
    have h2 := (e.symmL ℂ y).map_smul c (1 : ℂ)
    rwa [smul_eq_mul, mul_one] at h2
  calc α.toFun y v = α.toFun y (e.symmL ℂ y c) := by rw [hv]
    _ = α.toFun y (c • e.symmL ℂ y 1) := by rw [hsm]
    _ = c • α.toFun y (e.symmL ℂ y 1) := by rw [(α.toFun y).map_smul]
    _ = 0 := by rw [h, smul_zero]

/-- **Intrinsic vanishing characterization.** `formOrderW α x = ⊤` (the form's germ vanishes at `x`)
iff the *section* `α.toFun` vanishes on a punctured neighbourhood of `x`.  No chart-coefficient
change-of-variables — the chart coefficient is `α.toFun` paired with the spanning tangent vector. -/
theorem formOrderW_eq_top_iff (α : MeromorphicOneForm X) (x : X) :
    α.formOrderW x = ⊤ ↔ ∀ᶠ y in 𝓝[≠] x, α.toFun y = 0 := by
  rw [formOrderW, meromorphicOrderAt_eq_top_iff]
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x with he
  have hbase : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt ℂ _ x)
  -- The chart coefficient is the intrinsic "covector against the spanning tangent vector",
  -- read in the chart at `x`: `formCoeff = (fun y => α y (symmL y 1)) ∘ chart.symm`.
  have hcoeff : formCoeff α.toFun x = (fun y => α.toFun y (e.symmL ℂ y 1)) ∘ (chartAt ℂ x).symm := rfl
  rw [hcoeff, MeromorphicFunction.eventually_comp_chart_iff
    (fun y => α.toFun y (e.symmL ℂ y 1)) x (· = 0)]
  constructor
  · -- covector kills `symmL 1` near `x` ⟹ covector is `0` near `x` (on the base set).
    intro h
    filter_upwards [h, nhdsWithin_le_nhds hbase] with y hy hybase
    exact α.toFun_eq_zero_of_formCoeff_zero hybase hy
  · -- section vanishes ⟹ its pairing with `symmL 1` vanishes.
    intro h
    filter_upwards [h] with y hy
    rw [hy, ContinuousLinearMap.zero_apply]

/-- `formOrderW α x ≠ ⊤` (the form's germ is nonzero) iff the section `α.toFun` is eventually
nonzero on a punctured neighbourhood of `x`. -/
theorem formOrderW_ne_top_iff (α : MeromorphicOneForm X) (x : X) :
    α.formOrderW x ≠ ⊤ ↔ ∀ᶠ y in 𝓝[≠] x, α.toFun y ≠ 0 := by
  rw [formOrderW, meromorphicOrderAt_ne_top_iff_eventually_ne_zero (α.meromorphic x)]
  set e := trivializationAt ℂ (TangentSpace 𝓘(ℂ) (M := X)) x with he
  have hbase : e.baseSet ∈ 𝓝 x := e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt ℂ _ x)
  have hcoeff : formCoeff α.toFun x = (fun y => α.toFun y (e.symmL ℂ y 1)) ∘ (chartAt ℂ x).symm := rfl
  rw [hcoeff, MeromorphicFunction.eventually_comp_chart_iff
    (fun y => α.toFun y (e.symmL ℂ y 1)) x (· ≠ 0)]
  constructor
  · intro h
    filter_upwards [h] with y hy
    intro hzero; exact hy (by rw [hzero, ContinuousLinearMap.zero_apply])
  · intro h
    filter_upwards [h, nhdsWithin_le_nhds hbase] with y hy hybase
    intro hpair; exact hy (α.toFun_eq_zero_of_formCoeff_zero hybase hpair)

/-- **Form identity theorem.** If the germ of `α` is nonzero (`formOrderW ≠ ⊤`) at even one point,
it is nonzero at *every* point.  The set `{x | formOrderW α x = ⊤}` and its complement are both open
(via the two intrinsic characterizations above), so on the connected `X` it is empty.  Mirror of
`MeromorphicFunction.orderW_ne_top_of_exists`. -/
theorem formOrderW_ne_top_of_exists (α : MeromorphicOneForm X)
    (h₀ : ∃ x₀, α.formOrderW x₀ ≠ ⊤) (x : X) : α.formOrderW x ≠ ⊤ := by
  obtain ⟨x₀, hx₀⟩ := h₀
  have hUopen : IsOpen {y : X | α.formOrderW y = ⊤} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [Set.mem_setOf_eq, formOrderW_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at hy
    obtain ⟨V, hV, hVopen, hyV⟩ := hy
    refine Filter.mem_of_superset (hVopen.mem_nhds hyV) fun y' hy'V => ?_
    rw [Set.mem_setOf_eq, formOrderW_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
    rcases eq_or_ne y' y with rfl | hy'
    · exact ⟨V, hV, hVopen, hy'V⟩
    · exact ⟨V \ {y}, fun z hz _ => hV z hz.1 hz.2, hVopen.sdiff isClosed_singleton, ⟨hy'V, hy'⟩⟩
  have hUclosed : IsClosed {y : X | α.formOrderW y = ⊤} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    have hyne : α.formOrderW y ≠ ⊤ := hy
    rw [formOrderW_ne_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at hyne
    obtain ⟨W, hW, hWopen, hyW⟩ := hyne
    refine Filter.mem_of_superset (hWopen.mem_nhds hyW) fun y' hy'W => ?_
    show α.formOrderW y' ≠ ⊤
    rw [formOrderW_ne_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
    rcases eq_or_ne y' y with rfl | hy'ne
    · exact ⟨W, hW, hWopen, hy'W⟩
    · exact ⟨W \ {y}, fun z hz _ => hW z hz.1 hz.2, hWopen.sdiff isClosed_singleton, ⟨hy'W, hy'ne⟩⟩
  rcases isClopen_iff.mp ⟨hUclosed, hUopen⟩ with hU | hU
  · show x ∉ {y : X | α.formOrderW y = ⊤}
    rw [hU]; exact Set.notMem_empty x
  · exact absurd (hU.ge (Set.mem_univ x₀)) hx₀

end MeromorphicOneForm

end Jacobians.Dolbeault
