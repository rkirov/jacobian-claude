/-
Copyright (c) 2026 Bryan Sanchez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Sanchez
-/
import Jacobians.Discharge.Divisor
import Jacobians.Discharge.Manifold.MeromorphicAt
import Jacobians.Discharge.Manifold.MeromorphicDivisor

set_option autoImplicit true


/-! # The principal divisor map

This file builds the **principal divisor map** that sends a non-zero global
meromorphic function `f : X → ℂ` on a compact complex 1-manifold to its
order divisor `(f) := ∑_x ord_x(f) · [x]` in `Div X`. Concretely, it is a
genuine `Div X`-valued function on the type `MeromorphicNonzero X`, defined
by invoking `Jacobians.Discharge.MMeromorphicOn.divisor` (the chart-pullback
order divisor packaged in `Manifold/MeromorphicDivisor.lean`).

## The intended use

The set `range principalDivisorMap` is the future honest `PrincDiv X`
subgroup of `Div X` (currently `⊥` in `Divisor.lean`). The remaining
input — that the range is contained in `Div⁰ X`, equivalently the
residue theorem on a compact Riemann surface — is **not** in this file;
this file only builds the map.

## What's load-bearing

The `MeromorphicNonzero X` structure carries four fields:

* `toFun : X → ℂ`
* `meromorphic : MMeromorphicOn (𝓘(ℂ, ℂ)) toFun Set.univ`
* `nonvanishing_germ : ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) toFun x ≠ ⊤`
* `regular_continuousAt : ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) toFun x →
                                 ContinuousAt toFun x`

The `nonvanishing_germ` field is the standard non-vanishing-germ hypothesis
("no point has identically-zero germ"). It is **load-bearing**: without it,
`MMeromorphicOn.divisor` cannot be applied (its third argument is exactly
this hypothesis, and the local-finiteness of the support fails for the
identically-zero function).

The `regular_continuousAt` field pins down the *pointwise value* `toFun x`
to equal the analytic-continuation limit at every non-pole point. Without
this, `MMeromorphicOn` only constrains the *germ* of `toFun` in punctured
neighborhoods — meaning a function that disagrees with its germ-limit at
finitely many regular points (e.g. defined arbitrarily there) would still
be a valid `MeromorphicNonzero`. At those points, the pole-extension
`f.toRiemannSphere` would be genuinely discontinuous, making the headline
`R1` `ContMDiff` theorem **false**. The continuity field rules that out.

The constant-zero function does not give a `MeromorphicNonzero X` because
`mmeromorphicOrderAt 𝓘(ℂ,ℂ) 0 x = ⊤` everywhere (the germ is identically
zero). This is the correct semantic exclusion. -/

noncomputable section

open scoped Manifold Topology ContDiff
open Filter Set

namespace Jacobians.Discharge

universe u

/-- A **non-vanishing-germ meromorphic function** on `X`: a function
`f : X → ℂ`, a proof that `f` is meromorphic on `Set.univ`, a proof that
no germ of `f` is identically zero (`mmeromorphicOrderAt I f x ≠ ⊤`
everywhere), and a proof that `f` is continuous at every non-pole point
(`0 ≤ mmeromorphicOrderAt I f x`).

The non-vanishing-germ field is the standard hypothesis under which the
order divisor is locally finite and `principalDivisorMap` is well-defined.

The continuity-at-regular-points field pins down `toFun x` to equal the
analytic-continuation limit at non-pole points. Without it, `MMeromorphicOn`
only constrains the *germ* of `toFun` in punctured neighborhoods — leaving
the pointwise value `toFun x` free to disagree with the germ limit at
finitely many regular points. Such disagreement would make the
pole-extension to the Riemann sphere genuinely discontinuous and break the
unconditional `R1` `ContMDiff` theorem; the continuity field rules it out.

The model is hard-coded to `𝓘(ℂ, ℂ)` (the trivial complex model), matching
the rest of the manifold-meromorphic API in this repository. -/
structure MeromorphicNonzero (X : Type u)
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] where
  /-- The underlying function `X → ℂ`. -/
  toFun : X → ℂ
  /-- `toFun` is meromorphic on the whole manifold. -/
  meromorphic : MMeromorphicOn (𝓘(ℂ, ℂ)) toFun Set.univ
  /-- No point of `X` carries an identically-zero germ of `toFun`
  (equivalently, `toFun` is not the zero function in any chart neighborhood). -/
  nonvanishing_germ :
    ∀ x, mmeromorphicOrderAt (𝓘(ℂ, ℂ)) toFun x ≠ ⊤
  /-- At every non-pole point (`0 ≤ mmeromorphicOrderAt I toFun x`),
  `toFun` is continuous at `x`. Combined with meromorphicity, this forces
  `toFun x` to equal the analytic-continuation limit (the germ limit) at
  `x`, which is exactly what makes the pole-extension to the Riemann
  sphere continuous in the regular branch. -/
  regular_continuousAt :
    ∀ x, 0 ≤ mmeromorphicOrderAt (𝓘(ℂ, ℂ)) toFun x →
      ContinuousAt toFun x

namespace MeromorphicNonzero

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- Coercion from `MeromorphicNonzero X` to the underlying function `X → ℂ`. -/
instance : CoeFun (MeromorphicNonzero X) (fun _ => X → ℂ) where
  coe f := f.toFun

end MeromorphicNonzero

/-- The **principal divisor map**: send a non-vanishing-germ meromorphic
function `f : MeromorphicNonzero X` to its order divisor `(f)` in `Div X`.

The body genuinely invokes `Jacobians.Discharge.MMeromorphicOn.divisor` from
`Manifold/MeromorphicDivisor.lean`; in particular all three fields of
`MeromorphicNonzero` are load-bearing inputs to that divisor construction. -/
noncomputable def principalDivisorMap
    {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : MeromorphicNonzero X) : Div X :=
  Jacobians.Discharge.MMeromorphicOn.divisor (𝓘(ℂ, ℂ)) f.toFun
    f.meromorphic f.nonvanishing_germ

/-- The pointwise value of `principalDivisorMap f` at `x` is the integer
order `orderFun 𝓘(ℂ,ℂ) f.toFun x = (mmeromorphicOrderAt 𝓘(ℂ,ℂ) f.toFun x).untop₀`.
This unfolds the divisor's `toFun` field and is the API-friendly form of the
underlying definition. -/
@[simp] lemma principalDivisorMap_apply
    {X : Type u}
    [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]
    (f : MeromorphicNonzero X) (x : X) :
    (principalDivisorMap f : X → ℤ) x
      = Jacobians.Discharge.MMeromorphicOn.orderFun (𝓘(ℂ, ℂ)) f.toFun x := rfl

/-! ### Multiplicativity of the chart-pulled-back meromorphic order

The lemma `mmeromorphicOrderAt_mul` lifts mathlib's `meromorphicOrderAt_mul`
(`Mathlib/Analysis/Meromorphic/Order.lean`) through the chart-pullback
definition of `mmeromorphicOrderAt`. The proof is purely chart-pullback
bookkeeping: the chart representative of `f * g` is the pointwise product
of the chart representatives of `f` and `g`, so the standard
multiplicativity transports verbatim.

The constant-`1` order lemma `mmeromorphicOrderAt_one` follows from
`meromorphicOrderAt_const` at `c = 1 ≠ 0`. -/

variable {X : Type u}
  [TopologicalSpace X] [ChartedSpace ℂ X]

/-- **Multiplicativity of the chart-pulled-back meromorphic order.**
`mmeromorphicOrderAt I (f * g) x = mmeromorphicOrderAt I f x +
mmeromorphicOrderAt I g x` whenever both `f` and `g` are meromorphic at `x`.

Proof: unfold both sides to `meromorphicOrderAt` of chart pullbacks; observe
`(f * g) ∘ (chartAt ℂ x).symm = (f ∘ (chartAt ℂ x).symm) * (g ∘ (chartAt ℂ x).symm)`
definitionally; apply mathlib's `meromorphicOrderAt_mul`. -/
lemma mmeromorphicOrderAt_mul
    {I : ModelWithCorners ℂ ℂ ℂ} {f g : X → ℂ} {x : X}
    (hf : MMeromorphicAt I f x) (hg : MMeromorphicAt I g x) :
    mmeromorphicOrderAt I (f * g) x
      = mmeromorphicOrderAt I f x + mmeromorphicOrderAt I g x := by
  -- Unpack chart-pullback meromorphy of `f` and `g`.
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  have hg' : MeromorphicAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hg
  -- LHS: `mmeromorphicOrderAt I (f*g) x` is `meromorphicOrderAt ((f*g) ∘ ...) ...`
  -- and `(f * g) ∘ (chartAt ℂ x).symm = (f ∘ ...) * (g ∘ ...)` is rfl.
  show meromorphicOrderAt ((f * g) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
      = meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
        + meromorphicOrderAt (g ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h_comp : (f * g) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) * (g ∘ (chartAt ℂ x).symm) := rfl
  rw [h_comp]
  exact meromorphicOrderAt_mul hf' hg'

/-- **The chart-pulled-back order of the constant `1` is zero.** -/
lemma mmeromorphicOrderAt_one
    {I : ModelWithCorners ℂ ℂ ℂ} {x : X} :
    mmeromorphicOrderAt I (1 : X → ℂ) x = 0 := by
  -- LHS: unfold to `meromorphicOrderAt ((1 : X → ℂ) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)`.
  show meromorphicOrderAt ((1 : X → ℂ) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0
  -- `(1 : X → ℂ) ∘ (chartAt ℂ x).symm = fun _ => (1 : ℂ)` definitionally.
  have h_comp : ((1 : X → ℂ) ∘ (chartAt ℂ x).symm) = (fun _ : ℂ => (1 : ℂ)) := rfl
  rw [h_comp]
  -- Then apply `meromorphicOrderAt_const` at `c = 1`, which is `≠ 0`.
  classical
  rw [meromorphicOrderAt_const ((chartAt ℂ x) x) (1 : ℂ)]
  simp

/-- **The chart-pulled-back order of any nonzero constant `c` is zero.**
Generalizes `mmeromorphicOrderAt_one`. The chart pullback of `fun _ : X => c`
is the literal constant `fun _ : ℂ => c` on the codomain side, whose
mathlib `meromorphicOrderAt` is `0` whenever `c ≠ 0`. -/
lemma mmeromorphicOrderAt_const_ne_zero
    {I : ModelWithCorners ℂ ℂ ℂ} {x : X} {c : ℂ} (hc : c ≠ 0) :
    mmeromorphicOrderAt I (fun _ : X => c) x = 0 := by
  -- Unfold to mathlib `meromorphicOrderAt` after the trivial chart pullback.
  show meromorphicOrderAt ((fun _ : X => c) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0
  have h_comp : ((fun _ : X => c) ∘ (chartAt ℂ x).symm) = (fun _ : ℂ => c) := rfl
  rw [h_comp]
  classical
  rw [meromorphicOrderAt_const ((chartAt ℂ x) x) c]
  -- After the `_const` rewrite the goal becomes `(if c = 0 then ⊤ else 0) = 0`.
  simp [hc]

/-- **Inverse of the chart-pulled-back meromorphic order.**
`mmeromorphicOrderAt I (f⁻¹) x = -mmeromorphicOrderAt I f x`.

Proof: unfold both sides to `meromorphicOrderAt` of the chart pullbacks; observe
`(fun y => (f y)⁻¹) ∘ (chartAt ℂ x).symm = (f ∘ (chartAt ℂ x).symm)⁻¹` definitionally;
apply mathlib's unconditional `meromorphicOrderAt_inv`. -/
lemma mmeromorphicOrderAt_inv
    {I : ModelWithCorners ℂ ℂ ℂ} {f : X → ℂ} {x : X} :
    mmeromorphicOrderAt I (fun y => (f y)⁻¹) x
      = -mmeromorphicOrderAt I f x := by
  -- LHS unfolds to mathlib's `meromorphicOrderAt` on the chart pullback.
  show meromorphicOrderAt ((fun y => (f y)⁻¹) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
      = -meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  -- The chart pullback of `y ↦ (f y)⁻¹` equals the pointwise inverse of the
  -- chart pullback of `f`.
  have h_comp : (fun y => (f y)⁻¹) ∘ (chartAt ℂ x).symm
      = ((f ∘ (chartAt ℂ x).symm))⁻¹ := rfl
  rw [h_comp]
  exact meromorphicOrderAt_inv

/-- **Order of natural powers.** `mmeromorphicOrderAt I (f^n) x = n * mmeromorphicOrderAt I f x`
for natural `n`. -/
lemma mmeromorphicOrderAt_pow
    {I : ModelWithCorners ℂ ℂ ℂ} {f : X → ℂ} {x : X}
    (hf : MMeromorphicAt I f x) {n : ℕ} :
    mmeromorphicOrderAt I (fun y => (f y) ^ n) x
      = n * mmeromorphicOrderAt I f x := by
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  show meromorphicOrderAt ((fun y => (f y) ^ n) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
      = n * meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h_comp : (fun y => (f y) ^ n) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) ^ n := rfl
  rw [h_comp]
  exact meromorphicOrderAt_pow hf'

/-- **Order of integer powers.** `mmeromorphicOrderAt I (f^n) x = n * mmeromorphicOrderAt I f x`
for integer `n`. -/
lemma mmeromorphicOrderAt_zpow
    {I : ModelWithCorners ℂ ℂ ℂ} {f : X → ℂ} {x : X}
    (hf : MMeromorphicAt I f x) {n : ℤ} :
    mmeromorphicOrderAt I (fun y => (f y) ^ n) x
      = n * mmeromorphicOrderAt I f x := by
  have hf' : MeromorphicAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := hf
  show meromorphicOrderAt ((fun y => (f y) ^ n) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
      = n * meromorphicOrderAt (f ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x)
  have h_comp : (fun y => (f y) ^ n) ∘ (chartAt ℂ x).symm
      = (f ∘ (chartAt ℂ x).symm) ^ n := rfl
  rw [h_comp]
  exact meromorphicOrderAt_zpow hf'

end Jacobians.Discharge


/-! ## `MeromorphicNonzero X` as a multiplicative monoid

We endow `MeromorphicNonzero X` with multiplication and the constant `1`.
The multiplicative structure is consumed downstream by
`PrincipalDivisorRange.lean` only via `Mul` and `One` (for the
multiplicative-data bundle); the full `CommMonoid` laws are not used
elsewhere in the repo.

The naive pointwise product `(f * g).toFun x := f.toFun x * g.toFun x`
does **not** discharge the new `regular_continuousAt` field at *pole-zero
cancellation* points (where `f` has a pole, `g` has a zero, and the
orders sum to a non-negative number). At such an `x`, the pole-side value
`f.toFun x` is unconstrained while the zero-side value `g.toFun x` is
forced to `0` (by `g.regular_continuousAt`), so the literal product is
`0` — but the germ-limit of `f * g` at `x` may be the nonzero
"cancellation residue", giving a discontinuity.

We fix this by canonicalizing the product's pointwise value at every
point to the **punctured-neighborhood limit** when one exists, falling
back to the literal pointwise product otherwise (only relevant at genuine
poles of the product, where `regular_continuousAt`'s hypothesis fails
anyway).

The canonicalization changes `(f * g).toFun` only on the (locally
finite) pole set of `f` or `g`, hence does not affect the chart-pulled-
back germ in any punctured neighborhood: `mmeromorphicOrderAt` is
unchanged, and so is `principalDivisorMap (f * g)`.

A note on `CommMonoid`. The previous `CommMonoid` instance for
`MeromorphicNonzero X` relied on `(f * g).toFun = f.toFun * g.toFun`
being `rfl` — a property that is **incompatible** with the new
`regular_continuousAt` field (as the cancellation analysis above shows).
Re-proving the `CommMonoid` laws under the new germ-canonicalized
multiplication requires a multi-case analysis on whether the various
`germLimit` choose-cells fire, which we do not undertake here. The
downstream consumer (`PrincipalDivisorRange.lean`) uses only `Mul` and
`One`, both of which we provide. -/

namespace Jacobians.Discharge.MeromorphicNonzero

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-! ### Punctured-nhd nontriviality on a complex 1-manifold -/

/-- The punctured neighborhood of any point on a complex 1-manifold is
non-trivial. Proof: the chart `e := chartAt ℂ x` is an
`OpenPartialHomeomorph`; `e.map_nhdsWithin_eq` gives `map e (𝓝[{x}ᶜ] x)
= 𝓝[e '' (e.source ∩ {x}ᶜ)] (e x)`. The image set is contained in
`(e x)ᶜ` by injectivity of `e` on its source, so the RHS is `≤ 𝓝[≠] (e x)`,
which is `NeBot` because `ℂ` has no isolated points. The map being `NeBot`
forces `𝓝[≠] x` to be `NeBot` as well (`map_eq_bot_iff`). -/
lemma nhdsNE_neBot (x : X) : (𝓝[≠] x).NeBot := by
  set e := chartAt ℂ x
  have hxe : x ∈ e.source := mem_chart_source ℂ x
  -- `map e (𝓝[≠] x) = 𝓝[e '' (e.source ∩ {x}ᶜ)] (e x)`.
  have h_map : Filter.map e (𝓝[≠] x) = 𝓝[e '' (e.source ∩ {x}ᶜ)] (e x) :=
    e.map_nhdsWithin_eq hxe {x}ᶜ
  -- `e '' (e.source ∩ {x}ᶜ) ⊆ {e x}ᶜ` by injectivity of `e` on source.
  have h_subset : e '' (e.source ∩ {x}ᶜ) ⊆ {e x}ᶜ := by
    rintro p ⟨y, ⟨hy_src, hy_ne⟩, hpy⟩
    intro hp_eq
    apply hy_ne
    rw [Set.mem_singleton_iff] at hp_eq
    rw [Set.mem_singleton_iff]
    exact e.injOn hy_src hxe (hpy.trans hp_eq)
  -- Hence `𝓝[image] (e x) ≤ 𝓝[≠] (e x)`.
  have h_le : (𝓝[e '' (e.source ∩ {x}ᶜ)] (e x)) ≤ 𝓝[≠] (e x) :=
    nhdsWithin_mono _ h_subset
  -- `𝓝[≠] (e x)` is `NeBot` (ℂ has no isolated points).
  haveI : (𝓝[≠] (e x)).NeBot := inferInstance
  -- Therefore `𝓝[image] (e x)` is `NeBot` iff... actually we need the other direction.
  -- We have `h_le` going the wrong way for direct NeBot transfer.
  -- Use: image set is a nhd of e x in e.target, so 𝓝[image] (e x) is NeBot.
  -- Specifically: e '' (e.source \ {x}) = e.target \ {e x}, which is open punctured nhd.
  have h_image_eq : e '' (e.source ∩ {x}ᶜ) = e.target ∩ {e x}ᶜ := by
    ext p
    constructor
    · rintro ⟨y, ⟨hy_src, hy_ne⟩, hpy⟩
      refine ⟨?_, ?_⟩
      · rw [← hpy]; exact e.map_source hy_src
      · intro hp_eq
        simp only [Set.mem_singleton_iff] at hp_eq
        apply hy_ne
        simp only [Set.mem_singleton_iff]
        exact e.injOn hy_src hxe (hpy.trans hp_eq)
    · rintro ⟨hp_target, hp_ne⟩
      refine ⟨e.symm p, ⟨e.map_target hp_target, ?_⟩, e.right_inv hp_target⟩
      intro hsymm_eq
      simp only [Set.mem_singleton_iff] at hsymm_eq hp_ne
      apply hp_ne
      have hr := e.right_inv hp_target
      rw [hsymm_eq] at hr
      exact hr.symm
  -- After substitution: `Filter.map e (𝓝[≠] x) = 𝓝[e.target ∩ {e x}ᶜ] (e x)`.
  rw [h_image_eq] at h_map
  -- `e.target ∩ {e x}ᶜ` is an open nhd of points within `(e x)ᶜ`. Specifically,
  -- `𝓝[e.target ∩ {e x}ᶜ] (e x) = 𝓝[≠] (e x)` since `e.target` is a nhd of `e x`.
  have h_target_nhd : e.target ∈ 𝓝 (e x) :=
    e.open_target.mem_nhds (e.map_source hxe)
  have h_target_nhdsNE : e.target ∈ 𝓝[{e x}ᶜ] (e x) :=
    mem_nhdsWithin_of_mem_nhds h_target_nhd
  have h_eq_nhdsNE : (𝓝[e.target ∩ {e x}ᶜ] (e x)) = 𝓝[≠] (e x) := by
    rw [Set.inter_comm]
    -- nhdsWithin_inter_of_mem' : t ∈ 𝓝[s] a → 𝓝[s ∩ t] a = 𝓝[s] a.
    exact nhdsWithin_inter_of_mem' h_target_nhdsNE
  rw [h_eq_nhdsNE] at h_map
  -- Now `Filter.map e (𝓝[≠] x) = 𝓝[≠] (e x)`. Since RHS is `NeBot`, so is LHS,
  -- and `Filter.map e l` is `NeBot` iff `l` is `NeBot` (`map_neBot_iff`).
  haveI : (Filter.map e (𝓝[≠] x)).NeBot := h_map ▸ inferInstance
  exact (Filter.map_neBot_iff e).mp this

/-- Chart-symm carries `𝓝[≠] (chart x)` into `𝓝[≠] x`. -/
lemma chartSymm_tendsto_nhdsNE (x : X) :
    Filter.Tendsto (chartAt ℂ x).symm
      (𝓝[≠] ((chartAt ℂ x) x)) (𝓝[≠] x) := by
  have h_continuousAt :
      ContinuousAt (chartAt ℂ x).symm ((chartAt ℂ x) x) := by
    have h_co : ContinuousOn (chartAt ℂ x).symm (chartAt ℂ x).target :=
      (chartAt ℂ x).continuousOn_invFun
    exact h_co.continuousAt
      ((chartAt ℂ x).open_target.mem_nhds
        ((chartAt ℂ x).map_source (mem_chart_source ℂ x)))
  have h_pt : (chartAt ℂ x).symm ((chartAt ℂ x) x) = x :=
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x)
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have := h_continuousAt
    rw [ContinuousAt, h_pt] at this
    exact this.mono_left nhdsWithin_le_nhds
  · rw [eventually_iff_exists_mem]
    refine ⟨{z | z ∈ (chartAt ℂ x).target ∧ z ≠ (chartAt ℂ x) x}, ?_, ?_⟩
    · rw [mem_nhdsWithin]
      refine ⟨(chartAt ℂ x).target, (chartAt ℂ x).open_target,
              (chartAt ℂ x).map_source (mem_chart_source ℂ x), ?_⟩
      intro z hz
      refine ⟨hz.1, ?_⟩
      intro hzx
      exact hz.2 hzx
    · intro z hz
      show (chartAt ℂ x).symm z ∈ ({x}ᶜ)
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hsymm
      apply hz.2
      have := (chartAt ℂ x).right_inv hz.1
      rw [hsymm] at this
      exact this.symm

/-- Chart carries `𝓝[≠] x` into `𝓝[≠] (chart x)`. -/
lemma chart_tendsto_nhdsNE (x : X) :
    Filter.Tendsto (chartAt ℂ x) (𝓝[≠] x)
      (𝓝[≠] ((chartAt ℂ x) x)) := by
  have h_continuousAt : ContinuousAt (chartAt ℂ x) x := by
    have h_co : ContinuousOn (chartAt ℂ x) (chartAt ℂ x).source :=
      (chartAt ℂ x).continuousOn_toFun
    exact h_co.continuousAt
      ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
  rw [tendsto_nhdsWithin_iff]
  refine ⟨h_continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
  rw [eventually_iff_exists_mem]
  refine ⟨{y | y ∈ (chartAt ℂ x).source ∧ y ≠ x}, ?_, ?_⟩
  · rw [mem_nhdsWithin]
    refine ⟨(chartAt ℂ x).source, (chartAt ℂ x).open_source,
            mem_chart_source ℂ x, ?_⟩
    intro y hy
    refine ⟨hy.1, ?_⟩
    intro hyx
    exact hy.2 hyx
  · intro y hy
    show (chartAt ℂ x) y ∈ ({(chartAt ℂ x) x}ᶜ)
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hch
    apply hy.2
    exact (chartAt ℂ x).injOn hy.1 (mem_chart_source ℂ x) hch

/-! ### Germ-canonical value helper -/

/-- The **germ-canonical value** of `h : X → ℂ` at `x`: the unique
punctured-neighborhood limit if one exists (extracted via
`Classical.choice`), and otherwise the literal `h x`. Used to canonicalize
`MeromorphicNonzero.toFun` values under multiplication so that
`regular_continuousAt` can be discharged. -/
noncomputable def germLimit (h : X → ℂ) (x : X) : ℂ := by
  classical
  exact if hex : ∃ y : ℂ, Filter.Tendsto h (𝓝[≠] x) (𝓝 y) then hex.choose else h x

/-- If `h` has a punctured-nhd limit `y` at `x`, then `germLimit h x = y`. -/
lemma germLimit_eq_of_tendsto {h : X → ℂ} {x : X} {y : ℂ}
    (htendsto : Filter.Tendsto h (𝓝[≠] x) (𝓝 y)) :
    germLimit h x = y := by
  classical
  haveI := nhdsNE_neBot x
  unfold germLimit
  have hex : ∃ y' : ℂ, Filter.Tendsto h (𝓝[≠] x) (𝓝 y') := ⟨y, htendsto⟩
  rw [dif_pos hex]
  exact tendsto_nhds_unique hex.choose_spec htendsto

/-- If no punctured-nhd limit exists, `germLimit h x = h x`. -/
lemma germLimit_eq_self_of_not_tendsto {h : X → ℂ} {x : X}
    (hnot : ¬ ∃ y : ℂ, Filter.Tendsto h (𝓝[≠] x) (𝓝 y)) :
    germLimit h x = h x := by
  classical
  unfold germLimit
  rw [dif_neg hnot]

/-! ### Manifold-side and chart-side EventuallyEq -/

/-- `germLimit (f * g)` agrees with the literal pointwise product on a
punctured neighborhood of every point on the manifold side.

Proof: at every point `y` near `x` (other than `x` itself) where both
`f` and `g` are non-pole, both `regular_continuousAt`s force continuity
of `f.toFun` and `g.toFun` at `y`. The product is continuous; the
punctured limit at `y` equals the value, so `germLimit (f * g) y =
f.toFun y * g.toFun y`. The exceptional bad set (poles of `f` or `g`,
distinct from `x`) is finite, hence closed, with open complement
containing `x`. -/
lemma germLimit_manifold_eventuallyEq_punctured
    (f g : MeromorphicNonzero X) (x : X) :
    germLimit (fun y => f.toFun y * g.toFun y) =ᶠ[𝓝[≠] x]
      (fun y => f.toFun y * g.toFun y) := by
  have h_f_poles_fin :
      {y : X | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y < (0 : WithTop ℤ)}.Finite :=
    Jacobians.Discharge.MMeromorphicOn.poles_finite (X := X) (𝓘(ℂ, ℂ))
      f.toFun f.meromorphic f.nonvanishing_germ
  have h_g_poles_fin :
      {y : X | mmeromorphicOrderAt 𝓘(ℂ, ℂ) g.toFun y < (0 : WithTop ℤ)}.Finite :=
    Jacobians.Discharge.MMeromorphicOn.poles_finite (X := X) (𝓘(ℂ, ℂ))
      g.toFun g.meromorphic g.nonvanishing_germ
  set BadSet : Set X :=
      ({y : X | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y < (0 : WithTop ℤ)}
        ∪ {y : X | mmeromorphicOrderAt 𝓘(ℂ, ℂ) g.toFun y < (0 : WithTop ℤ)}) \ {x}
    with hBadSet_def
  have h_bad_fin : BadSet.Finite :=
    (h_f_poles_fin.union h_g_poles_fin).diff
  have h_bad_closed : IsClosed BadSet := h_bad_fin.isClosed
  have hx_not_bad : x ∉ BadSet := by
    intro hxB; exact hxB.2 rfl
  have h_compl_open : IsOpen BadSetᶜ := h_bad_closed.isOpen_compl
  have hx_compl : x ∈ BadSetᶜ := hx_not_bad
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [h_compl_open.mem_nhds hx_compl] with y hy_compl hy_ne
  -- `hy_compl : y ∈ BadSetᶜ`, `hy_ne : y ∈ {x}ᶜ`.
  -- Unfold both: we want `0 ≤ order_f y` and `0 ≤ order_g y`.
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy_ne
  -- `hy_ne : y ≠ x`.
  have hy_not_pole : ¬ y ∈ ({y' | mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y' < (0 : WithTop ℤ)}
        ∪ {y' | mmeromorphicOrderAt 𝓘(ℂ, ℂ) g.toFun y' < (0 : WithTop ℤ)}) := by
    intro hyP
    apply hy_compl
    show y ∈ BadSet
    refine ⟨hyP, ?_⟩
    intro hyx
    exact hy_ne hyx
  have hf_reg : 0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun y := by
    by_contra h
    push_neg at h
    apply hy_not_pole
    exact Or.inl h
  have hg_reg : 0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) g.toFun y := by
    by_contra h
    push_neg at h
    apply hy_not_pole
    exact Or.inr h
  have hf_cont : ContinuousAt f.toFun y := f.regular_continuousAt y hf_reg
  have hg_cont : ContinuousAt g.toFun y := g.regular_continuousAt y hg_reg
  have h_prod_cont : ContinuousAt (fun z => f.toFun z * g.toFun z) y :=
    hf_cont.mul hg_cont
  have h_punct_tend : Filter.Tendsto (fun z => f.toFun z * g.toFun z) (𝓝[≠] y)
      (𝓝 (f.toFun y * g.toFun y)) :=
    (h_prod_cont.tendsto).mono_left nhdsWithin_le_nhds
  exact germLimit_eq_of_tendsto h_punct_tend

/-- Chart-side counterpart: after chart-pullback, `germLimit (f * g) ∘
chart.symm` agrees with the literal pointwise product on a punctured
neighborhood of `chart x`. -/
lemma germLimit_chart_eventuallyEq_punctured
    (f g : MeromorphicNonzero X) (x : X) :
    ((germLimit (fun y => f.toFun y * g.toFun y)) ∘ (chartAt ℂ x).symm)
      =ᶠ[𝓝[≠] ((chartAt ℂ x) x)]
      ((fun y => f.toFun y * g.toFun y) ∘ (chartAt ℂ x).symm) :=
  (chartSymm_tendsto_nhdsNE x).eventually
    (germLimit_manifold_eventuallyEq_punctured f g x)

/-! ### Multiplication and identity -/

/-- Multiplication of non-vanishing-germ meromorphic functions: the value
at every point is the **germ-canonical** pointwise product. -/
noncomputable instance : Mul (MeromorphicNonzero X) where
  mul f g :=
    { toFun := germLimit (fun y => f.toFun y * g.toFun y)
      meromorphic := by
        intro x _
        show MeromorphicAt
            ((germLimit (fun y => f.toFun y * g.toFun y)) ∘ (chartAt ℂ x).symm)
            ((chartAt ℂ x) x)
        have h_chart_mero : MeromorphicAt
            ((fun y => f.toFun y * g.toFun y) ∘ (chartAt ℂ x).symm)
            ((chartAt ℂ x) x) := by
          have hf_at : MMeromorphicAt 𝓘(ℂ, ℂ) f.toFun x := f.meromorphic x trivial
          have hg_at : MMeromorphicAt 𝓘(ℂ, ℂ) g.toFun x := g.meromorphic x trivial
          exact hf_at.mul hg_at
        exact h_chart_mero.congr
          (germLimit_chart_eventuallyEq_punctured f g x).symm
      nonvanishing_germ := by
        intro x
        have h_chart_eq :
            mmeromorphicOrderAt 𝓘(ℂ, ℂ)
              (germLimit (fun y => f.toFun y * g.toFun y)) x
              = mmeromorphicOrderAt 𝓘(ℂ, ℂ) (fun y => f.toFun y * g.toFun y) x := by
          show meromorphicOrderAt
              ((germLimit (fun y => f.toFun y * g.toFun y)) ∘ (chartAt ℂ x).symm)
              ((chartAt ℂ x) x)
              = meromorphicOrderAt
                ((fun y => f.toFun y * g.toFun y) ∘ (chartAt ℂ x).symm)
                ((chartAt ℂ x) x)
          exact meromorphicOrderAt_congr
            (germLimit_chart_eventuallyEq_punctured f g x)
        rw [h_chart_eq]
        have hf_at : MMeromorphicAt 𝓘(ℂ, ℂ) f.toFun x := f.meromorphic x trivial
        have hg_at : MMeromorphicAt 𝓘(ℂ, ℂ) g.toFun x := g.meromorphic x trivial
        have h_eq_mul : (fun y => f.toFun y * g.toFun y) = f.toFun * g.toFun := rfl
        rw [h_eq_mul]
        have h_sum :
            mmeromorphicOrderAt 𝓘(ℂ, ℂ) (f.toFun * g.toFun) x
              = mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun x
                + mmeromorphicOrderAt 𝓘(ℂ, ℂ) g.toFun x :=
          mmeromorphicOrderAt_mul hf_at hg_at
        rw [h_sum]
        intro h_top
        rw [WithTop.add_eq_top] at h_top
        rcases h_top with h | h
        · exact f.nonvanishing_germ x h
        · exact g.nonvanishing_germ x h
      regular_continuousAt := by
        intro x hx
        have h_chart_eq :
            mmeromorphicOrderAt 𝓘(ℂ, ℂ)
              (germLimit (fun y => f.toFun y * g.toFun y)) x
              = mmeromorphicOrderAt 𝓘(ℂ, ℂ) (fun y => f.toFun y * g.toFun y) x := by
          show meromorphicOrderAt
              ((germLimit (fun y => f.toFun y * g.toFun y)) ∘ (chartAt ℂ x).symm)
              ((chartAt ℂ x) x)
              = meromorphicOrderAt
                ((fun y => f.toFun y * g.toFun y) ∘ (chartAt ℂ x).symm)
                ((chartAt ℂ x) x)
          exact meromorphicOrderAt_congr
            (germLimit_chart_eventuallyEq_punctured f g x)
        rw [h_chart_eq] at hx
        have h_chart_mero : MeromorphicAt
            ((fun y => f.toFun y * g.toFun y) ∘ (chartAt ℂ x).symm)
            ((chartAt ℂ x) x) := by
          have hf_at : MMeromorphicAt 𝓘(ℂ, ℂ) f.toFun x := f.meromorphic x trivial
          have hg_at : MMeromorphicAt 𝓘(ℂ, ℂ) g.toFun x := g.meromorphic x trivial
          exact hf_at.mul hg_at
        obtain ⟨c, h_chart_tend⟩ :=
          tendsto_nhds_of_meromorphicOrderAt_nonneg h_chart_mero hx
        have h_compose : Filter.Tendsto
            (((fun y => f.toFun y * g.toFun y) ∘ (chartAt ℂ x).symm) ∘ (chartAt ℂ x))
            (𝓝[≠] x) (𝓝 c) :=
          h_chart_tend.comp (chart_tendsto_nhdsNE x)
        have h_mfd_tend : Filter.Tendsto
            (fun y => f.toFun y * g.toFun y) (𝓝[≠] x) (𝓝 c) := by
          apply h_compose.congr'
          have h_src_mem : (chartAt ℂ x).source ∈ 𝓝[≠] x :=
            nhdsWithin_le_nhds
              ((chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x))
          filter_upwards [h_src_mem] with y hy
          show (fun z => f.toFun z * g.toFun z) ((chartAt ℂ x).symm ((chartAt ℂ x) y))
              = f.toFun y * g.toFun y
          rw [(chartAt ℂ x).left_inv hy]
        have h_germ_val :
            germLimit (fun y => f.toFun y * g.toFun y) x = c :=
          germLimit_eq_of_tendsto h_mfd_tend
        rw [continuousAt_iff_punctured_nhds]
        rw [h_germ_val]
        apply h_mfd_tend.congr'
        exact (germLimit_manifold_eventuallyEq_punctured f g x).symm }

/-- `(f * g).toFun x = germLimit (f.toFun * g.toFun) x`. Definitional. -/
@[simp] lemma mul_toFun (f g : MeromorphicNonzero X) (x : X) :
    (f * g).toFun x = germLimit (fun y => f.toFun y * g.toFun y) x := rfl

/-- At every doubly-regular point (where both `f` and `g` are non-pole),
`(f * g).toFun x` equals the literal pointwise product
`f.toFun x * g.toFun x`. -/
lemma mul_toFun_eq_pointwise_of_regular (f g : MeromorphicNonzero X) {x : X}
    (hf : 0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun x)
    (hg : 0 ≤ mmeromorphicOrderAt 𝓘(ℂ, ℂ) g.toFun x) :
    (f * g).toFun x = f.toFun x * g.toFun x := by
  have hf_cont : ContinuousAt f.toFun x := f.regular_continuousAt x hf
  have hg_cont : ContinuousAt g.toFun x := g.regular_continuousAt x hg
  have h_prod_cont : ContinuousAt (fun y => f.toFun y * g.toFun y) x :=
    hf_cont.mul hg_cont
  have h_punct_tend : Filter.Tendsto (fun y => f.toFun y * g.toFun y) (𝓝[≠] x)
      (𝓝 (f.toFun x * g.toFun x)) :=
    (h_prod_cont.tendsto).mono_left nhdsWithin_le_nhds
  show germLimit (fun y => f.toFun y * g.toFun y) x = f.toFun x * g.toFun x
  exact germLimit_eq_of_tendsto h_punct_tend

/-- The constant function `1` as a `MeromorphicNonzero`. -/
noncomputable def one (X : Type*) [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X] :
    MeromorphicNonzero X :=
  { toFun := fun _ => (1 : ℂ)
    meromorphic := MMeromorphicOn.const (1 : ℂ)
    nonvanishing_germ := by
      intro x
      have h_eq : (fun _ : X => (1 : ℂ)) = (1 : X → ℂ) := rfl
      rw [h_eq, mmeromorphicOrderAt_one]
      exact WithTop.zero_ne_top
    regular_continuousAt := by
      intro _ _
      exact continuousAt_const }

noncomputable instance : One (MeromorphicNonzero X) := ⟨one X⟩

/-- The non-zero complex constant `c : ℂ` (with `hc : c ≠ 0`), packaged as
a `MeromorphicNonzero X`.

* `meromorphic`: every constant function is meromorphic at every point
  (`MMeromorphicOn.const c`, lifted from mathlib's
  `analyticAt_const.meromorphicAt` via the chart pullback).
* `nonvanishing_germ`: a non-zero constant has chart-pulled-back order
  `0 ≠ ⊤` everywhere (`mmeromorphicOrderAt_const_ne_zero hc`).
* `regular_continuousAt`: constants are continuous (`continuousAt_const`),
  so the regular-point hypothesis is irrelevant. -/
noncomputable def const (c : ℂ) (hc : c ≠ 0) : MeromorphicNonzero X :=
  { toFun := fun _ => c
    meromorphic := MMeromorphicOn.const c
    nonvanishing_germ := by
      intro x
      rw [mmeromorphicOrderAt_const_ne_zero hc]
      exact WithTop.zero_ne_top
    regular_continuousAt := by
      intro _ _
      exact continuousAt_const }

@[simp] lemma const_toFun (c : ℂ) (hc : c ≠ 0) (x : X) :
    (const (X := X) c hc).toFun x = c := rfl

/-- The coercion form of `const_toFun`: viewed as a function `X → ℂ` via the
`CoeFun` instance, `const c hc` evaluates to `c` everywhere. -/
@[simp] lemma const_coe_apply (c : ℂ) (hc : c ≠ 0) (x : X) :
    ((const (X := X) c hc) : X → ℂ) x = c := rfl

/-- The pointwise value of `const c hc` is non-zero everywhere.

This is the **`const_zero_invalid`** auxiliary lemma: although the
constructor `MeromorphicNonzero.const` already requires `hc : c ≠ 0`, this
lemma makes the consequence — non-vanishing of every value of the
constant function — directly accessible at the `toFun` level. It is the
witness any downstream `f.toFun x ≠ 0` rewrite needs when `f = const c hc`. -/
lemma const_toFun_ne_zero (c : ℂ) (hc : c ≠ 0) (x : X) :
    (const (X := X) c hc).toFun x ≠ 0 := by
  rw [const_toFun]
  exact hc

/-- Coercion form of `const_toFun_ne_zero`. -/
lemma const_coe_ne_zero (c : ℂ) (hc : c ≠ 0) (x : X) :
    ((const (X := X) c hc) : X → ℂ) x ≠ 0 :=
  const_toFun_ne_zero c hc x

/-- The constant `MeromorphicNonzero` value is determined by its scalar
**at any chosen point `x : X`**: two non-zero constants are equal as
`MeromorphicNonzero X` iff their scalars agree. Stated point-relative so
the lemma is usable on a possibly-empty `X` without an extra `[Nonempty X]`
assumption. -/
lemma const_eq_iff_of_point (c c' : ℂ) (hc : c ≠ 0) (hc' : c' ≠ 0)
    (x : X) :
    (const (X := X) c hc) = const c' hc' ↔ c = c' := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hfun : (const (X := X) c hc).toFun = (const c' hc').toFun :=
      congrArg MeromorphicNonzero.toFun h
    have := congrFun hfun x
    simpa [const_toFun] using this
  · subst h; rfl

/-- `(1 : MeromorphicNonzero X).toFun x = 1`. Definitional. -/
@[simp] lemma one_toFun (x : X) :
    ((1 : MeromorphicNonzero X)).toFun x = (1 : ℂ) := rfl

/-- Two `MeromorphicNonzero X` values are equal iff their underlying
functions are equal pointwise. -/
@[ext] theorem ext_aux {f g : MeromorphicNonzero X}
    (h : ∀ x, f.toFun x = g.toFun x) : f = g := by
  cases f with
  | mk f1 f2 f3 f4 =>
    cases g with
    | mk g1 g2 g3 g4 =>
      have hfg : f1 = g1 := funext h
      subst hfg
      rfl

end Jacobians.Discharge.MeromorphicNonzero

/-! ## `principalDivisorMap` is multiplicative

We prove that `principalDivisorMap` sends multiplication on
`MeromorphicNonzero X` to addition on `Div X`. With the new germ-
canonicalized `Mul`, the underlying chart-pulled-back germ at every point
is **the same** as for the literal pointwise product (the canonicalization
only changes values on a discrete pole set, not on punctured nhds).
Multiplicativity of the order divisor therefore reduces to the
chart-pullback `mmeromorphicOrderAt_mul` plus a `meromorphicOrderAt_congr`
to bridge the `germLimit (...)` representative back to `f.toFun * g.toFun`. -/

namespace Jacobians.Discharge

open Jacobians.Discharge.MeromorphicNonzero (germLimit
  germLimit_chart_eventuallyEq_punctured)

variable {X : Type u}
  [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [ChartedSpace ℂ X] [IsManifold (𝓘(ℂ, ℂ)) ω X]

/-- The order divisor of `1 : MeromorphicNonzero X` is the zero divisor:
the constant function `1` has order zero everywhere. -/
@[simp] lemma principalDivisorMap_one :
    principalDivisorMap (1 : MeromorphicNonzero X) = (0 : Div X) := by
  classical
  ext x
  show Jacobians.Discharge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ)
      ((1 : MeromorphicNonzero X).toFun) x = (0 : Div X) x
  have h_one : (1 : MeromorphicNonzero X).toFun = (1 : X → ℂ) := rfl
  rw [h_one]
  unfold MMeromorphicOn.orderFun
  rw [mmeromorphicOrderAt_one]
  rfl

/-- The order divisor of a product is the sum of order divisors:
`ord_x(f * g) = ord_x(f) + ord_x(g)`, summed over `x`.

With the new germ-canonicalized `Mul`, the underlying chart-pulled-back
germ of `(f * g).toFun = germLimit (f.toFun * g.toFun)` agrees with that
of the literal `f.toFun * g.toFun` (via
`germLimit_chart_eventuallyEq_punctured`), so `mmeromorphicOrderAt` is
unchanged and the original `mmeromorphicOrderAt_mul` decomposition
applies. -/
lemma principalDivisorMap_mul (f g : MeromorphicNonzero X) :
    principalDivisorMap (f * g)
      = principalDivisorMap f + principalDivisorMap g := by
  classical
  ext x
  show Jacobians.Discharge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ)
      ((f * g).toFun) x
    = (principalDivisorMap f + principalDivisorMap g : Div X) x
  have h_sum_apply :
      ((principalDivisorMap f + principalDivisorMap g : Div X) : X → ℤ) x
        = Jacobians.Discharge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ) f.toFun x
          + Jacobians.Discharge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ) g.toFun x := by
    simp [Function.locallyFinsuppWithin.coe_add, Pi.add_apply]
  rw [h_sum_apply]
  -- Bridge `(f * g).toFun = germLimit (...)` to `f.toFun * g.toFun` via the
  -- chart-side EventuallyEq, then apply `mmeromorphicOrderAt_mul`.
  show (mmeromorphicOrderAt 𝓘(ℂ, ℂ) (germLimit (fun y => f.toFun y * g.toFun y)) x).untop₀
      = (mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun x).untop₀
        + (mmeromorphicOrderAt 𝓘(ℂ, ℂ) g.toFun x).untop₀
  -- Step 1: `mmeromorphicOrderAt 𝓘 (germLimit (f.toFun * g.toFun)) x =
  --          mmeromorphicOrderAt 𝓘 (f.toFun * g.toFun) x`.
  have h_chart_order :
      mmeromorphicOrderAt 𝓘(ℂ, ℂ) (germLimit (fun y => f.toFun y * g.toFun y)) x
        = mmeromorphicOrderAt 𝓘(ℂ, ℂ) (fun y => f.toFun y * g.toFun y) x := by
    show meromorphicOrderAt
        ((germLimit (fun y => f.toFun y * g.toFun y)) ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x)
        = meromorphicOrderAt
          ((fun y => f.toFun y * g.toFun y) ∘ (chartAt ℂ x).symm)
          ((chartAt ℂ x) x)
    exact meromorphicOrderAt_congr
      (germLimit_chart_eventuallyEq_punctured f g x)
  rw [h_chart_order]
  -- Step 2: standard `mmeromorphicOrderAt_mul` decomposition.
  have h_eq_mul : (fun y => f.toFun y * g.toFun y) = f.toFun * g.toFun := rfl
  rw [h_eq_mul]
  have hf_at : MMeromorphicAt 𝓘(ℂ, ℂ) f.toFun x := f.meromorphic x trivial
  have hg_at : MMeromorphicAt 𝓘(ℂ, ℂ) g.toFun x := g.meromorphic x trivial
  have h_order :
      mmeromorphicOrderAt 𝓘(ℂ, ℂ) (f.toFun * g.toFun) x
        = mmeromorphicOrderAt 𝓘(ℂ, ℂ) f.toFun x
          + mmeromorphicOrderAt 𝓘(ℂ, ℂ) g.toFun x :=
    mmeromorphicOrderAt_mul hf_at hg_at
  rw [h_order]
  exact WithTop.untop₀_add (f.nonvanishing_germ x) (g.nonvanishing_germ x)

/-! ### The trivial case of the residue theorem: non-zero constants

The principal divisor of a non-zero constant function is the zero divisor:
`mmeromorphicOrderAt 𝓘(ℂ,ℂ) (fun _ => c) x = 0` everywhere (by
`mmeromorphicOrderAt_const_ne_zero hc`), so `orderFun ... x = 0`
everywhere, and the divisor is pointwise zero. The degree is then `0` by
`Div.degree_zero`. This is the trivially-true case of the residue
theorem on a compact Riemann surface — the "constants are degree-zero"
sub-claim — and is the unique `MeromorphicNonzero` representative with
`mmeromorphicOrderAt I f x = 0` at every point. -/

/-- The principal divisor of a non-zero constant function is the zero
divisor. The chart-pulled-back order of `fun _ => c` is `0` everywhere
(by `mmeromorphicOrderAt_const_ne_zero hc`), so the order divisor is
pointwise zero. -/
@[simp] lemma principalDivisorMap_const (c : ℂ) (hc : c ≠ 0) :
    principalDivisorMap (MeromorphicNonzero.const (X := X) c hc) = (0 : Div X) := by
  classical
  ext x
  show Jacobians.Discharge.MMeromorphicOn.orderFun 𝓘(ℂ, ℂ)
      ((MeromorphicNonzero.const (X := X) c hc).toFun) x = (0 : Div X) x
  -- Unfold `(const c hc).toFun` to the literal constant function `fun _ => c`.
  have h_const : (MeromorphicNonzero.const (X := X) c hc).toFun = (fun _ : X => c) := rfl
  rw [h_const]
  unfold MMeromorphicOn.orderFun
  rw [mmeromorphicOrderAt_const_ne_zero hc]
  rfl

/-- The **trivial case of the residue theorem** for non-zero constant
functions: the principal divisor of `MeromorphicNonzero.const c hc` has
degree `0`. Direct corollary of `principalDivisorMap_const` and
`Div.degree_zero`. -/
lemma residueTheorem_const (c : ℂ) (hc : c ≠ 0) :
    (principalDivisorMap (MeromorphicNonzero.const (X := X) c hc)).degree = 0 := by
  rw [principalDivisorMap_const c hc, Div.degree_zero]

end Jacobians.Discharge
