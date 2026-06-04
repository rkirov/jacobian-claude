/-
  Riemann–Roch INTERFACE (the meet-in-the-middle).

  Goal: reduce the headline consumer `exists_singleSimplePole_of_genus_zero` to ONE genuine
  classical input — Riemann–Roch — by PROVING every step in between (no typeclass/sorry
  relocation). When the Dolbeault→Serre climb (G2–G4) discharges that single input, the
  headline theorem falls out.

  PROVEN (axiom-clean): the ℂ-module on `MeromorphicFunction X` (so `L(D)` can be a
  `Submodule ℂ`); `linearSystem D` as a `Submodule` + `lDim`.

  ISOLATED INPUTS (the genuine wall — the only `sorry`s here):
    • `exists_riemannRoch_divisor` — a canonical divisor `K` with `l(D)−l(K−D)=deg D+1−g`
      (Forster 16.9; ⟸ Dolbeault/Serre, absent from Mathlib).
    • `MeromorphicFunction.deg_div` — every principal divisor has degree 0 (residue theorem).

  REAL REDUCTIONS STILL TO PROVE (no theater — these are genuine, not relocations):
  faithfulness/identity theorem (nonzero ⟹ order ≠ ⊤), `l(0)=1` via Liouville, `l(D)=0` for
  `deg D<0`, and the single-simple-pole extraction.
-/
import Jacobians.Abel
import Jacobians.MeromorphicLiouville
import Jacobians.DegDivResidue

-- Many declarations here are purely algebraic (the ℂ-module on `MeromorphicFunction`) and use
-- only `[ChartedSpace ℂ X]`, not the full compact-manifold hypotheses carried by the consumers.
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MeromorphicFunction

-- The structural facts and the ℂ-module algebra below use only the charted-space structure (no
-- compactness/connectedness), so they apply to open submanifolds `↥U` too. Omit the unused
-- hypotheses so the derived instances have a minimal typeclass footprint.
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

/-- Two meromorphic functions are equal iff their underlying maps agree (the meromorphy
field is a `Prop`, hence proof-irrelevant). -/
@[ext] theorem ext {f g : MeromorphicFunction X} (h : f.toFun = g.toFun) : f = g := by
  obtain ⟨ft, fh⟩ := f
  obtain ⟨gt, gh⟩ := g
  subst h
  rfl

theorem toFun_injective :
    Function.Injective (MeromorphicFunction.toFun : MeromorphicFunction X → (X → ℂ)) :=
  fun _ _ h => ext h

end MeromorphicFunction

/-! ### Meromorphy is preserved by the pointwise vector-space operations

These need only the charted-space structure, not the full compact-manifold hypotheses. -/

section
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

theorem IsMeromorphic.add {f g : X → ℂ} (hf : IsMeromorphic X f) (hg : IsMeromorphic X g) :
    IsMeromorphic X (f + g) := fun x => (hf x).add (hg x)

theorem IsMeromorphic.neg {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X (-f) := fun x => (hf x).neg

theorem IsMeromorphic.sub {f g : X → ℂ} (hf : IsMeromorphic X f) (hg : IsMeromorphic X g) :
    IsMeromorphic X (f - g) := by rw [sub_eq_add_neg]; exact hf.add hg.neg

theorem IsMeromorphic.const_smul (c : ℂ) {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X (c • f) := fun x => (MeromorphicAt.const c _).smul (hf x)

theorem IsMeromorphic.nsmul (n : ℕ) {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X (n • f) := by
  have h : (n • f : X → ℂ) = (n : ℂ) • f := by funext x; simp [nsmul_eq_mul]
  rw [h]; exact hf.const_smul _

theorem IsMeromorphic.zsmul (n : ℤ) {f : X → ℂ} (hf : IsMeromorphic X f) :
    IsMeromorphic X (n • f) := by
  have h : (n • f : X → ℂ) = (n : ℂ) • f := by funext x; simp [zsmul_eq_mul]
  rw [h]; exact hf.const_smul _

end

/-! ### The ℂ-vector-space structure on `MeromorphicFunction X`

Built by transporting the structure on `X → ℂ` along the injective map `toFun`. -/

namespace MeromorphicFunction

section Algebra
-- The ℂ-vector-space algebra uses only the charted-space structure; omit the rest so the module
-- instances apply to open submanifolds `↥U` (which are not compact) — used by the Dolbeault Čech layer.
omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]

noncomputable instance : Zero (MeromorphicFunction X) := ⟨⟨fun _ => 0, IsMeromorphic.zero X⟩⟩
noncomputable instance : Add (MeromorphicFunction X) :=
  ⟨fun f g => ⟨f.toFun + g.toFun, IsMeromorphic.add f.meromorphic g.meromorphic⟩⟩
noncomputable instance : Neg (MeromorphicFunction X) :=
  ⟨fun f => ⟨-f.toFun, IsMeromorphic.neg f.meromorphic⟩⟩
noncomputable instance : Sub (MeromorphicFunction X) :=
  ⟨fun f g => ⟨f.toFun - g.toFun, IsMeromorphic.sub f.meromorphic g.meromorphic⟩⟩
noncomputable instance : SMul ℕ (MeromorphicFunction X) :=
  ⟨fun n f => ⟨n • f.toFun, IsMeromorphic.nsmul n f.meromorphic⟩⟩
noncomputable instance : SMul ℤ (MeromorphicFunction X) :=
  ⟨fun n f => ⟨n • f.toFun, IsMeromorphic.zsmul n f.meromorphic⟩⟩
noncomputable instance : SMul ℂ (MeromorphicFunction X) :=
  ⟨fun c f => ⟨c • f.toFun, IsMeromorphic.const_smul c f.meromorphic⟩⟩

@[simp] theorem add_toFun (f g : MeromorphicFunction X) :
    (f + g).toFun = f.toFun + g.toFun := rfl
@[simp] theorem zero_toFun : (0 : MeromorphicFunction X).toFun = 0 := rfl
@[simp] theorem neg_toFun (f : MeromorphicFunction X) : (-f).toFun = -f.toFun := rfl
@[simp] theorem sub_toFun (f g : MeromorphicFunction X) :
    (f - g).toFun = f.toFun - g.toFun := rfl
@[simp] theorem smul_toFun (c : ℂ) (f : MeromorphicFunction X) :
    (c • f).toFun = c • f.toFun := rfl

noncomputable instance : AddCommGroup (MeromorphicFunction X) :=
  toFun_injective.addCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- The underlying-map homomorphism, used to transport the `Module` structure. -/
def toFunHom : MeromorphicFunction X →+ (X → ℂ) where
  toFun := MeromorphicFunction.toFun
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable instance : Module ℂ (MeromorphicFunction X) :=
  toFun_injective.module ℂ toFunHom (fun _ _ => rfl)

end Algebra

/-- The order of `f` at `x` as `WithTop ℤ` — the meromorphic order *before* the `untop₀` that
defines `orderAtPoint`. It is `⊤` exactly when `f` vanishes in a punctured neighbourhood of `x`;
phrasing `L(D)` on this order makes the zero function a member of every `L(D)` automatically. -/
noncomputable def orderW (f : MeromorphicFunction X) (x : X) : WithTop ℤ :=
  meromorphicOrderAt (f.toFun ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)

theorem orderW_zero (x : X) : (0 : MeromorphicFunction X).orderW x = ⊤ := by
  rw [orderW, meromorphicOrderAt_eq_top_iff]
  exact Filter.Eventually.of_forall fun _ => rfl

/-- The chart is a local homeomorphism near `y`, so an eventually-property of `g` on the punctured
neighbourhood `𝓝[≠] y` transfers to the chart-pulled-back function on `𝓝[≠] (chart y)`. -/
theorem eventually_comp_chart_iff (g : X → ℂ) (y : X) (P : ℂ → Prop) :
    (∀ᶠ w in 𝓝[≠] ((chartAt (H := ℂ) y) y), P ((g ∘ (chartAt (H := ℂ) y).symm) w))
      ↔ ∀ᶠ z in 𝓝[≠] y, P (g z) := by
  have hy : y ∈ (chartAt (H := ℂ) y).source := mem_chart_source ℂ y
  have hyt : (chartAt (H := ℂ) y) y ∈ (chartAt (H := ℂ) y).target :=
    (chartAt (H := ℂ) y).map_source hy
  have hey : (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) = y :=
    (chartAt (H := ℂ) y).left_inv hy
  rw [eventually_nhdsWithin_iff, eventually_nhdsWithin_iff]
  constructor
  · intro h
    have h2 := ((chartAt (H := ℂ) y).continuousAt hy).eventually h
    filter_upwards [h2, (chartAt (H := ℂ) y).open_source.mem_nhds hy] with z hz hz_src
    intro hz_mem
    have hz_ne : z ≠ y := hz_mem
    have hchart : (chartAt (H := ℂ) y) z ∈ ({(chartAt (H := ℂ) y) y} : Set ℂ)ᶜ :=
      fun heq => hz_ne ((chartAt (H := ℂ) y).injOn hz_src hy heq)
    have := hz hchart
    rwa [Function.comp_apply, (chartAt (H := ℂ) y).left_inv hz_src] at this
  · intro h
    have hsymm : ContinuousAt (chartAt (H := ℂ) y).symm ((chartAt (H := ℂ) y) y) :=
      (chartAt (H := ℂ) y).continuousAt_symm hyt
    have h2 := hsymm.eventually (p := fun z => z ∈ ({y} : Set X)ᶜ → P (g z)) (by rw [hey]; exact h)
    filter_upwards [h2, (chartAt (H := ℂ) y).open_target.mem_nhds hyt] with w hw hw_tgt
    intro hw_mem
    have hw_ne : w ≠ (chartAt (H := ℂ) y) y := hw_mem
    have hsymm_ne : (chartAt (H := ℂ) y).symm w ∈ ({y} : Set X)ᶜ := by
      intro heq
      apply hw_ne
      have hr := (chartAt (H := ℂ) y).right_inv hw_tgt
      rw [Set.mem_singleton_iff.mp heq] at hr
      exact hr.symm
    have := hw hsymm_ne
    rw [Function.comp_apply]; exact this

/-- `orderW f y = ⊤` (the germ vanishes) iff `f.toFun` vanishes throughout a punctured
neighbourhood of `y` (intrinsic — the chart drops out). -/
theorem orderW_eq_top_iff (f : MeromorphicFunction X) (y : X) :
    f.orderW y = ⊤ ↔ ∀ᶠ z in 𝓝[≠] y, f.toFun z = 0 := by
  rw [orderW, meromorphicOrderAt_eq_top_iff]
  exact eventually_comp_chart_iff f.toFun y (· = 0)

/-- `orderW f y ≠ ⊤` (the germ is nonzero) iff `f.toFun` is eventually nonzero on a punctured
neighbourhood of `y`. -/
theorem orderW_ne_top_iff (f : MeromorphicFunction X) (y : X) :
    f.orderW y ≠ ⊤ ↔ ∀ᶠ z in 𝓝[≠] y, f.toFun z ≠ 0 := by
  rw [orderW, meromorphicOrderAt_ne_top_iff_eventually_ne_zero (f.meromorphic y)]
  exact eventually_comp_chart_iff f.toFun y (· ≠ 0)

/-- **Faithfulness / identity theorem.** If the germ of `f` is nonzero at even one point, it is
nonzero (`orderW ≠ ⊤`) at *every* point. The set `{y | orderW f y = ⊤}` and its complement are
both open (via the two intrinsic characterizations above), so on the connected `X` it is empty. -/
theorem orderW_ne_top_of_exists (f : MeromorphicFunction X)
    (h₀ : ∃ x₀, f.orderW x₀ ≠ ⊤) (x : X) : f.orderW x ≠ ⊤ := by
  obtain ⟨x₀, hx₀⟩ := h₀
  have hUopen : IsOpen {y : X | f.orderW y = ⊤} := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    rw [Set.mem_setOf_eq, orderW_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at hy
    obtain ⟨V, hV, hVopen, hyV⟩ := hy
    refine Filter.mem_of_superset (hVopen.mem_nhds hyV) fun y' hy'V => ?_
    rw [Set.mem_setOf_eq, orderW_eq_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
    rcases eq_or_ne y' y with rfl | hy'
    · exact ⟨V, hV, hVopen, hy'V⟩
    · exact ⟨V \ {y}, fun z hz _ => hV z hz.1 hz.2, hVopen.sdiff isClosed_singleton, ⟨hy'V, hy'⟩⟩
  have hUclosed : IsClosed {y : X | f.orderW y = ⊤} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    have hyne : f.orderW y ≠ ⊤ := hy
    rw [orderW_ne_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff] at hyne
    obtain ⟨W, hW, hWopen, hyW⟩ := hyne
    refine Filter.mem_of_superset (hWopen.mem_nhds hyW) fun y' hy'W => ?_
    show f.orderW y' ≠ ⊤
    rw [orderW_ne_top_iff, eventually_nhdsWithin_iff, eventually_nhds_iff]
    rcases eq_or_ne y' y with rfl | hy'ne
    · exact ⟨W, hW, hWopen, hy'W⟩
    · exact ⟨W \ {y}, fun z hz _ => hW z hz.1 hz.2, hWopen.sdiff isClosed_singleton, ⟨hy'W, hy'ne⟩⟩
  rcases isClopen_iff.mp ⟨hUclosed, hUopen⟩ with hU | hU
  · show x ∉ {y : X | f.orderW y = ⊤}
    rw [hU]; exact Set.notMem_empty x
  · exact absurd (hU.ge (Set.mem_univ x₀)) hx₀

end MeromorphicFunction

/-! ## Part 2: the linear system `L(D)`, its dimension `l(D)`, and the isolated RR inputs -/

/-- The complete linear system `L(D)` = meromorphic functions with `div f ≥ −D`, phrased on the
`WithTop ℤ` order (so the zero function, order `⊤`, is automatically a member). A `Submodule ℂ`. -/
noncomputable def linearSystem (D : Divisor X) : Submodule ℂ (MeromorphicFunction X) where
  carrier := {f | ∀ x, (-(D x) : WithTop ℤ) ≤ f.orderW x}
  add_mem' {f g} hf hg := fun x =>
    le_trans (le_min (hf x) (hg x)) (meromorphicOrderAt_add (f.meromorphic x) (g.meromorphic x))
  zero_mem' := fun x => by rw [MeromorphicFunction.orderW_zero]; exact le_top
  smul_mem' c f hf := fun x => by
    rcases eq_or_ne c 0 with hc | hc
    · have h0 : (c • f).orderW x = ⊤ := by
        rw [hc, zero_smul]; exact MeromorphicFunction.orderW_zero x
      rw [h0]; exact le_top
    · rw [show (c • f).orderW x = f.orderW x from
        meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using hc)]
      exact hf x

/-- **Germ-zero "junk" functions.** `MeromorphicFunction.toFun` carries removable-singularity
junk (cf. the `toSphere` note): e.g. the indicator of a single point is a *nonzero* meromorphic
function whose germ is `0` everywhere (`orderW ≡ ⊤`). Such functions lie in EVERY `L(D)`, and
point-indicators are linearly independent, so the naive `finrank ℂ (L(D))` is wrong (the space is
infinite-dimensional, forcing `finrank = 0` for all `D`, which makes RR false). We quotient them
out so `l(D)` is the genuine, finite dimension. -/
noncomputable def germZeroSubmodule : Submodule ℂ (MeromorphicFunction X) where
  carrier := {f | ∀ x, f.orderW x = ⊤}
  add_mem' {f g} hf hg := fun x => by
    have h : min (f.orderW x) (g.orderW x) ≤ (f + g).orderW x :=
      meromorphicOrderAt_add (f.meromorphic x) (g.meromorphic x)
    rw [hf x, hg x, min_self] at h
    exact top_le_iff.mp h
  zero_mem' := fun x => MeromorphicFunction.orderW_zero x
  smul_mem' c f hf := fun x => by
    rcases eq_or_ne c 0 with hc | hc
    · rw [hc, zero_smul]; exact MeromorphicFunction.orderW_zero x
    · rw [show (c • f).orderW x = f.orderW x from
        meromorphicOrderAt_smul_of_ne_zero analyticAt_const (by simpa using hc)]
      exact hf x

/-- `l(D) = dim_ℂ (L(D) ⧸ germ-zero junk)` (Forster's `h⁰(X, O_D)`) — the genuine dimension of
the linear system, with the `toFun`-junk quotiented out. -/
noncomputable def lDim (D : Divisor X) : ℕ :=
  Module.finrank ℂ
    (↥(linearSystem (X := X) D) ⧸ (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) D))

/-- **Isolated input — Riemann–Roch** (Forster Thm 16.9, Serre-dual form). There is a canonical
divisor `K` for which `l(D) − l(K−D) = deg D + 1 − g` for every `D`. This one statement bundles
the existence of a canonical divisor with the RR equality — precisely the classical theorem the
Dolbeault→Serre climb (G2–G4) delivers and that Mathlib lacks. It is *used*, not relocated: the
reductions below (and the genus-zero endgame) are proved outright from it, so discharging this
single `sorry` discharges the headline consumer. -/
theorem exists_riemannRoch_divisor :
    ∃ K : Divisor X, ∀ D : Divisor X,
      (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
        = Divisor.deg X D + 1 - (genus X : ℤ) := sorry

/-- Every principal divisor has degree `0` (Forster Cor. 4.25 / the argument principle). Proved via
the **degree route** (`degDiv_eq_zero`): `deg (div f) = zerosCount f − polesCount f`, and both counts
equal a common proper-map degree, so the difference is `0`. The sole remaining analytic input is the
one honest named sorry `exists_properMapDegree` (in `Jacobians.DegDivResidue`); the RR derivations
below consume this `deg_div`. -/
theorem MeromorphicFunction.deg_div (f : MeromorphicFunction X) :
    Divisor.deg X f.div = 0 := degDiv_eq_zero f

/-! ## Part 3: negative-degree vanishing (explicit finiteness, dim 0)

The first genuine consequence, proved outright from `deg_div` + faithfulness: a linear system of
negative degree is trivial. This is `FiniteDimensional` with `l(D) = 0`, the cleanest explicit
finiteness — and it uses *only* the residue-theorem input, not the general finiteness theorem. -/

/-- `l(D) = 0` when `deg D < 0`. Any `f ∈ L(D)` with nonzero germ would give (by faithfulness) a
divisor `div f ≥ −D` with `deg(div f) = 0 ≥ −deg D > 0`, impossible; so every `f ∈ L(D)` is germ-
zero, the quotient `L(D)/germZero` is trivial, and its dimension is `0`. -/
theorem lDim_eq_zero_of_deg_neg (D : Divisor X) (hD : Divisor.deg X D < 0) :
    lDim (X := X) D = 0 := by
  have hsub : linearSystem (X := X) D ≤ germZeroSubmodule := by
    intro f hf
    by_contra hng
    have hex : ∃ x₀, f.orderW x₀ ≠ ⊤ := by
      by_contra h; push_neg at h; exact hng h
    have hfaith : ∀ z : X, f.orderW z ≠ ⊤ := fun z =>
      MeromorphicFunction.orderW_ne_top_of_exists f hex z
    have hdiv : ∀ x, -(D x) ≤ (f.div : Divisor X) x := by
      intro x
      have hmem : (-(D x) : WithTop ℤ) ≤ f.orderW x := hf x
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (hfaith x)
      rw [← hn] at hmem
      have hdivx : (f.div : Divisor X) x = n := by
        show (f.orderW x).untop₀ = n
        rw [← hn]; rfl
      rw [hdivx]; exact WithTop.coe_le_coe.mp hmem
    have heff : ∀ x, 0 ≤ (f.div + D) x := fun x => by
      rw [Finsupp.add_apply]; linarith [hdiv x]
    have hdeg_eff : (0 : ℤ) ≤ Divisor.deg X (f.div + D) := by
      change (0 : ℤ) ≤ ∑ i ∈ (f.div + D).support, (f.div + D) i
      exact Finset.sum_nonneg fun i _ => heff i
    rw [map_add, MeromorphicFunction.deg_div f] at hdeg_eff
    omega
  rw [lDim]
  have htop : (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) D) = ⊤ :=
    Submodule.comap_subtype_eq_top.mpr hsub
  rw [htop]
  haveI : Subsingleton (↥(linearSystem (X := X) D) ⧸
      (⊤ : Submodule ℂ ↥(linearSystem (X := X) D))) :=
    ⟨fun a b => Quotient.inductionOn₂' a b fun x y =>
      (Submodule.Quotient.eq ⊤).mpr Submodule.mem_top⟩
  exact Module.finrank_zero_of_subsingleton

/-- **A function in `L(0)` is germ-constant** (Liouville). With no pole (`orderW ≥ 0`), the
limit-repair `holoRepr` is holomorphic (`mdifferentiable_holoRepr`), hence constant on the compact
connected `X` (`exists_eq_const_of_compactSpace`); off-center the chart pullback equals that
constant, so `f.toFun` agrees with it on every punctured neighbourhood. This is the repo's
Liouville-for-meromorphic content (`MeromorphicLiouville`), reused — no new analysis. -/
theorem germ_eq_const_of_mem_linearSystem_zero (f : MeromorphicFunction X)
    (hf : f ∈ linearSystem (X := X) 0) : ∃ c : ℂ, ∀ x, ∀ᶠ z in 𝓝[≠] x, f.toFun z = c := by
  have hpos : ∀ x, 0 ≤ f.orderAtPoint x := by
    intro x
    have hx := hf x
    simp only [Finsupp.coe_zero, Pi.zero_apply, neg_zero] at hx
    exact untop₀_nonneg_iff.mpr hx
  obtain ⟨c, hc_const⟩ := (f.mdifferentiable_holoRepr hpos).exists_eq_const_of_compactSpace
  have hc : ∀ y, f.holoRepr y = c := fun y => congrFun hc_const y
  refine ⟨c, fun x => ?_⟩
  set φ := chartAt (H := ℂ) x with hφ
  obtain ⟨V, hVopen, hzV, hFV, hrepr⟩ := f.exists_holoRepr_eq_NFOn x (hpos x)
  have hF_eq : (f.toFun ∘ φ.symm) =ᶠ[𝓝[≠] (φ x)] (fun _ => c) := by
    have h1 := hFV.toMeromorphicNFOn_eq_self_on_nhdsNE hzV
    have h2 : (fun w => toMeromorphicNFOn (f.toFun ∘ φ.symm) V w) =ᶠ[𝓝[≠] (φ x)] (fun _ => c) := by
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (hVopen.mem_nhds hzV)] with w hw
      rw [← hrepr w hw]; exact hc _
    exact h1.symm.trans h2
  exact (MeromorphicFunction.eventually_comp_chart_iff f.toFun x (· = c)).mp hF_eq

/-- `l(0) = 1`: `L(0)/germZero ≅ ℂ` (the constants). Spanned by the class of the constant `1`
(nonzero, since its order is `0 ≠ ⊤`), and every member is germ-constant by Liouville, hence a
scalar multiple of it. Elementary finiteness — uses Liouville, not the wall. -/
theorem lDim_zero_eq_one : lDim (X := X) 0 = 1 := by
  have h1m : IsMeromorphic X (fun _ : X => (1 : ℂ)) := fun x => MeromorphicAt.const 1 _
  have horder1 : ∀ x, MeromorphicFunction.orderW (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X) x = 0 := by
    intro x
    show meromorphicOrderAt ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) _ = 0
    rw [show ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) = (fun _ => (1 : ℂ)) from rfl,
      meromorphicOrderAt_const]
    simp
  have hmem1 : (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X) ∈ linearSystem (X := X) 0 := by
    intro x
    rw [horder1 x]
    simp
  set q : ↥(linearSystem (X := X) 0) := ⟨⟨fun _ => 1, h1m⟩, hmem1⟩ with hq
  rw [lDim]
  refine finrank_eq_one (Submodule.Quotient.mk q) ?_ ?_
  · -- `[const 1] ≠ 0`: else `const 1 ∈ germZero`, but its order is `0 ≠ ⊤`.
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    intro hmem
    obtain ⟨x⟩ := (inferInstance : Nonempty X)
    have : MeromorphicFunction.orderW (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X) x = ⊤ :=
      (Submodule.mem_comap.mp hmem) x
    rw [horder1 x] at this
    exact (by decide : (0 : WithTop ℤ) ≠ ⊤) this
  · -- surjectivity: every class is `c • [const 1]` for the germ-constant value `c`.
    intro w
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    obtain ⟨c, hgc⟩ := germ_eq_const_of_mem_linearSystem_zero g.1 g.2
    refine ⟨c, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
    show ((c • q - g : ↥(linearSystem (X := X) 0)) : MeromorphicFunction X) ∈ germZeroSubmodule
    intro x
    rw [MeromorphicFunction.orderW_eq_top_iff]
    filter_upwards [hgc x] with z hz
    show c • (1 : ℂ) - g.1.toFun z = 0
    rw [hz]; simp

/-! ## Part 4: standard RR consequences (pure arithmetic from RR + `l(0)=1`) -/

/-- `l(K) = g`, from Riemann–Roch at `D = 0` (and `l(0) = 1`). -/
theorem lDim_canonical_eq_genus {K : Divisor X}
    (hrr : ∀ D : Divisor X, (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
      = Divisor.deg X D + 1 - (genus X : ℤ)) : lDim (X := X) K = genus X := by
  have h := hrr 0
  rw [sub_zero, Divisor.deg_zero, lDim_zero_eq_one] at h
  omega

/-- `deg K = 2g − 2`, from Riemann–Roch at `D = K`. -/
theorem deg_canonical {K : Divisor X}
    (hrr : ∀ D : Divisor X, (lDim (X := X) D : ℤ) - (lDim (X := X) (K - D) : ℤ)
      = Divisor.deg X D + 1 - (genus X : ℤ)) : Divisor.deg X K = 2 * (genus X : ℤ) - 2 := by
  have h := hrr K
  rw [sub_self, lDim_zero_eq_one, lDim_canonical_eq_genus hrr] at h
  omega

/-! ## Part 5: the meet-in-the-middle — discharge the consumer from RR -/

/-- **Touch point.** `genus X = 0` + Riemann–Roch ⟹ a meromorphic function with a single simple
pole. RR at `D = P` gives `l(P) = 2 > 1 = l(0)`, so `L(P)/germZero` is not spanned by the constant
class; a member outside that span is not germ-constant, hence (by Liouville's contrapositive
`germ_eq_const_of_mem_linearSystem_zero`) has a pole, necessarily a *simple* pole at `P` — the only
pole `L(P)` permits — and by faithfulness its order is finite everywhere. This discharges
`exists_singleSimplePole_of_genus_zero` modulo `{riemannRoch, deg_div}`. -/
theorem exists_singleSimplePole_of_genus_zero_of_rr (hg : genus X = 0) :
    ∃ (P : X) (f : MeromorphicFunction X), f.HasSingleSimplePole P := by
  obtain ⟨P⟩ := (inferInstance : Nonempty X)
  obtain ⟨K, hrr⟩ := exists_riemannRoch_divisor (X := X)
  refine ⟨P, ?_⟩
  set DP : Divisor X := Finsupp.single P 1 with hDP
  have hdegDP : Divisor.deg X DP = 1 := by rw [hDP, Divisor.deg_single]
  -- `l(P) = 2`.
  have hlKDP : lDim (X := X) (K - DP) = 0 := by
    apply lDim_eq_zero_of_deg_neg
    rw [Divisor.deg_sub, deg_canonical hrr, hdegDP, hg]; norm_num
  have hlDP : lDim (X := X) DP = 2 := by
    have h := hrr DP; rw [hlKDP, hdegDP, hg] at h; omega
  -- The constant `1` as a member of `L(P)`, with order `0`.
  have h1m : IsMeromorphic X (fun _ : X => (1 : ℂ)) := fun x => MeromorphicAt.const 1 _
  have horder1 : ∀ x, (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X).orderW x = 0 := by
    intro x
    show meromorphicOrderAt ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) _ = 0
    rw [show ((fun _ : X => (1 : ℂ)) ∘ (chartAt (H := ℂ) x).symm) = (fun _ => (1 : ℂ)) from rfl,
      meromorphicOrderAt_const]; simp
  have hmem1 : (⟨fun _ => 1, h1m⟩ : MeromorphicFunction X) ∈ linearSystem (X := X) DP := by
    intro x; rw [horder1 x]
    have hge : (0 : ℤ) ≤ DP x := by
      classical rw [hDP, Finsupp.single_apply]; split <;> norm_num
    exact_mod_cast neg_nonpos.mpr hge
  set q1 : ↥(linearSystem (X := X) DP) := ⟨⟨fun _ => 1, h1m⟩, hmem1⟩ with hq1
  -- Work in the quotient `Q := L(P)/germZero`, of dimension `l(P) = 2`; pin its submodule once.
  set c1 : ↥(linearSystem (X := X) DP) ⧸
      (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) DP) :=
    Submodule.Quotient.mk q1 with hc1
  have hfr : Module.finrank ℂ (↥(linearSystem (X := X) DP) ⧸
      (germZeroSubmodule (X := X)).submoduleOf (linearSystem (X := X) DP)) = 2 := hlDP
  -- `[1] ≠ 0`, so `span {[1]}` has dimension 1 < 2 = `l(P)`, hence is not all of `L(P)/germZero`.
  have hq1ne : c1 ≠ 0 := by
    rw [hc1, Ne, Submodule.Quotient.mk_eq_zero]
    intro hmem
    have h := (Submodule.mem_comap.mp hmem) P
    have hP0 : (↑q1 : MeromorphicFunction X).orderW P = 0 := horder1 P
    have hbad : (0 : WithTop ℤ) = ⊤ := by rw [← hP0]; exact h
    exact absurd hbad (by simp)
  have hspan_ne : Submodule.span ℂ {c1} ≠ ⊤ := by
    intro htop
    have h1 := finrank_span_singleton (K := ℂ) hq1ne
    rw [htop, finrank_top, hfr] at h1
    exact absurd h1 (by norm_num)
  obtain ⟨v, hv⟩ : ∃ v, v ∉ Submodule.span ℂ {c1} := by
    by_contra hall; push_neg at hall; exact hspan_ne (Submodule.eq_top_iff'.mpr hall)
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  -- `f` is not germ-constant (else its class would lie in `span {[1]}`).
  have hnc : ¬ ∃ c, ∀ x, ∀ᶠ z in 𝓝[≠] x, (f : MeromorphicFunction X).toFun z = c := by
    rintro ⟨c, hgc⟩
    apply hv
    have hfc : Submodule.Quotient.mk f = c • c1 := by
      rw [hc1, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
      show ((f - c • q1 : ↥(linearSystem (X := X) DP)) : MeromorphicFunction X) ∈ germZeroSubmodule
      intro x
      rw [MeromorphicFunction.orderW_eq_top_iff]
      filter_upwards [hgc x] with z hz
      show (f : MeromorphicFunction X).toFun z - c • (1 : ℂ) = 0
      rw [hz]; simp
    rw [hfc]; exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self _)
  -- hence `f` has a pole, located at `P` with order exactly `-1`.
  have hpole : ∃ x₀, (f : MeromorphicFunction X).orderW x₀ < 0 := by
    by_contra hno; push_neg at hno
    exact hnc (germ_eq_const_of_mem_linearSystem_zero (f : MeromorphicFunction X) (fun x => hno x))
  obtain ⟨x₀, hx₀⟩ := hpole
  have hx₀P : x₀ = P := by
    by_contra hne
    have hmemf := f.2 x₀
    have hDP0 : DP x₀ = 0 := by
      classical rw [hDP, Finsupp.single_apply, if_neg (fun h : P = x₀ => hne h.symm)]
    rw [hDP0] at hmemf
    have hge : (0 : WithTop ℤ) ≤ (f : MeromorphicFunction X).orderW x₀ := by simpa using hmemf
    exact absurd (lt_of_le_of_lt hge hx₀) (lt_irrefl _)
  rw [hx₀P] at hx₀
  have hPval : (f : MeromorphicFunction X).orderW P = -1 := by
    have hmemf := f.2 P
    have hDP1 : DP P = 1 := by rw [hDP, Finsupp.single_eq_same]
    rw [hDP1] at hmemf
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (lt_of_lt_of_le hx₀ le_top).ne
    rw [← hn] at hmemf hx₀ ⊢
    have hn1 : (-1 : ℤ) ≤ n := by exact_mod_cast hmemf
    have hn2 : n < 0 := by exact_mod_cast hx₀
    rw [show n = (-1 : ℤ) from by omega]; simp
  refine ⟨(f : MeromorphicFunction X), ?_, ?_⟩
  · show ((f : MeromorphicFunction X).orderW P).untop₀ = -1
    rw [hPval]; rfl
  · intro x hx
    show 0 ≤ ((f : MeromorphicFunction X).orderW x).untop₀
    have hmemf := f.2 x
    have hDP0 : DP x = 0 := by
      classical rw [hDP, Finsupp.single_apply, if_neg (fun h : P = x => hx h.symm)]
    rw [hDP0] at hmemf
    rw [untop₀_nonneg_iff]; simpa using hmemf

end Jacobians
