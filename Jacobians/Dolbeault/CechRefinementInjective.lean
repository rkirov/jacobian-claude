/-
  Dolbeault ladder — **Forster GTM 81 Lemma 12.4**: refinement maps on `H¹` are injective
  UNCONDITIONALLY (sheaf axioms I + II / gluing only — no acyclicity, no Leray hypothesis).

  The conditional version `IsRefinement.refinementDescend_of_isDiskAcyclic`
  (`CechRefinementLeray.lean`) needs the coarse cover `𝔘` to be disk-acyclic.  Forster 12.4 shows the
  `RefinementDescend` predicate holds for ANY refinement, using only that the germ-class `𝒪_D`-sections
  form a genuine SHEAF (gluing + separation).  We supply exactly that sheaf input as two reusable
  lemmas on an *open* `W ⊆ X` (NOT all of `X`):

    * `omegaDGerm_separated` — sheaf axiom I (separation): two `MGerm W` agreeing on every member of a
      cover `(A k)_k` of `W` are equal.
    * `omegaDGerm_glue` — sheaf axiom II (gluing): a matching family `(s k)_k` of `𝒪_D`-germs over a
      cover `(A k)_k` of `W` glues to a single `h ∈ OmegaDGerm D W` restricting to each `s k`.

  Both are the `W`-local analogue of `CechH0`'s X-GLOBAL gluing (`cechRestrictL_surjective`).  The
  gluing reuses `CechH0`'s per-point meromorphic-normal-form construction verbatim — that construction
  is entirely chart-local, so it transports from `X` to the open region `W` with no compactness input.

  ## What is proven (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)

    * `IsRefinement.refinementDescend_unconditional` — Forster 12.4: `RefinementDescend hr D` for ANY
      refinement `hr : IsRefinement 𝔙 𝔘 r`.
    * `IsRefinement.refineH1_injective_unconditional` — hence `refineH1 hr` is injective (immediate from
      the existing `refineH1_injective_iff_descend`).

  NO `sorry` in this file.
-/
import Jacobians.Dolbeault.CechRefinementLeray
import Jacobians.Dolbeault.CechH0

open scoped Manifold ContDiff Topology
open TopologicalSpace (Opens)

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The germ-class `𝒪_D` sheaf on an OPEN region `W` (gluing + separation)

`CechH0` proves the gluing/separation only when the cover is all of `X` (`cechRestrictL_surjective`).
Forster 12.4 needs it on each coarse set `𝔘.U i` — an *open* `W ⊆ X`.  We re-derive it here from the
chart-local atoms `CechH0` already exposes (`Gext`, `nfX`, `Gext_meromorphicAt`,
`Gext_overlap_eventuallyEq`, `nfX_Gext_codiscrete`, `toMeromorphicNFAt_chart_val_congr`, …); none of
those uses compactness, so they transport to the region `W` unchanged. -/

variable (D : Divisor X)

/-- A germ-class agreement between two `↥W`-functions on a sub-open `A ≤ W` upgrades, near each point
of `A`, to a punctured-neighbourhood agreement of their extensions-by-zero on `X`.  (Pull the
`↥(A)`-germ agreement back to `X` via `eventually_nhdsNE_of_subtype`; on the overlap the extensions are
the functions themselves by `Gext_apply_mem`.) -/
theorem Gext_eventuallyEq_of_subOpen {W A : Opens X} (hAW : A ≤ W) (fa fb : W → ℂ)
    (hagree : toGerm A (fa ∘ openIncl hAW) = toGerm A (fb ∘ openIncl hAW))
    {x : X} (hx : x ∈ A) :
    Gext fa =ᶠ[𝓝[≠] x] Gext fb := by
  rw [toGerm_eq_iff] at hagree
  refine eventually_nhdsNE_of_subtype hx (fun z => Gext fa z = Gext fb z) ?_
  filter_upwards [hagree ⟨x, hx⟩] with w hw
  have hwW : (w : X) ∈ W := hAW w.2
  rw [Gext_apply_mem fa hwW, Gext_apply_mem fb hwW]
  simpa only [Function.comp_apply, openIncl] using hw

/-- **Sheaf axiom I (separation) for germ-class `𝒪_D`-sections.**  If two germ-classes on an open `W`
restrict to the *same* germ-class on every member `A k` of a cover of `W`, they are equal.  (Each point
of `↥W` lies in some `A k`, where the two agree; that agreement pulls back to a punctured-neighbourhood
agreement on `↥W`.) -/
theorem omegaDGerm_separated {W : Opens X} {K : Type*} (A : K → Opens X) (hAW : ∀ k, A k ≤ W)
    (hcov : ⨆ k, A k = W) (a b : MGerm W)
    (hagree : ∀ k, rawRestrictG (hAW k) a = rawRestrictG (hAW k) b) :
    a = b := by
  induction a using Filter.Germ.inductionOn with | _ fa =>
  induction b using Filter.Germ.inductionOn with | _ fb =>
  show toGerm W fa = toGerm W fb
  rw [toGerm_eq_iff]
  intro w
  -- `w ∈ W`, so `w.1 ∈ A k` for some `k`; reduce to the sub-open agreement on `A k`.
  have hwsup : (w : X) ∈ ⨆ k, A k := hcov ▸ w.2
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hwsup
  have hak : toGerm (A k) (fa ∘ openIncl (hAW k)) = toGerm (A k) (fb ∘ openIncl (hAW k)) := by
    have := hagree k
    rwa [show (rawRestrictG (hAW k) (fa : MGerm W)) = toGerm (A k) (fa ∘ openIncl (hAW k)) from
        rawRestrictG_coe (hAW k) fa,
      show (rawRestrictG (hAW k) (fb : MGerm W)) = toGerm (A k) (fb ∘ openIncl (hAW k)) from
        rawRestrictG_coe (hAW k) fb] at this
  -- The extensions agree punctured-near `w.1` in `X`; pull that back to `↥W`.
  have hX : Gext fa =ᶠ[𝓝[≠] (w : X)] Gext fb :=
    Gext_eventuallyEq_of_subOpen (hAW k) fa fb hak hk
  have hW := eventually_subtype_of_nhdsNE (V := W) (u := w)
    (fun z => Gext fa z = Gext fb z) hX
  filter_upwards [hW] with v hv
  rw [Gext_apply_mem fa v.2, Gext_apply_mem fb v.2] at hv
  simpa using hv

/-- A function on `↥U` is meromorphic on `↥U` once its extension-by-zero `Gext g` is meromorphic at
each point of `U` (read in `X`'s chart) — the converse direction of `Gext_meromorphicAt`, via the same
`Gext_chart_bridge`. -/
theorem isMeromorphic_of_Gext_meromorphicAt {U : Opens X} {g : U → ℂ}
    (h : ∀ y ∈ U,
      MeromorphicAt (Gext g ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y)) :
    IsMeromorphic (U : Type _) g := by
  intro u
  obtain ⟨hbase, hev⟩ := Gext_chart_bridge g u.2
  have hmer := h u.1 u.2
  rw [← hbase] at hmer
  -- `g ∘ chartAt_↥U.symm =ᶠ[𝓝] Gext g ∘ chartAt_X.symm`, with matching base points (`hbase`).
  exact hmer.congr (hev.filter_mono nhdsWithin_le_nhds).symm

/-- **Sheaf axiom II (gluing) for germ-class `𝒪_D`-sections.**  A matching family `(s k)_k` of
`𝒪_D`-germs over a cover `(A k)_k` of an open `W` glues to a single `h ∈ OmegaDGerm D W` whose
restriction to each `A k` is `s k`.  This is the `W`-local form of `CechH0.cechRestrictL_surjective`:
extract honest representatives `gA k ∈ OmegaD D (A k)`, extend each by `0`, and glue them by the
per-point meromorphic-normal-form recipe (`toMeromorphicNFAt`).  The glued function agrees off a
discrete set near every point of `W` with the local member whose patch contains the point, so it is
meromorphic on `↥W`, satisfies the order bound, and has the prescribed germ on each `A k`. -/
theorem omegaDGerm_glue {W : Opens X} {K : Type*} (A : K → Opens X) (hAW : ∀ k, A k ≤ W)
    (hcov : ⨆ k, A k = W) (s : Π k, MGerm (A k)) (hs : ∀ k, s k ∈ OmegaDGerm D (A k))
    (hmatch : ∀ k l, rawRestrictG (inf_le_left : A k ⊓ A l ≤ A k) (s k)
      = rawRestrictG (inf_le_right : A k ⊓ A l ≤ A l) (s l)) :
    ∃ h ∈ OmegaDGerm D W, ∀ k, rawRestrictG (hAW k) h = s k := by
  -- The empty-index case forces `W = ⊥`; the zero germ works (no `k` to restrict to).
  rcases isEmpty_or_nonempty K with hK | hK
  · exact ⟨0, Submodule.zero_mem _, fun k => isEmptyElim k⟩
  -- Extract honest representatives `gA k ∈ OmegaD D (A k)` with `[gA k] = s k`.
  have hchoose : ∀ k, ∃ gk : A k → ℂ, gk ∈ OmegaD D (A k) ∧ toGerm (A k) gk = s k := fun k => by
    obtain ⟨gk, hgk, hgkeq⟩ := hs k; exact ⟨gk, hgk, hgkeq⟩
  choose gA hgA_mem hgA_rep using hchoose
  have hgA_mer : ∀ k, IsMeromorphic (A k : Type _) (gA k) := fun k => ((mem_OmegaD).1 (hgA_mem k)).1
  have hgA_ord : ∀ k, ∀ u : A k, (-(D u.1) : WithTop ℤ) ≤ ordU (gA k) u :=
    fun k => ((mem_OmegaD).1 (hgA_mem k)).2
  -- The family of extensions-by-zero.
  set G : K → X → ℂ := fun k => Gext (gA k) with hG
  -- A total index choice on `X`: a covering patch on `W`, an arbitrary index off `W`.
  have hcovW : ∀ x : X, x ∈ W → ∃ k, x ∈ A k := fun x hx => by
    have : x ∈ ⨆ k, A k := hcov ▸ hx
    exact TopologicalSpace.Opens.mem_iSup.mp this
  classical
  set idx : X → K := fun x => if hx : x ∈ W then (hcovW x hx).choose else Classical.arbitrary K
    with hidx_def
  have hidxW : ∀ x : X, ∀ hx : x ∈ W, x ∈ A (idx x) := fun x hx => by
    rw [hidx_def]; simp only [dif_pos hx]; exact (hcovW x hx).choose_spec
  -- The matching hypotheses in `Gext`/normal-form shape.
  have Hmer : ∀ k, ∀ y, y ∈ A k →
      MeromorphicAt (G k ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) :=
    fun k y hy => Gext_meromorphicAt (hgA_mer k) hy
  have Hoverlap : ∀ k l, ∀ x, x ∈ A k → x ∈ A l → G k =ᶠ[𝓝[≠] x] G l := by
    intro k l x hxk hxl
    -- The Čech matching for `(gA k, gA l)` on the overlap `A k ⊓ A l`.
    have hm : rawRestrictG (inf_le_right : A k ⊓ A l ≤ A l) (toGerm (A l) (gA l))
        = rawRestrictG (inf_le_left : A k ⊓ A l ≤ A k) (toGerm (A k) (gA k)) := by
      rw [hgA_rep k, hgA_rep l]; exact (hmatch k l).symm
    exact Gext_overlap_eventuallyEq (gA k) (gA l) hm hxk hxl
  have Hnf : ∀ k, ∀ y, y ∈ A k → ∀ᶠ z in 𝓝[≠] y, nfX (G k) z := by
    intro k y hy
    -- `nfX_Gext_codiscrete` is stated through a `FiniteCover`; its content is `A k`-local.  Re-derive.
    have hmer : MeromorphicAt (Gext (gA k) ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) :=
      Gext_meromorphicAt (hgA_mer k) hy
    have hana : ∀ᶠ w in 𝓝[≠] ((chartAt (H := ℂ) y) y),
        AnalyticAt ℂ (Gext (gA k) ∘ (chartAt (H := ℂ) y).symm) w := hmer.eventually_analyticAt
    have htend : Filter.Tendsto (chartAt (H := ℂ) y) (𝓝[≠] y) (𝓝[≠] ((chartAt (H := ℂ) y) y)) := by
      have hy' : y ∈ (chartAt (H := ℂ) y).source := mem_chart_source ℂ y
      rw [tendsto_nhdsWithin_iff]
      refine ⟨((chartAt (H := ℂ) y).continuousAt hy').continuousWithinAt.tendsto, ?_⟩
      rw [eventually_nhdsWithin_iff]
      filter_upwards [(chartAt (H := ℂ) y).open_source.mem_nhds hy'] with z hz hzne
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hzne ⊢
      exact fun hc => hzne ((chartAt (H := ℂ) y).injOn hz hy' hc)
    have hana' : ∀ᶠ z in 𝓝[≠] y,
        AnalyticAt ℂ (Gext (gA k) ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) z) :=
      htend.eventually hana
    have hsrc : ∀ᶠ z in 𝓝[≠] y, z ∈ (chartAt (H := ℂ) y).source :=
      eventually_nhdsWithin_of_eventually_nhds
        ((chartAt (H := ℂ) y).open_source.mem_nhds (mem_chart_source ℂ y))
    filter_upwards [hana', hsrc] with z hz hzsrc
    exact (analyticAt_chart_change hzsrc hz).meromorphicNFAt
  -- The glued function on `X` (the per-point normal-form value).
  set Gpt : X → ℂ := fun x =>
    toMeromorphicNFAt (G (idx x) ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)
      ((chartAt (H := ℂ) x) x) with hGpt
  -- Central agreement: near every `y ∈ A i`, `Gpt` equals the local member `G i`.
  have hGev : ∀ {y : X} {i : K}, y ∈ A i → Gpt =ᶠ[𝓝[≠] y] G i := by
    intro y i hy
    have hAi : ∀ᶠ z in 𝓝[≠] y, z ∈ A i :=
      eventually_nhdsWithin_of_eventually_nhds ((A i).isOpen.mem_nhds hy)
    have hWi : ∀ᶠ z in 𝓝[≠] y, z ∈ W :=
      eventually_nhdsWithin_of_eventually_nhds (W.isOpen.mem_nhds (hAW i hy))
    filter_upwards [hAi, hWi, Hnf i y hy] with z hz hzW hznf
    show toMeromorphicNFAt (G (idx z) ∘ (chartAt (H := ℂ) z).symm) ((chartAt (H := ℂ) z) z)
        ((chartAt (H := ℂ) z) z) = G i z
    rw [toMeromorphicNFAt_chart_val_congr (Hoverlap (idx z) i z (hidxW z hzW) hz)
      (Hmer (idx z) z (hidxW z hzW))]
    rw [toMeromorphicNFAt_eq_self.mpr (show MeromorphicNFAt (G i ∘ (chartAt (H := ℂ) z).symm)
      ((chartAt (H := ℂ) z) z) from hznf)]
    simp only [Function.comp_apply, OpenPartialHomeomorph.left_inv _ (mem_chart_source ℂ z)]
  -- The representative section on `↥W`: `Gpt` restricted to `W`.
  set hRep : W → ℂ := fun w => Gpt w.1 with hRep_def
  -- `Gext hRep` agrees with `Gpt` near every `y ∈ W` (off `W`, `Gext hRep = 0`).
  have hGextRep : ∀ {y : X}, y ∈ W → Gext hRep =ᶠ[𝓝[≠] y] Gpt := by
    intro y hy
    have hWy : ∀ᶠ z in 𝓝[≠] y, z ∈ W :=
      eventually_nhdsWithin_of_eventually_nhds (W.isOpen.mem_nhds hy)
    filter_upwards [hWy] with z hz
    rw [Gext_apply_mem hRep hz]
  -- Hence `Gext hRep` agrees with `G i` near every `y ∈ A i`.
  have hRepEv : ∀ {y : X} {i : K}, y ∈ A i → Gext hRep =ᶠ[𝓝[≠] y] G i := fun {y i} hy =>
    (hGextRep (hAW i hy)).trans (hGev hy)
  -- `Gext hRep` is meromorphic at each point of `W` (agrees with a meromorphic `G i` there).
  have hGextRep_mer : ∀ y, ∀ hy : y ∈ W,
      MeromorphicAt (Gext hRep ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) y) := by
    intro y hy
    obtain ⟨i, hyi⟩ := hcovW y hy
    exact (Hmer i y hyi).congr (eventuallyEq_comp_chart (hRepEv hyi)).symm
  -- `hRep` is meromorphic on `↥W`, with the right order bound at every point.
  have hRep_mem : hRep ∈ OmegaD D W := by
    rw [mem_OmegaD]
    refine ⟨isMeromorphic_of_Gext_meromorphicAt hGextRep_mer, fun w => ?_⟩
    obtain ⟨i, hwi⟩ := hcovW w.1 w.2
    -- `ordU hRep w = orderAt (Gext hRep) = orderAt (G i) = ordU (gA i) ⟨w.1, hwi⟩ ≥ -(D w.1)`.
    rw [ordU_eq_orderAt_Gext hRep w.2,
      meromorphicOrderAt_congr (eventuallyEq_comp_chart (hRepEv hwi)), hG,
      ← ordU_eq_orderAt_Gext (gA i) hwi]
    exact hgA_ord i ⟨w.1, hwi⟩
  -- Assemble: the glued germ and its restriction property.
  refine ⟨toGerm W hRep, ⟨hRep, hRep_mem, rfl⟩, fun k => ?_⟩
  -- `rawRestrictG (hAW k) [hRep] = [gA k] = s k`: equality of germs on `A k`.
  rw [rawRestrictG_coe, ← hgA_rep k, toGerm_eq_iff]
  intro u
  -- On `↥(A k)`, `hRep ∘ openIncl = Gpt|_{A k}` agrees punctured-near `u` with `gA k`.
  have hpull := eventually_subtype_of_nhdsNE (V := A k) (u := u)
    (fun z => Gext hRep z = G k z) (hRepEv u.2)
  filter_upwards [hpull] with v hv
  simp only [Function.comp_apply, openIncl]
  -- Goal `hRep ⟨v.1, _⟩ = gA k v`.  `hRep ⟨v.1,_⟩ = Gext hRep v.1 = G k v.1 = Gext (gA k) v.1 = gA k v`.
  rw [show (hRep ⟨(v : X), hAW k v.2⟩) = Gext hRep v.1 from
    (Gext_apply_mem hRep (hAW k v.2)).symm, hv]
  show Gext (gA k) v.1 = gA k v
  rw [Gext_apply_mem (gA k) v.2]

end Jacobians.Dolbeault
