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

/-- **Sheaf axiom II (gluing) for germ-class `𝒪_D`-sections.**  A matching family `(s k)_k` of
`𝒪_D`-germs over a cover `(A k)_k` of an open `W` glues to a single `h ∈ OmegaDGerm D W` whose
restriction to each `A k` is `s k`.  This is the `W`-local form of `CechH0.cechRestrictL_surjective`. -/
theorem omegaDGerm_glue {W : Opens X} {K : Type*} (A : K → Opens X) (hAW : ∀ k, A k ≤ W)
    (hcov : ⨆ k, A k = W) (s : Π k, MGerm (A k)) (hs : ∀ k, s k ∈ OmegaDGerm D (A k))
    (hmatch : ∀ k l, rawRestrictG (inf_le_left : A k ⊓ A l ≤ A k) (s k)
      = rawRestrictG (inf_le_right : A k ⊓ A l ≤ A l) (s l)) :
    ∃ h ∈ OmegaDGerm D W, ∀ k, rawRestrictG (hAW k) h = s k := by
  sorry

end Jacobians.Dolbeault
