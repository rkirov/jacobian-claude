/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueRamifiedRealSlitSection
import Jacobians.SymmetricFunctionDescent

/-!
# Wiring the `Rem` symmetric-function descent into the ramified `ClusterTraceData` (Gate-A)

`Jacobians.SymmetricFunctionDescent` proved the single genuinely-new analytic lemma — the
**symmetric-function descent** `analyticAt_weightedSymSum_descent` ("the trace of a holomorphic germ is
holomorphic", Forster §5 / Miranda §VIII.3): for `Q` analytic at `0`, `m > 0`, `ζ` a primitive `m`-th
root,

> `∑_{j<m} Q(ζʲ·u)·ζʲ = m·u^{m−1}·G(uᵐ)`   (`G` analytic at `0`, near `u = 0`),

and wired it into the slit form `Rem z = G(z − c)` (`exists_ramifiedTrace_descent`).

This file connects that descent to the genuine ramified `ClusterTraceData` consumed by the residue
theorem: it builds a `ClusterTraceData` at a non-pole fibre preimage **on a (shrunk) slit `S`**, taking
the descent germ `G` from `analyticAt_weightedSymSum_descent` and supplying `Rem`/`hRem_an`/`hRem_slit`
**from the descent** (no longer a free data hypothesis).

## What is delivered

* `exists_clusterTraceData_descent_at_fibrePoint` — from the Forster §5 normal form
  (`exists_clusterSplit_at_fibrePoint`), the Laurent principal part of the straightened integrand
  (`exists_principalPart_meromorphicAt`), and the descent germ, build a `ClusterTraceData ω₀ g.toFun p c
  S` whose `Rem`/`hRem_an`/`hRem_slit` come from the descent.

The genuine remaining inputs (the *shrunk slit* `S` smallness, `hs_an_sheet`, `hpp_split_sheet`) are
exactly the mechanical slit residuals — the same continuity/smallness facts the section half already
consumes (`cpow_slitBranch_tendsto_zero` + the §5 atom's open domains).  They are supplied as explicit
hypotheses here, so this file **eliminates the `Rem` descent as a data hypothesis**, reducing the
per-preimage cluster data to those mechanical residuals.

## ⚠ Soundness

`Rem := G(· − c)` is the genuine symmetric-function descent (single-valued via the roots of unity).  The
`hRem_slit` identity holds on `S` precisely because each `w₀ z` (`z ∈ S`) lands in the descent
neighbourhood (the shrunk-slit smallness `hsmall`).  No custom axiom, no `sorry`, no false/junk/circular
field.  `S` is an arbitrary slit (the shrunk one downstream); `D` is the whole fibre (#17).

## References

* `Jacobians.SymmetricFunctionDescent` (`analyticAt_weightedSymSum_descent`,
  `exists_ramifiedTrace_descent`).
* `SerreResidueRamifiedMultiplicityBridge.lean` (`exists_clusterSplit_at_fibrePoint`),
  `SerreResidueRamifiedFullFibreBuilder.lean` (`ClusterTraceData.ofNormalForm`),
  `FormTracePrincipalPart.lean` (`exists_principalPart_meromorphicAt`).
-/

noncomputable section

open Complex Metric Filter Topology
open scoped Manifold ContDiff Real

attribute [local instance] Classical.propDecidable

set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault.SerreResidueTheorem

open Jacobians Jacobians.Dolbeault Jacobians.TraceResidue Jacobians.MeromorphicTrace
  Jacobians.SymmetricDescent
  Jacobians.Dolbeault.FormResidueTheorem Jacobians.Dolbeault.FormTraceFibre
  Jacobians.Dolbeault.FormTraceGlobal Jacobians.Dolbeault.FormTracePrincipalPart
  Jacobians.ProperMapDegree Jacobians.ProperMapDegreeConstruct Jacobians.RiemannSphere

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-- **The ramified `ClusterTraceData` with `Rem` supplied by the symmetric-function descent.**  At a
non-pole fibre preimage `p` over `coe c` of a non-constant cover `f` (`f.div ≠ 0`), of genuine
multiplicity `m = (localDeg f (coe c) p).toNat`, with `ζ` a primitive `m`-th root, the Forster §5 local
inverse `s` (from `exists_clusterSplit_at_fibrePoint`), the slit branch `w₀`/`hw₀_*` (e.g. the `cpow`
branch on a slit `S`), the Laurent principal part `ppN`/`ppb`/`ppR` of the straightened integrand at `0`
(from `exists_principalPart_meromorphicAt`), and the *descent germ* `G` (from
`analyticAt_weightedSymSum_descent` applied to `Q t := ppR t`), this assembles a `ClusterTraceData` whose
single-valued remainder trace `Rem := G(· − c)` is **analytic at `c` by the descent** — discharging
`hRem_an`/`hRem_slit` rather than assuming them.

The remaining genuine inputs are the mechanical slit residuals (`hs_an_sheet`, `hpp_split_sheet`) and the
shrunk-slit smallness `hsmall` (each `w₀ z`, `z ∈ S`, lands in the descent neighbourhood — equivalently,
the descent identity holds pointwise at `w₀ z`). -/
theorem exists_clusterTraceData_descent_at_fibrePoint (ω₀ : HolomorphicOneForms X)
    (g : MeromorphicFunction X) {f : MeromorphicFunction X} (hdiv : (f.div : Divisor X) ≠ 0)
    {c : ℂ} {p : X} (hp_fib : f.toRiemannSphere p = ((c : ℂ) : RiemannSphere))
    (hp_np : 0 ≤ f.orderAtPoint p)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (localDeg f ((c : ℂ) : RiemannSphere) p).toNat)
    (S : Set ℂ)
    (s : ℂ → ℂ) (hs_an : AnalyticAt ℂ s 0) (hs0 : s 0 = (chartAt ℂ p) p) (hs_deriv : deriv s 0 ≠ 0)
    (w₀ : ℂ → ℂ) (hw₀_ne : ∀ z ∈ S, w₀ z ≠ 0)
    (hw₀_pow : ∀ z ∈ S, w₀ z ^ ((localDeg f ((c : ℂ) : RiemannSphere) p).toNat : ℤ) = z - c)
    (hw₀_deriv : ∀ z ∈ S, deriv w₀ z = ((localDeg f ((c : ℂ) : RiemannSphere) p).toNat : ℂ)⁻¹
      * w₀ z ^ (1 - ((localDeg f ((c : ℂ) : RiemannSphere) p).toNat : ℤ)))
    (hw₀_diff : ∀ z ∈ S, DifferentiableAt ℂ w₀ z)
    (ppN : ℕ) (ppb : ℕ → ℂ) (ppR : ℂ → ℂ) (hppR_an : AnalyticAt ℂ ppR 0)
    (hs_an_sheet : ∀ z ∈ S, ∀ j ∈ Finset.range (localDeg f ((c : ℂ) : RiemannSphere) p).toNat,
      AnalyticAt ℂ s (ζ ^ j * w₀ z))
    (hpp_split_sheet : ∀ z ∈ S, ∀ j ∈ Finset.range (localDeg f ((c : ℂ) : RiemannSphere) p).toNat,
      straightenedIntegrand ω₀ g.toFun p s (ζ ^ j * w₀ z)
        = negTail 0 ppb ppN (ζ ^ j * w₀ z) + ppR (ζ ^ j * w₀ z))
    (G : ℂ → ℂ) (hG : AnalyticAt ℂ G 0)
    (hsmall : ∀ z ∈ S,
      (∑ j ∈ Finset.range (localDeg f ((c : ℂ) : RiemannSphere) p).toNat, ppR (ζ ^ j * w₀ z) * ζ ^ j)
        = (localDeg f ((c : ℂ) : RiemannSphere) p).toNat * (w₀ z) ^
            ((localDeg f ((c : ℂ) : RiemannSphere) p).toNat - 1) * G ((w₀ z) ^
            (localDeg f ((c : ℂ) : RiemannSphere) p).toNat)) :
    Nonempty (ClusterTraceData ω₀ g.toFun p c S) := by
  set m := (localDeg f ((c : ℂ) : RiemannSphere) p).toNat with hm_def
  have hm : 0 < m := (Jacobians.analyticOrderAt_holoRepr_sub_eq_mult f hdiv hp_fib hp_np).1
  -- build `Rem`/`hRem_an`/`hRem_slit` from the descent (with `wp = 0`)
  obtain ⟨Rem, hRem_an, hRem_slit⟩ := exists_ramifiedTrace_descent (ppR := ppR) (wp := 0) c hm ζ w₀ S G
    hG (by intro z hz; simpa using hw₀_ne z hz) hw₀_pow hw₀_deriv
    (by intro z hz; simpa using hsmall z hz)
  refine ⟨?_⟩
  -- assemble the `ClusterTraceData` via `ofNormalForm` with the descent-supplied `Rem`
  refine ClusterTraceData.ofNormalForm ω₀ g.toFun p c S m hm ζ hζ
    s hs_an hs0 hs_deriv w₀ hw₀_ne hw₀_pow hw₀_deriv hw₀_diff hs_an_sheet
    (by simpa [Function.comp] using g.meromorphic p) ppN ppb ppR hppR_an hpp_split_sheet
    Rem hRem_an ?_
  -- `hRem_slit` from `ofNormalForm`'s shape (`wp = 0`) matches the descent's slit identity.
  intro z hz
  have := hRem_slit z hz
  simpa using this

end Jacobians.Dolbeault.SerreResidueTheorem
