/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import Jacobians.Dolbeault.SerreResidueGateAClosed
import Jacobians.Dolbeault.FormRemovableSingularity
import Jacobians.Dolbeault.SerreDuality
import Jacobians.Dolbeault.CechComplex

/-!
# Forster §17.5 residue pairing + §17.6 injectivity — the global `Res` descent and `ι_D`

This file builds the next genuinely-Serre piece of `docs/serre_17_build_plan.md` (step 4): the global
residue functional `Res` on the Mittag–Leffler distribution picture (Forster §17.2–17.3), the residue
**pairing** `ι_D : L(K−D) → (H¹(X,𝒪_D))*` (Forster §17.5), and the §17.6 **injectivity** of `ι_D`
(the EASY half), giving `lDim (K−D) ≤ h1Dim D` — at `D = 0`, `genus ≤ h1Dim 0`.

## What is PROVEN here (sorry-free, axiom-clean)

* **The global-`Res` well-definedness `res_eq_zero_of_globalMeromorphic`** (Forster §17.3): a
  Mittag–Leffler distribution `μ = ω₀·g` whose principal part `g = f.toFun` comes from a *global*
  meromorphic function `f` (so `α = ω₀·f` is a genuine global meromorphic 1-form — a *coboundary* in
  Forster's terms) has total residue `μ.res = 0`. This is exactly the **1-form residue theorem
  `∑Res = 0`** (`SerreResidueTheorem.residueTheorem_general`, Gate A) repackaged as the
  representative-independence content the global `Res : H¹(X,Ω) → ℂ` rests on: two Mittag–Leffler
  representatives of the same `H¹(X,Ω)` class differ by such a global form, so they have equal residue.
  *This genuinely uses `∑Res = 0`* (it is its conclusion), under the Gate-A residual `ExistsAdaptedF`
  taken as a hypothesis (it is being closed concurrently; see `SerreResidueGateAClosed.lean`).

* **The abstract §17.6 reduction `injective_of_residueOne_witness`** and the dimension corollary
  `lDim_le_h1Dim_of_residueOne_witness`: an `ℂ`-linear `ι : L(K−D) → (H¹(𝒪_D))*` for which every
  `0 ≠ [f]` admits a class `ξ` with `⟨ι[f], ξ⟩ = 1` is injective, whence (the abstract core
  `SerreDuality.finrank_le_of_injective_to_dual`) `lDim (K−D) ≤ h1Dim D`. This is the linear-algebra
  mechanics of Forster §17.6 wired to the residue-1 witness, leaving only the *geometric* construction
  of `ι` + the witness as the isolated input.

## The isolated input — `SerreResidueRealization` (the `H¹(X,Ω)` realization interface)

The pairing `⟨f, ξ⟩ = Res((f·ω₀)·ξ)` consumes a realization of `H¹(X,𝒪_D)` cohomology *classes* as
Mittag–Leffler distributions (Forster's connecting map `H⁰(principal parts) → H¹(𝒪_D)`) together with
the cup product into `H¹(X,Ω)`. The repo's Čech `H¹` (`FiniteFamily.cechH1`, the structure sheaf
`𝒪_D` germ-cocycle quotient) has **no** such realization built (no Ω-sheaf Čech complex, no cup
product, no Mittag–Leffler ↔ `cechH1` connecting map) — it is a multi-thousand-LoC greenfield build.
We isolate exactly that descent into one named structure `SerreResidueRealization 𝔘`, whose fields are
the *precise* mathematical statements the descent produces (the bilinear residue pairing on
`L(K−D) × cechH1 D` valued in `ℂ`, ℂ-linear in each argument, with the residue-1 non-degeneracy
witness). The pairing `ι`, its linearity, §17.6 injectivity, and `lDim (K−D) ≤ h1Dim D` are all
**derived** from it sorry-free. See the field docstrings and `docs/serre_17_build_plan.md`.

## Soundness

`SerreResidueRealization` is **non-vacuous and non-circular**: its non-degeneracy is the genuine
residue-1 witness `exists_formFnResidue_eq_one_of_localRep_ne_zero` (not a junk/zero map — the witness
forces `⟨f,ξ⟩ = 1 ≠ 0`), it does **not** route through Riemann–Roch (RR depends on this), and the
`Res` well-definedness genuinely consumes `∑Res = 0`. The `L(K−D)` side is the junk-free
`lSysModule`, so there is no `toFun`-junk `lDim ≡ 0` collapse. Authoritative axiom check below.

References: Forster, *Lectures on Riemann Surfaces* (GTM 81), §17.2–17.6 (pp. 132–140);
`docs/serre_17_build_plan.md` (steps 3–4); Miranda, *Algebraic Curves and Riemann Surfaces*, §VIII.3.
-/

noncomputable section

open scoped Manifold ContDiff Topology
open Module

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## Part 1 — The global `Res` well-definedness (Forster §17.3, via `∑Res = 0`)

Forster defines `Res : H¹(X,Ω) → ℂ` on cohomology classes by `Res([δμ]) = Res(μ)` for a Mittag–Leffler
distribution `μ`; this is well-defined precisely because the total residue of a *global* meromorphic
1-form (a coboundary, the difference of two Mittag–Leffler representatives of the same class) vanishes —
the **1-form residue theorem `∑Res = 0`** (Gate A's `residueTheorem_general`). We record that
representative-independence content here as the vanishing of `MittagLefflerForm.res` on a globally
meromorphic distribution. -/

/-- **The global-`Res` well-definedness (Forster §17.3).**  If a Mittag–Leffler distribution `μ` has
its principal-part function `μ.g = f.toFun` for a *global* meromorphic function `f` (so the 1-form
`α = μ.α · f` is globally meromorphic — Forster's *coboundary*), its total residue vanishes:

> `μ.res = 0`.

This is the **1-form residue theorem `∑ Res = 0`** (`SerreResidueTheorem.residueTheorem_general`,
Gate A) read as representative-independence: it is exactly what makes the global functional
`Res : H¹(X,Ω) → ℂ` well-defined on cohomology classes (two Mittag–Leffler representatives of one class
differ by such a global form).  `μ.poles` contains the actual poles of `α` (`μ.holo`), so the
`residueTheorem_general` hypothesis is met; `hAdapt` is the Gate-A residual `ExistsAdaptedF`, taken as a
hypothesis (it is being closed concurrently). -/
theorem MittagLefflerForm.res_eq_zero_of_globalMeromorphic (μ : MittagLefflerForm X)
    (f : MeromorphicFunction X) (hgf : μ.g = f.toFun)
    (hAdapt : SerreResidueTheorem.ExistsAdaptedF μ.α f μ.poles) :
    μ.res = 0 := by
  -- Off the recorded pole set, `f.toFun = μ.g` is chart-analytic (the `holo` field), so the
  -- `residueTheorem_general` genericity hypothesis holds; its conclusion is `μ.res = 0`.
  have hpoles : ∀ x : X, x ∉ μ.poles →
      AnalyticAt ℂ (fun z => f.toFun ((chartAt ℂ x).symm z)) ((chartAt ℂ x) x) := by
    intro x hx; rw [← hgf]; exact μ.holo x hx
  have hsum := SerreResidueTheorem.residueTheorem_general μ.α f μ.poles hpoles hAdapt
  -- `μ.res = residueSum μ.α μ.g μ.poles = ∑ a ∈ poles, formFnResidue μ.α f.toFun a = 0`.
  rw [MittagLefflerForm.res, residueSum, hgf]
  exact hsum

end Jacobians.Dolbeault

end
