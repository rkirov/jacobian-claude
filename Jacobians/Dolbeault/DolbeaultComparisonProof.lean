/-
  The **L3 kernel** — Dolbeault's comparison theorem `H^{0,1}(X) ≅ H¹(X, 𝒪)`, the single hardest
  analytic input of the `D = 0` Serre route (`arithmeticGenus_eq_genus`).

  Target (proven standalone here, the caller in `DolbeaultComparison` wires it):

    `cechH1_dolbeault_comparison (𝔘 : FiniteCover X) :`
    `    finrank ℝ (DolbeaultH01 X) = 2 * finrank ℂ (𝔘.cechH1 0)`

  the `ℝ`-vs-`ℂ` dimension count of Dolbeault's iso (`H^{0,1}` is `Module ℝ` of real-dim `2g`;
  `cechH1` is `Module ℂ` of complex-dim `g`).

  MATH (Dolbeault's theorem). Two mutually-inverse maps:
  * **Dolbeault → Čech.** A smooth `(0,1)`-form `g`: on each chart-disk `U_i` solve `∂̄u_i = g`
    *locally* (`DbarLocal.dbar_solvable_locally`, DONE). Then `∂̄(u_i − u_j) = g − g = 0` on
    `U_i ∩ U_j`, so `{u_i − u_j}` is a holomorphic Čech `1`-cocycle; its class lands in `cechH1`.
  * **Čech → Dolbeault.** A holomorphic cocycle `{f_ij}`: with a partition of unity `{ρ_k}`
    subordinate to the cover, set `h_i := ∑_k ρ_k f_ik`; then `f_ij = h_j − h_i` (smooth) and
    `∂̄h_i = ∂̄h_j` on overlaps (`f_ij` holomorphic) glue to a global `(0,1)`-form; its class.

  These are mutually inverse, giving a linear iso and hence the `finrank` relation.

  HONESTY. This file builds the connective tissue sorry-free and isolates each genuinely-hard
  analytic sub-kernel as a *named honest `sorry` with a TRUE statement*. See the closing summary
  comment for exactly which sub-kernels remain. We never weaken the target.
-/
import Jacobians.Dolbeault.DolbeaultComparison
import Jacobians.Dolbeault.DbarLocal
import Mathlib.Geometry.Manifold.PartitionOfUnity

open scoped Manifold ContDiff Bundle Topology
open TopologicalSpace (Opens)

-- Same permissive transparency as `RealForms`/`DolbeaultH01`/`DolbeaultComparison` (the section
-- hom-bundle instances need it).
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

namespace Jacobians.Dolbeault

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ## The two comparison maps and their assembly into an `ℝ`-linear equivalence

Dolbeault's theorem is realised by two mutually-inverse `ℝ`-linear maps between `DolbeaultH01 X`
(an `ℝ`-module) and `𝔘.cechH1 0` (a `ℂ`-module, viewed as an `ℝ`-module via `ℝ ↪ ℂ`). We state each
map and the two round-trip identities as honest named `sorry`s (each is a TRUE statement — the real
analytic content), then assemble the equivalence and the `finrank` count *sorry-free*. The factor `2`
is the `ℝ`-vs-`ℂ` dimension (`finrank_real_of_complex` on the `ℂ`-module `cechH1`); it needs **no**
`Module ℂ` on `DolbeaultH01` — the `ℝ`-linear equivalence carries `finrank ℝ (DolbeaultH01) =
finrank ℝ (cechH1) = 2 · finrank ℂ (cechH1)`. -/

variable (𝔘 : FiniteCover X)

/-- **Dolbeault → Čech** (honest named sub-kernel). The `ℝ`-linear map `H^{0,1}(X) → H¹(X, 𝒪)`:
represent a class by a smooth `(0,1)`-form `g`, solve `∂̄u_i = g` on each chart-disk `U_i`
(`DbarLocal.dbar_solvable_locally`), and send `[g]` to the class of the holomorphic Čech `1`-cocycle
`{u_i − u_j}` (holomorphic because `∂̄(u_i − u_j) = g − g = 0` on `U_i ∩ U_j`). Well-definedness
(independence of the representative `g` and of the local primitive choices `u_i`) is part of this
sub-kernel. -/
noncomputable def dolbeault_to_cech : DolbeaultH01 X →ₗ[ℝ] 𝔘.cechH1 0 :=
  sorry

/-- **Čech → Dolbeault** (honest named sub-kernel). The `ℝ`-linear inverse `H¹(X, 𝒪) → H^{0,1}(X)`:
represent a class by a holomorphic Čech `1`-cocycle `{f_ij}`, choose a partition of unity `{ρ_k}`
subordinate to the cover (`SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source`, available
since a compact manifold is `σ`-compact), set `h_i := ∑_k ρ_k · f_ik` (smooth), so that
`f_ij = h_j − h_i` and the `∂̄h_i` agree on overlaps (`f_ij` holomorphic ⟹ `∂̄(h_j − h_i) = 0`),
gluing to a global smooth `(0,1)`-form whose class is the image. Well-definedness (independence of
the cocycle representative and of the partition of unity) is part of this sub-kernel. -/
noncomputable def cech_to_dolbeault : 𝔘.cechH1 0 →ₗ[ℝ] DolbeaultH01 X :=
  sorry

/-- **`comparison_bijective`, part 1** (honest named sub-kernel): Dolbeault → Čech → Dolbeault is the
identity. Globalizing a locally-solved `(0,1)`-form via the partition of unity returns the same
Dolbeault class. -/
theorem cech_to_dolbeault_comp_dolbeault_to_cech :
    (cech_to_dolbeault 𝔘) ∘ₗ (dolbeault_to_cech 𝔘) = LinearMap.id :=
  sorry

/-- **`comparison_bijective`, part 2** (honest named sub-kernel): Čech → Dolbeault → Čech is the
identity. Local-solving the partition-of-unity primitive recovers the same Čech cohomology class. -/
theorem dolbeault_to_cech_comp_cech_to_dolbeault :
    (dolbeault_to_cech 𝔘) ∘ₗ (cech_to_dolbeault 𝔘) = LinearMap.id :=
  sorry

/-- **The Dolbeault isomorphism** `H^{0,1}(X) ≃ₗ[ℝ] H¹(X, 𝒪)` — assembled *sorry-free* from the two
maps and the two round-trip identities above (`LinearEquiv.ofLinear`). All remaining content is in
the four named sub-kernels. -/
noncomputable def comparison_linearEquiv : DolbeaultH01 X ≃ₗ[ℝ] 𝔘.cechH1 0 :=
  LinearEquiv.ofLinear (dolbeault_to_cech 𝔘) (cech_to_dolbeault 𝔘)
    (dolbeault_to_cech_comp_cech_to_dolbeault 𝔘)
    (cech_to_dolbeault_comp_dolbeault_to_cech 𝔘)

/-- **The L3 kernel: Čech ↔ Dolbeault comparison** — the standalone proof of the statement at
`DolbeaultComparison.lean:227` (`cechH1_dolbeault_comparison`; the caller wires it to this).
Proven *sorry-free* from `comparison_linearEquiv`: the `ℝ`-linear iso transports `finrank ℝ`, and the
`ℝ`-vs-`ℂ` factor on the `ℂ`-module `cechH1` is `finrank_real_of_complex`. The entire remaining
content sits in the four named sub-kernels (`dolbeault_to_cech`, `cech_to_dolbeault`, and the two
round-trip identities). -/
theorem cechH1_dolbeault_comparison_proof :
    Module.finrank ℝ (DolbeaultH01 X) = 2 * Module.finrank ℂ (𝔘.cechH1 0) := by
  rw [(comparison_linearEquiv 𝔘).finrank_eq, finrank_real_of_complex]

end Jacobians.Dolbeault
