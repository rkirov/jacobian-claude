/-
  Riemann–Roch INTERFACE (the meet-in-the-middle).

  Goal: isolate the three irreducible analytic inputs of the Dolbeault→RR climb
  (`riemannRoch`, `deg_div`, existence of a canonical divisor) and PROVE everything
  else, discharging the frontier consumer `exists_singleSimplePole_of_genus_zero`
  modulo exactly those inputs. This gives the analytic ladder a concrete target and
  validates that the upstream work is load-bearing.

  PART 1 (this commit): the ℂ-module structure on `MeromorphicFunction X` — the
  prerequisite for `L(D)` to be a `Submodule ℂ`. Pure algebra (no analysis): `+`, `•`,
  `0`, `-` act pointwise on `toFun`, and the structure transports along the injection
  `toFun : MeromorphicFunction X → (X → ℂ)`.
-/
import Jacobians.Abel
import Jacobians.DegreeOneSphere

-- Many declarations here are purely algebraic (the ℂ-module on `MeromorphicFunction`) and use
-- only `[ChartedSpace ℂ X]`, not the full compact-manifold hypotheses carried by the consumers.
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MeromorphicFunction

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

end MeromorphicFunction

end Jacobians
