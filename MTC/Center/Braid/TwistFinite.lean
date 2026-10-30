module
public import MTC.Center.Braid.CentralityClosure
public import MTC.Center.Dimensions.PivotalTwist
public import MTC.Fusion.Agreement
public import MTC.CategoryTheory.Dimensions.MultiplicityDefect

open MTC.PropertyF.Reduction

open MTC.Fusion

open MTC.Braided

/-!
# Finite-order monodromy

Finite order on detecting components gives finite order for a natural
endomorphism. For a balanced automorphism this implies finite-order monodromy.
-/
@[expose] public noncomputable section
open MTC.Modular (doubleBraiding)
open MTC.CategoryTheory.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.Center.Braid
universe v u
variable {D : Type u} [Category.{v} D]
variable {C : MTC.Fusion.BraidedFusionCategory.{v,u}}

/-- A natural endomorphism has finite order if finitely many components detect
it and each of those components has finite order. -/
theorem natural_end_finite_order_of_components {ι : Type*} [Finite ι] (X : ι → D)
    (hext : ∀ {α β : 𝟭 D ⟶ 𝟭 D}, (∀ i, α.app (X i) = β.app (X i)) → α = β)
    (α : 𝟭 D ⟶ 𝟭 D) (h : ∀ i, IsOfFinOrder (End.of (α.app (X i)))) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ Y, (End.of (α.app Y)) ^ n = 1 :=
  let a : End (𝟭 D) := End.of α
  let φ : End (𝟭 D) →* (∀ i, End (X i)) :=
    MonoidHom.pi fun i ↦ ((CategoryTheory.evaluation D D).obj (X i)).mapEnd (𝟭 D)
  let hφ : Function.Injective φ := fun _ _ hbc ↦
    End.ext <| hext fun i ↦ congrArg End.asHom (congrFun hbc i)
  let ⟨n, hn, ha⟩ :=
    (hφ.isOfFinOrder_iff.mp (show IsOfFinOrder (φ a) from IsOfFinOrder.pi h)).exists_pow_eq_one
  ⟨n, hn.ne', fun Y ↦
    let ψ := ((CategoryTheory.evaluation D D).obj Y).mapEnd (𝟭 D)
    ((map_pow ψ a n).symm.trans (congrArg ψ ha)).trans (map_one ψ)⟩

/-- Tensoring two endomorphisms commutes with taking powers. -/
theorem tensor_end_pow [MonoidalCategory D]
    {X Y : D} (f : End X) (g : End Y) (n : ℕ) :
    (End.of (f.asHom ⊗ₘ g.asHom)) ^ n =
      End.of ((f ^ n).asHom ⊗ₘ (g ^ n).asHom) := by
  induction n with
  | zero => exact End.ext (id_tensorHom_id X Y).symm
  | succ n ih =>
    apply End.ext
    simp only [pow_succ, End.mul_asHom, ih, tensorHom_comp_tensorHom]

/-- A natural automorphism of the identity satisfies the twist balancing law. -/
abbrev IsBalancedTwist [MonoidalCategory D] [BraidedCategory D] (θ : 𝟭 D ≅ 𝟭 D) : Prop :=
  ∀ X Y, doubleBraiding X Y ≫ (θ.hom.app X ⊗ₘ θ.hom.app Y) = θ.hom.app (X ⊗ Y)

/-- A balanced natural automorphism with finite-order simple components has
finite-order double braidings on every pair of objects. The balancing identity
is stated explicitly and is not asserted here for the pivotal twist. -/
theorem mixed_monodromy_finite_of_balanced_finite_twist (θ : 𝟭 C.Obj ≅ 𝟭 C.Obj)
    (hfinite : ∀ i, IsOfFinOrder (End.of (θ.hom.app (MTC.Fusion.simples C i))))
    (hbalance : IsBalancedTwist θ)
    (X Y : C.Obj) : IsOfFinOrder (End.of (doubleBraiding X Y)) := by
  let : HasFiniteBiproducts C.Obj := Abelian.hasFiniteBiproducts
  obtain ⟨n, hn, hp⟩ := natural_end_finite_order_of_components (simples C)
    (fun h ↦ MTC.CategoryTheory.Dimensions.natTrans_eq_of_biproduct_components (simples_decompose C) h) θ.hom hfinite
  let t : End (X ⊗ Y) := End.of (θ.hom.app X ⊗ₘ θ.hom.app Y)
  let m : End (X ⊗ Y) := End.of (doubleBraiding X Y)
  have ht : t ^ n = 1 := by
    simp [t, tensor_end_pow (End.of (θ.hom.app X)) (End.of (θ.hom.app Y)) n, hp, End.ext_iff]
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  simpa only [show t * m = End.of (θ.hom.app (X ⊗ Y)) from End.ext (hbalance X Y),
    hp, ht, one_mul] using
    ((show Commute t m from End.ext (Modular.doubleBraiding_natural (θ.hom.app X) (θ.hom.app Y))).mul_pow n).symm

/-- The actual pivotal twist scalars, viewed as nonzero complex numbers. -/
def pivotalTwistUnit (C : MTC.Fusion.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C)) : ℂˣ := by
  letI : Simple (simples C i) := simples_simple C i
  exact Units.mk0 (pivotalBraidedTwistScalar C p (simples C i))
    (pivotalBraidedTwistScalar_ne_zero C p (simples C i))

end MTC.Center.Braid
