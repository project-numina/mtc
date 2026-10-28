module
public import PropertyF.Ground.CentreCabling.CentralityClosure
public import PropertyF.Ground.CentreDimensions.PivotalTwist
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.MultiplicityDefect

/-! Reduction of mixed monodromy to the finite order of the pivotal twist. -/
@[expose] public noncomputable section
open PropertyF.Ground.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreCabling
universe v u

/-- A natural endomorphism has finite order if finitely many components detect
it and each of those components has finite order. -/
theorem natural_end_finite_order_of_components {D : Type u} [Category.{v} D]
    {ι : Type*} [Finite ι] (X : ι → D)
    (hext : ∀ {α β : 𝟭 D ⟶ 𝟭 D}, (∀ i, α.app (X i) = β.app (X i)) → α = β)
    (α : 𝟭 D ⟶ 𝟭 D) (h : ∀ i, IsOfFinOrder (End.of (α.app (X i)))) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ Y, (End.of (α.app Y)) ^ n = 1 := by
  obtain ⟨n, hn, hs⟩ := (IsOfFinOrder.pi h).exists_pow_eq_one
  let a : End (𝟭 D) := End.of α
  have happ (k : ℕ) (Y : D) : (a ^ k).asHom.app Y =
      ((End.of (α.app Y)) ^ k).asHom := by
    simpa [Functor.mapEnd, a] using congrArg End.asHom
      (map_pow (((CategoryTheory.evaluation D D).obj Y).mapEnd (𝟭 D)) a k)
  have ha : a ^ n = 1 := by
    apply End.ext
    apply hext
    intro i
    rw [happ]
    simpa using congrArg End.asHom (congrFun hs i)
  refine ⟨n, hn.ne', fun Y ↦ ?_⟩
  let φ := ((CategoryTheory.evaluation D D).obj Y).mapEnd (𝟭 D)
  exact ((map_pow φ a n).symm.trans (congrArg φ ha)).trans (map_one φ)

/-- A natural endomorphism of the identity in a fusion category has a common
finite order as soon as its components on the simple representatives do. -/
theorem natural_end_finite_order_of_simples
    {C : Ground.BraidedFusionCategory.{v,u}} (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj)
    (h : ∀ i, IsOfFinOrder (End.of (α.app (Ground.simples C i)))) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ X, (End.of (α.app X)) ^ n = 1 :=
  natural_end_finite_order_of_components (simples C)
    (fun h ↦ Dimensions.natTrans_eq_of_simple_components C h) α h

/-- Tensoring two endomorphisms commutes with taking powers. -/
theorem tensor_end_pow {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {X Y : D} (f : End X) (g : End Y) (n : ℕ) :
    (End.of (f.asHom ⊗ₘ g.asHom)) ^ n =
      End.of ((f ^ n).asHom ⊗ₘ (g ^ n).asHom) := by
  induction n with
  | zero => exact End.ext (id_tensorHom_id X Y).symm
  | succ n ih =>
    apply End.ext
    simp only [pow_succ, End.mul_asHom, ih, tensorHom_comp_tensorHom]

/-- A balanced natural automorphism with finite-order simple components has
finite-order double braidings on every pair of objects. The balancing identity
is stated explicitly and is not asserted here for the pivotal twist. -/
theorem mixed_monodromy_finite_of_balanced_finite_twist
    {C : Ground.BraidedFusionCategory.{v,u}} (θ : 𝟭 C.Obj ≅ 𝟭 C.Obj)
    (hfinite : ∀ i, IsOfFinOrder (End.of (θ.hom.app (Ground.simples C i))))
    (hbalance : ∀ X Y, Modular.doubleBraiding X Y ≫
      (θ.hom.app X ⊗ₘ θ.hom.app Y) = θ.hom.app (X ⊗ Y))
    (X Y : C.Obj) : IsOfFinOrder (End.of (Modular.doubleBraiding X Y)) := by
  obtain ⟨n, hn, hp⟩ := natural_end_finite_order_of_simples θ.hom hfinite
  let t : End (X ⊗ Y) := End.of (θ.hom.app X ⊗ₘ θ.hom.app Y)
  let z : End (X ⊗ Y) := End.of (θ.hom.app (X ⊗ Y))
  let m : End (X ⊗ Y) := End.of (Modular.doubleBraiding X Y)
  have ht : t ^ n = 1 := by
    change (End.of (θ.hom.app X ⊗ₘ θ.hom.app Y)) ^ n = 1
    rw [tensor_end_pow, hp X, hp Y]
    apply End.ext
    simp
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  symm
  simpa only [show t * m = z from End.ext (hbalance X Y), z, hp, ht, one_mul] using
    (show Commute t m from End.ext (doubleBraiding_natural (θ.hom.app X) (θ.hom.app Y))).mul_pow n

/-- The actual pivotal twist scalars, viewed as nonzero complex numbers. -/
def pivotalTwistUnit (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C)) : ℂˣ := by
  letI : Simple (simples C i) := simples_simple C i
  exact Units.mk0 (pivotalBraidedTwistScalar C p (simples C i))
    (pivotalBraidedTwistScalar_ne_zero C p (simples C i))

end PropertyF.Ground.CentreCabling
