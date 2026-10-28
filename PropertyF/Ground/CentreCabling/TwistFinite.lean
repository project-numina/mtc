module
public import PropertyF.Ground.CentreCabling.CentralityClosure
public import PropertyF.Ground.CentreDimensions.PivotalTwist
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.MultiplicityDefect

/-! Reduction of mixed monodromy to the finite order of the pivotal twist. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreCabling
universe v u

/-- A natural endomorphism of the identity in a fusion category has a common
finite order as soon as its components on the simple representatives do. -/
theorem natural_end_finite_order_of_simples
    (C : Ground.BraidedFusionCategory.{v,u}) (α : 𝟭 C.Obj ⟶ 𝟭 C.Obj)
    (h : ∀ i, IsOfFinOrder (End.of (α.app (Ground.simples C i)))) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ X, (End.of (α.app X)) ^ n = 1 := by
  obtain ⟨n, hn, hs⟩ := (IsOfFinOrder.pi h).exists_pow_eq_one
  let a : End (𝟭 C.Obj) := End.of α
  have happ (k : ℕ) (X : C.Obj) : (a ^ k).asHom.app X =
      ((End.of (α.app X)) ^ k).asHom := by
    simpa [Functor.mapEnd, a] using congrArg End.asHom
      (map_pow (((CategoryTheory.evaluation C.Obj C.Obj).obj X).mapEnd (𝟭 C.Obj)) a k)
  have ha : a ^ n = 1 := by
    apply End.ext
    apply Dimensions.natTrans_eq_of_simple_components C
    intro i
    rw [happ]
    simpa using congrArg End.asHom (congrFun hs i)
  refine ⟨n, hn.ne', fun X ↦ ?_⟩
  let φ := ((CategoryTheory.evaluation C.Obj C.Obj).obj X).mapEnd (𝟭 C.Obj)
  exact ((map_pow φ a n).symm.trans (congrArg φ ha)).trans (map_one φ)

/-- Tensoring two endomorphisms commutes with taking powers. -/
theorem tensor_end_pow {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {X Y : D} (f : End X) (g : End Y) (n : ℕ) :
    (End.of (f.asHom ⊗ₘ g.asHom)) ^ n =
      End.of ((f ^ n).asHom ⊗ₘ (g ^ n).asHom) := by
  induction n with
  | zero => apply End.ext; simp
  | succ n ih =>
    apply End.ext
    simp only [pow_succ, End.mul_asHom, ih, tensorHom_comp_tensorHom]

/-- A balanced natural automorphism with finite-order simple components has
finite-order double braidings on every pair of objects. The balancing identity
is stated explicitly and is not asserted here for the pivotal twist. -/
theorem mixed_monodromy_finite_of_balanced_finite_twist
    (C : Ground.BraidedFusionCategory.{v,u}) (θ : 𝟭 C.Obj ≅ 𝟭 C.Obj)
    (hfinite : ∀ i, IsOfFinOrder (End.of (θ.hom.app (Ground.simples C i))))
    (hbalance : ∀ X Y, Modular.doubleBraiding X Y ≫
      (θ.hom.app X ⊗ₘ θ.hom.app Y) = θ.hom.app (X ⊗ Y))
    (X Y : C.Obj) : IsOfFinOrder (End.of (Modular.doubleBraiding X Y)) := by
  obtain ⟨n, hn, hp⟩ := natural_end_finite_order_of_simples C θ.hom hfinite
  let t : End (X ⊗ Y) := End.of (θ.hom.app X ⊗ₘ θ.hom.app Y)
  let z : End (X ⊗ Y) := End.of (θ.hom.app (X ⊗ Y))
  let m : End (X ⊗ Y) := End.of (Modular.doubleBraiding X Y)
  have ht : t ^ n = 1 := by
    change (End.of (θ.hom.app X ⊗ₘ θ.hom.app Y)) ^ n = 1
    rw [tensor_end_pow, hp X, hp Y]
    apply End.ext
    simp
  have hc : Commute t m := End.ext (doubleBraiding_natural (θ.hom.app X) (θ.hom.app Y))
  have hmt : t * m = z := End.ext (hbalance X Y)
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, ?_⟩
  have h := hc.mul_pow n
  rw [hmt, hp _, ht, one_mul] at h
  exact h.symm

/-- The actual pivotal twist scalars, viewed as nonzero complex numbers. -/
def pivotalTwistUnit (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (i : Fin (rank C)) : ℂˣ := by
  letI : Simple (simples C i) := simples_simple C i
  exact Units.mk0 (Dimensions.pivotalBraidedTwistScalar C p (simples C i))
    (Dimensions.pivotalBraidedTwistScalar_ne_zero C p (simples C i))

end PropertyF.Ground.CentreCabling
