module
public import PropertyF.Ground.CentreCabling.ImageCore
public import PropertyF.Ground.CentreDimensions.PivotalTwist
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
  classical
  let n : ℕ := (Finset.univ : Finset (Fin (Ground.rank C))).lcm
    (fun i => orderOf (End.of (α.app (Ground.simples C i))))
  have hn : n ≠ 0 := by
    apply Finset.lcm_ne_zero_iff.mpr
    intro i hi
    exact (h i).orderOf_pos.ne'
  have hs (i : Fin (Ground.rank C)) :
      (End.of (α.app (Ground.simples C i))) ^ n = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact Finset.dvd_lcm (Finset.mem_univ i)
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
    simpa using congrArg End.asHom (hs i)
  refine ⟨n, hn, ?_⟩
  intro X
  apply End.ext
  rw [← happ]
  exact congrArg (fun f : End (𝟭 C.Obj) => f.asHom.app X) ha

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
  have hz : IsOfFinOrder z := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, hp _⟩
  have htf : IsOfFinOrder t := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, Nat.pos_of_ne_zero hn, ht⟩
  have hc : Commute z t := by
    apply End.ext
    change (θ.hom.app X ⊗ₘ θ.hom.app Y) ≫ θ.hom.app (X ⊗ Y) =
      θ.hom.app (X ⊗ Y) ≫ (θ.hom.app X ⊗ₘ θ.hom.app Y)
    exact θ.hom.naturality _
  have hmt : t * m = z := by
    apply End.ext
    exact hbalance X Y
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  have hpow : t ^ (n - 1) * t = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hpos, ht]
  have hm : m = t ^ (n - 1) * z := by
    calc
      m = (t ^ (n - 1) * t) * m := by rw [hpow, one_mul]
      _ = t ^ (n - 1) * (t * m) := by rw [mul_assoc]
      _ = _ := by rw [hmt]
  change IsOfFinOrder m
  rw [hm]
  exact ((hc.symm).pow_left _).isOfFinOrder_mul (htf.pow) hz

end PropertyF.Ground.CentreCabling
