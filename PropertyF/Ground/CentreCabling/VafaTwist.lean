module
public import PropertyF.Ground.CentreCabling.TwistFinite
public import PropertyF.Ground.CentreCabling.VafaFusion

/-! A precise reduction of Vafa finiteness to the lantern determinant relation. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u

/-- The actual pivotal twist scalars, viewed as nonzero complex numbers. -/
def pivotalTwistUnit (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (i : Fin (rank C)) : ℂˣ := by
  letI : Simple (simples C i) := simples_simple C i
  exact Units.mk0 (Dimensions.pivotalBraidedTwistScalar C p (simples C i))
    (Dimensions.pivotalBraidedTwistScalar_ne_zero C p (simples C i))

/-- The standard Vafa lantern determinant relations give finite-order simple
pivotal twists. The determinant relations remain explicit hypotheses. -/
theorem pivotal_twist_finite_of_vafa_relations
    (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (h : ∀ i, pivotalTwistUnit C p i ^ (4 * vafaMultiplicity C i) =
      ∏ j, pivotalTwistUnit C p j ^ vafaWeight C i j)
    (i : Fin (rank C)) :
    IsOfFinOrder (End.of ((Dimensions.pivotalBraidedTwist C p (simples C i)).hom)) := by
  have hf := finite_order_of_vafa_relations (vafaWeight C) (fun i => 4 * vafaMultiplicity C i)
    (vafaWeight_sum_lt C) (pivotalTwistUnit C p) h i
  have hf' : IsOfFinOrder ((pivotalTwistUnit C p i : ℂˣ) : ℂ) :=
    Units.isOfFinOrder_val.mpr hf
  letI : Simple (simples C i) := simples_simple C i
  have hmap := (Dimensions.simpleEndScalarEquiv C (simples C i)).symm.toMonoidHom.isOfFinOrder hf'
  simpa [pivotalTwistUnit, Dimensions.pivotalBraidedTwistScalar] using hmap

/-- The lantern determinant relations and the balancing law suffice for all
mixed centre monodromies; neither premise is asserted proved. -/
theorem mixed_monodromy_finite_of_vafa_relations
    (C : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj))
    (h : ∀ i, pivotalTwistUnit C p i ^ (4 * vafaMultiplicity C i) =
      ∏ j, pivotalTwistUnit C p j ^ vafaWeight C i j)
    (hbalance : ∀ X Y, Modular.doubleBraiding X Y ≫
      ((Dimensions.pivotalBraidedTwist C p X).hom ⊗ₘ
        (Dimensions.pivotalBraidedTwist C p Y).hom) =
      (Dimensions.pivotalBraidedTwist C p (X ⊗ Y)).hom)
    (X Y : C.Obj) : IsOfFinOrder (End.of (Modular.doubleBraiding X Y)) := by
  apply mixed_monodromy_finite_of_balanced_finite_twist C
    (Dimensions.pivotalBraidedTwistNaturalIso C p)
  · exact pivotal_twist_finite_of_vafa_relations C p h
  · exact hbalance

end PropertyF.Ground.CentreCabling
