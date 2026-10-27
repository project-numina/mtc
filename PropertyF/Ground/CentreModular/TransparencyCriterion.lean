module
public import PropertyF.Ground.CentreModular.VafaPivotal
public import PropertyF.Ground.CentreModular.KirbyCriterion
public import PropertyF.Ground.CentreCabling.TraceSaturation
public import PropertyF.Ground.CentreCabling.CentralityClosure

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u

/-- Positive FP dimensions and twist balancing upgrade the numerical S-test
to actual transparency of a simple object. -/
theorem transparent_of_S_test_and_balancing
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (hbalance : ∀ X Y, Modular.doubleBraiding X Y ≫
      ((Dimensions.pivotalBraidedTwist C p X).hom ⊗ₘ
        (Dimensions.pivotalBraidedTwist C p Y).hom) =
      (Dimensions.pivotalBraidedTwist C p (X ⊗ Y)).hom)
    (k : Fin (rank C))
    (hs : ∀ i, Modular.categoricalS C p i k =
      Modular.simpleDimension C p i * Modular.simpleDimension C p k) :
    Transparent (simples C k) := by
  have hsimple (i : Fin (rank C)) :
      Modular.doubleBraiding (simples C i) (simples C k) = 𝟙 _ := by
    apply CentreCabling.doubleBraiding_eq_one_of_sTest_of_finite_order C p hdim i k
    · exact mixed_monodromy_finite_of_pivotal_balancing C p hbalance _ _
    · exact hs i
  intro X
  have hx : Modular.doubleBraiding X (simples C k) = 𝟙 _ := by
    apply CentreCabling.doubleBraiding_eq_one_of_simple_constituents C (fun _ => True)
      (fun _ _ => trivial) X (simples C k) trivial
    intro i _
    exact hsimple i
  have hc := congrArg (fun f => (β_ X (simples C k)).inv ≫ f ≫ (β_ X (simples C k)).hom) hx
  change Modular.doubleBraiding (simples C k) X = 𝟙 _
  simpa [Modular.doubleBraiding, Category.assoc] using hc

/-- In a positive pivotal category with balanced twist, S is invertible if the
unit is the only transparent simple object. -/
theorem categoricalS_det_ne_zero_of_trivial_transparency
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (hbalance : ∀ X Y, Modular.doubleBraiding X Y ≫
      ((Dimensions.pivotalBraidedTwist C p X).hom ⊗ₘ
        (Dimensions.pivotalBraidedTwist C p Y).hom) =
      (Dimensions.pivotalBraidedTwist C p (X ⊗ Y)).hom)
    (htrivial : ∀ k, Transparent (simples C k) → k = unitIndex C) :
    (Modular.categoricalS C p).det ≠ 0 := by
  apply categoricalS_det_ne_zero_of_trivial_S_centralizer C p hdim
  intro k hs
  exact htrivial k (transparent_of_S_test_and_balancing C p hdim hbalance k hs)

end PropertyF.Ground.CentreModular
