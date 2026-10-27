module
public import PropertyF.Ground.CentreInduction.FiniteMonodromyModular
public import PropertyF.Ground.CentreModular.VafaPivotal

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreModular
universe v u
set_option backward.isDefEq.respectTransparency false

/-- The actual centre's S matrix is invertible if it has a pivotal structure
with FP-valued dimensions and balanced pivotal twist. Centre rigidity and
fusion remain explicit instances. -/
theorem center_S_invertible_of_balanced_pivotal
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj))
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ))
    (hbalance : ∀ X Y : (Integrate.bundledCenter C).Obj,
      Modular.doubleBraiding X Y ≫
        ((Dimensions.pivotalBraidedTwist (Integrate.bundledCenter C) p X).hom ⊗ₘ
          (Dimensions.pivotalBraidedTwist (Integrate.bundledCenter C) p Y).hom) =
        (Dimensions.pivotalBraidedTwist (Integrate.bundledCenter C) p (X ⊗ Y)).hom) :
    (Modular.categoricalS (Integrate.bundledCenter C) p).det ≠ 0 := by
  apply CentreInduction.center_S_invertible_of_finite_simple_monodromy C p hdim
  intro i j
  exact mixed_monodromy_finite_of_pivotal_balancing (Integrate.bundledCenter C) p hbalance _ _

end PropertyF.Ground.CentreModular
