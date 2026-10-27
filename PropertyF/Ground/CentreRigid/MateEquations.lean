module
public import PropertyF.Ground.Integrate.CenterDualMate

/-! The normalized dual candidate starts from an adjoint mate. These equations
expose its compatibility with the units and counits of the tensor adjunctions. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreRigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

theorem dualMate_unit (Z : CategoryTheory.Center C) (U : C) :
    (tensorLeftAdjunction Z.1 Z.1ᘁ).unit.app U ≫
      (Integrate.halfBraidingIso Z).hom.app
        ((tensorLeft Z.1ᘁ).obj U) =
    (tensorRightAdjunction (ᘁZ.1) Z.1).unit.app U ≫
      (tensorRight Z.1).map ((Integrate.dualMateIso Z).inv.app U) := by
  simpa [Integrate.dualMateIso] using
    unit_conjugateEquiv_symm (tensorLeftAdjunction Z.1 Z.1ᘁ)
      (tensorRightAdjunction (ᘁZ.1) Z.1) (Integrate.halfBraidingIso Z).hom U

end PropertyF.Ground.CentreRigid
