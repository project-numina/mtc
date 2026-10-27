module
public import PropertyF.Ground.CentreRigid.MateEquations

/-! Componentwise cup and cap identities for the dual mate. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreRigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- The mate unit in terms of the actual base coevaluation maps. -/
theorem dualMate_unit_explicit (Z : Center C) (U : C) :
  (λ_ U).inv ≫ (η_ Z.1 Z.1ᘁ ▷ U) ≫ (α_ Z.1 Z.1ᘁ U).hom ≫
    (Z.2.β (Z.1ᘁ ⊗ U)).hom =
  (ρ_ U).inv ≫ (U ◁ η_ (ᘁZ.1) Z.1) ≫ (α_ U (ᘁZ.1) Z.1).inv ≫
    ((Integrate.dualMateIso Z).inv.app U ▷ Z.1) := by
  have h := CentreRigid.dualMate_unit Z U
  simpa [tensorRightAdjunction, tensorLeftAdjunction, Adjunction.mkOfHomEquiv, Adjunction.mk',
    tensorRightHomEquiv, tensorLeftHomEquiv, Integrate.halfBraidingIso] using h

set_option backward.isDefEq.respectTransparency false in
/-- The unit component identifies the two chosen duals compatibly with the crossed cup. -/
theorem dualMateUnit_crossed_coevaluation (Z : Center C) :
  η_ Z.1 Z.1ᘁ ≫ (Z.2.β (Z.1ᘁ)).hom =
  η_ (ᘁZ.1) Z.1 ≫ ((Integrate.dualMateUnit Z).inv ▷ Z.1) := by
  have h := CentreRigid.dualMate_unit_explicit Z (𝟙_ C)
  have hn := Z.2.naturality (ρ_ Z.1ᘁ).hom
  dsimp [Integrate.dualMateUnit] 
  simp only [Category.assoc, comp_whiskerRight]
  calc
    _ = ((λ_ (𝟙_ C)).inv ≫ (η_ Z.1 Z.1ᘁ ▷ (𝟙_ C)) ≫
        (α_ Z.1 Z.1ᘁ (𝟙_ C)).hom ≫ (Z.2.β (Z.1ᘁ ⊗ (𝟙_ C))).hom) ≫
          ((ρ_ Z.1ᘁ).hom ▷ Z.1) := by rw [Category.assoc, Category.assoc, Category.assoc, ← hn]; monoidal
    _ = ((ρ_ (𝟙_ C)).inv ≫ ((𝟙_ C) ◁ η_ (ᘁZ.1) Z.1) ≫
        (α_ (𝟙_ C) (ᘁZ.1) Z.1).inv ≫ ((Integrate.dualMateIso Z).inv.app (𝟙_ C) ▷ Z.1)) ≫
          ((ρ_ Z.1ᘁ).hom ▷ Z.1) := by rw [h]
    _ = _ := by monoidal

end PropertyF.Ground.CentreRigid
