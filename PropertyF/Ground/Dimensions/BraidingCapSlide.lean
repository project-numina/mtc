module
public import PropertyF.Ground.Dimensions.Drinfeld

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- A braiding slides past an evaluation cap with the inverse crossing on the dual strand. -/
theorem braiding_cap_slide {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [RightRigidCategory C] (X Y : C) :
    (β_ (Xᘁ) Y).hom ▷ X ⊗≫ Y ◁ ε_ X (Xᘁ) ⊗≫ (ρ_ Y).hom =
      𝟙 (((Xᘁ) ⊗ Y) ⊗ X) ⊗≫ (Xᘁ) ◁ (β_ X Y).inv ⊗≫ ε_ X (Xᘁ) ▷ Y ⊗≫ (λ_ Y).hom := by
  have h := braiding_naturality_left (ε_ X (Xᘁ)) Y
  rw [braiding_tensor_left_hom] at h
  have h' := congrArg (fun f => f ≫ (ρ_ Y).hom) h
  simp only [Category.assoc, braiding_rightUnitor] at h'
  calc
    _ = (α_ (Xᘁ) Y X).hom ≫ (Xᘁ) ◁ (β_ X Y).inv ≫ (α_ (Xᘁ) X Y).inv ≫
      (ε_ X (Xᘁ) ▷ Y ≫ (λ_ Y).hom) := by
        rw [h']
        simp only [Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc,
          Iso.inv_hom_id, whiskerLeft_id, Category.id_comp, Iso.hom_inv_id_assoc]
        monoidal
    _ = _ := by monoidal
set_option backward.isDefEq.respectTransparency false in
/-- The same cap slide for the reversed braiding. -/
theorem braiding_inverse_cap_slide {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [BraidedCategory C] [RightRigidCategory C] (X Y : C) :
    (β_ Y (Xᘁ)).inv ▷ X ⊗≫ Y ◁ ε_ X (Xᘁ) ⊗≫ (ρ_ Y).hom =
      𝟙 (((Xᘁ) ⊗ Y) ⊗ X) ⊗≫ (Xᘁ) ◁ (β_ Y X).hom ⊗≫ ε_ X (Xᘁ) ▷ Y ⊗≫ (λ_ Y).hom := by
  exact @braiding_cap_slide C _ _ (reverseBraiding C) _ X Y
end PropertyF.Ground.Dimensions
