module
public import PropertyF.Ground.Integrate.CenterDualMate

/-! Unit cases of the tensor law for the normalized dual crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreRigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

theorem dualCrossing_tensor_unit_left (Z : CategoryTheory.Center C) (V : C) :
    ((Integrate.dualCrossingIso Z).app ((𝟙_ C) ⊗ V)).hom =
      (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app (𝟙_ C)).hom ▷ V) ≫
        (α_ _ _ _).hom ≫ ((𝟙_ C) ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫
          (α_ _ _ _).inv := by
  rw [← cancel_mono ((λ_ V).hom ▷ Z.1ᘁ)]
  rw [← Integrate.dualCrossing_natural Z (λ_ V).hom]
  rw [Integrate.dualCrossing_unit]
  simp only [Iso.trans_hom, Iso.symm_hom]
  monoidal

theorem dualCrossing_tensor_unit_right (Z : CategoryTheory.Center C) (U : C) :
    ((Integrate.dualCrossingIso Z).app (U ⊗ (𝟙_ C))).hom =
      (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ (𝟙_ C)) ≫
        (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app (𝟙_ C)).hom) ≫
          (α_ _ _ _).inv := by
  rw [← cancel_mono ((ρ_ U).hom ▷ Z.1ᘁ)]
  rw [← Integrate.dualCrossing_natural Z (ρ_ U).hom]
  rw [Integrate.dualCrossing_unit]
  simp only [Iso.trans_hom, Iso.symm_hom]
  monoidal

end PropertyF.Ground.CentreRigid
