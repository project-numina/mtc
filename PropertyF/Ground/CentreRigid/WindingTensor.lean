module
public import PropertyF.Ground.CentreRigid.WindingDecomposition

/-! Factor centre windings over tensor product test strands. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreRigid
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- A winding around a tensor-product strand factors into two successive windings. -/
theorem winding_tensor (C : BraidedFusionCategory.{v,u}) (X Y : Center C.Obj) (f : X.1 ⟶ Y.1)
    (T U : C.Obj) :
    CentreInduction.winding C X Y (T ⊗ U) f =
      (α_ X.1 T U).inv ≫ ((X.2.β T).hom ▷ U) ≫ (α_ T X.1 U).hom ≫
        (T ◁ CentreInduction.winding C X Y U f) ≫ (α_ T Y.1 U).inv ≫
          ((Y.2.β T).inv ▷ U) ≫ (α_ Y.1 T U).hom := by
  have hy : Y.2.β (T ⊗ U) = (α_ Y.1 T U).symm ≪≫
      (whiskerRightIso (Y.2.β T) U) ≪≫ (α_ T Y.1 U) ≪≫
      (whiskerLeftIso T (Y.2.β U)) ≪≫ (α_ T U Y.1).symm := by
    apply Iso.ext
    exact Y.2.monoidal T U
  dsimp only [CentreInduction.winding]
  rw [X.2.monoidal, hy]
  simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, whiskerRightIso_inv,
    whiskerLeft_comp]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Partial trace of a map with a spectator strand is its whiskered partial trace. -/
theorem trace_whisker (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (A X Y T : C.Obj) (g : X ⊗ T ⟶ Y ⊗ T) :
    CentreInduction.partialTraceHom p (A ⊗ X) (A ⊗ Y) T
      ((α_ A X T).hom ≫ (A ◁ g) ≫ (α_ A Y T).inv) =
    A ◁ CentreInduction.partialTraceHom p X Y T g := by
  simp only [CentreInduction.partialTraceHom, LinearMap.coe_mk, AddHom.coe_mk,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Closing the inner factor of a tensor winding gives the outer winding of its closed trace. -/
theorem trace_inner_winding_tensor (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (X Y : Center C.Obj) (f : X.1 ⟶ Y.1) (T U : C.Obj) :
    CentreInduction.partialTraceHom p (X.1 ⊗ T) (Y.1 ⊗ T) U
      ((α_ X.1 T U).hom ≫ CentreInduction.winding C X Y (T ⊗ U) f ≫ (α_ Y.1 T U).inv) =
    CentreInduction.winding C X Y T
      (CentreInduction.partialTraceHom p X.1 Y.1 U (CentreInduction.winding C X Y U f)) := by
  rw [winding_tensor]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [CentreInduction.partialTraceHom_precompose]
  have hh : (α_ T X.1 U).hom ≫ (T ◁ CentreInduction.winding C X Y U f) ≫
      (α_ T Y.1 U).inv ≫ ((Y.2.β T).inv ▷ U) =
    ((α_ T X.1 U).hom ≫ (T ◁ CentreInduction.winding C X Y U f) ≫
      (α_ T Y.1 U).inv) ≫ ((Y.2.β T).inv ▷ U) := by simp [Category.assoc]
  rw [hh, CentreInduction.partialTraceHom_postcompose, trace_whisker]
  rfl

end PropertyF.Ground.CentreRigid
