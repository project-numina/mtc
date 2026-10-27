module
public import PropertyF.Ground.CentreRigid.Evaluation
public import PropertyF.Ground.CentreInduction.ForgetDual

/-! The chosen centre duals require no comparison maps after forgetting. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreRigid
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The standard forgetful dual comparison is the identity. -/
theorem forgetDualIso_eq_refl (C : BraidedFusionCategory.{v,u}) (Z : Center C.Obj) :
    letI := CentreRigid.rigidCenter (C := C.Obj)
    CentreInduction.forgetDualIso C Z = Iso.refl Z.1ᘁ := by
  letI := CentreRigid.rigidCenter (C := C.Obj)
  change rightDualIso (CentreInduction.forgetPairing C Z) HasRightDual.exact = Iso.refl Z.1ᘁ
  rw [show CentreInduction.forgetPairing C Z = HasRightDual.exact from rfl]
  exact rightDualIso_id _

set_option backward.isDefEq.respectTransparency false in
/-- The standard forgetful double-dual comparison is the identity. -/
theorem forgetDoubleDualIso_eq_refl (C : BraidedFusionCategory.{v,u}) (Z : Center C.Obj) :
    letI := CentreRigid.rigidCenter (C := C.Obj)
    CentreInduction.forgetDoubleDualIso C Z = Iso.refl ((Z.1ᘁ)ᘁ) := by
  letI := CentreRigid.rigidCenter (C := C.Obj)
  unfold CentreInduction.forgetDoubleDualIso
  rw [forgetDualIso_eq_refl C (Zᘁ), forgetDualIso_eq_refl C Z]
  apply Iso.ext
  simp only [Dimensions.rightDualIsoMap, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv, Iso.refl_inv, Iso.refl_hom, rightAdjointMate_id]
  change 𝟙 ((Z.1ᘁ)ᘁ) ≫ 𝟙 ((Z.1ᘁ)ᘁ) = 𝟙 ((Z.1ᘁ)ᘁ)
  simp

end PropertyF.Ground.CentreRigid
