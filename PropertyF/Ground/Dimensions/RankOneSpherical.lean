module
public import PropertyF.Ground.Dimensions.FourthTensorUnit
public import PropertyF.Ground.Dimensions.CoevaluationSliding

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- A signed scalar tensor defect forces the fourth-dual tensor law. -/
theorem fourthDualIso_tensor_of_signed_defect (C : Ground.BraidedFusionCategory.{v,u})
    (X Y : C.Obj) (z : ℂ) (hz : z * z = 1)
    (hd : (rootTensorDefect C X Y).hom = z • 𝟙 (X ⊗ Y)) :
    (fourthDualIso C (X ⊗ Y)).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ) := by
  let T := rootTensorIso C X Y
  let A := (fourthDualRootNaturalIso C).app (X ⊗ Y)
  have hcomp : (z • 𝟙 (X ⊗ Y)) ≫ T.hom = A.hom := by
    rw [← hd]
    change (A.hom ≫ T.inv) ≫ T.hom = A.hom
    simp only [doubleDualFunctor, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hcomp' : z • T.hom = A.hom := by simpa [Linear.smul_comp] using hcomp
  have ht : T.hom = z • A.hom := by
    have hm := congrArg (fun f => z • f) hcomp'
    simp only [smul_smul, hz, one_smul] at hm
    exact hm
  have hsq : T.hom ≫ ((T.homᘁ)ᘁ) = (fourthDualIso C (X ⊗ Y)).hom := by
    rw [ht]
    simp only [rightAdjointMate_smul, Linear.smul_comp, Linear.comp_smul, smul_smul,
      hz, one_smul]
    exact congrArg (fun n => (n.app (X ⊗ Y)).hom) (fourthDualRootNaturalSquare_eq C)
  exact hsq.symm.trans (rootTensor_square_eq_fourthDual_tensor C X Y)

/-- The fourth-dual tensor law holds when the left factor is the chosen unit
simple representative. -/
theorem fourthDualIso_tensor_unitLabel_left (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (fourthDualIso C (Ground.simples C (Ground.unitIndex C) ⊗ X)).hom =
      ((fourthDualIso C (Ground.simples C (Ground.unitIndex C))).hom ⊗ₘ (fourthDualIso C X).hom) ≫
        (doubleDualTensorIso (((Ground.simples C (Ground.unitIndex C))ᘁ)ᘁ) ((Xᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso (Ground.simples C (Ground.unitIndex C)) X).homᘁ)ᘁ) :=
  fourthDualIso_tensor_of_signed_defect C _ _ (rootDimension C (Ground.unitIndex C))
    (rootDimension_unit_sq C) (rootTensorDefect_unitLabel_left C X)

/-- The fourth-dual tensor law holds when the right factor is the chosen unit
simple representative. -/
theorem fourthDualIso_tensor_unitLabel_right (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (fourthDualIso C (X ⊗ Ground.simples C (Ground.unitIndex C))).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C (Ground.simples C (Ground.unitIndex C))).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) (((Ground.simples C (Ground.unitIndex C))ᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X (Ground.simples C (Ground.unitIndex C))).homᘁ)ᘁ) :=
  fourthDualIso_tensor_of_signed_defect C _ _ (rootDimension C (Ground.unitIndex C))
    (rootDimension_unit_sq C) (rootTensorDefect_unitLabel_right C X)
end PropertyF.Ground.Dimensions
