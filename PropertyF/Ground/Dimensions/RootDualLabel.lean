module
public import PropertyF.Ground.Dimensions.ENOFrobenius

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The ENO root at the chosen dual label, transported from the actual right dual. -/
theorem rootDualSign_label (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    ((fourthDualRootNaturalIso C).app (Ground.simples C (Ground.dualIndex C i))).hom =
      rootDualSign C i • ((rightDualLabelIso C i).inv ≫
        (rightDualIsoMap ((fourthDualRootNaturalIso C).app (Ground.simples C i))).symm.hom ≫
        (((rightDualLabelIso C i).homᘁ)ᘁ)) := by
  have hn := (fourthDualRootNaturalIso C).hom.naturality (rightDualLabelIso C i).hom
  change (rightDualLabelIso C i).hom ≫
      ((fourthDualRootNaturalIso C).app (Ground.simples C (Ground.dualIndex C i))).hom =
      ((fourthDualRootNaturalIso C).app ((Ground.simples C i)ᘁ)).hom ≫
        (((rightDualLabelIso C i).homᘁ)ᘁ) at hn
  rw [rootDualSign_component] at hn
  apply (cancel_epi (rightDualLabelIso C i).hom).1
  simp only [Linear.comp_smul, Iso.hom_inv_id_assoc]
  simpa only [Linear.smul_comp] using hn
/-- The ENO signs agree on the chosen dual label. -/
theorem rootDualSign_dual (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    rootDualSign C (Ground.dualIndex C i) = rootDualSign C i := by
  let X := Ground.simples C i
  let Y := Ground.simples C (Ground.dualIndex C i)
  let : Simple X := Ground.simples_simple C i
  let : Simple Y := Ground.simples_simple C _
  let : Simple (Xᘁ) := simple_rightDual C X
  have he : Ground.squaredNorm C Y = Ground.squaredNorm C X := by
    rw [← target_squaredNorm_iso C (rightDualLabelIso C i)]
    exact target_squaredNorm_rightDual C X
  rw [squaredNorm_eq_rootDualSign_mul, squaredNorm_eq_rootDualSign_mul] at he
  rw [Ground.dualIndex_involutive] at he
  have hd := rootDimension_ne_zero C i
  have he' := rootDimension_ne_zero C (Ground.dualIndex C i)
  have hc : rootDualSign C (Ground.dualIndex C i) *
      (rootDimension C i * rootDimension C (Ground.dualIndex C i)) =
      rootDualSign C i * (rootDimension C i * rootDimension C (Ground.dualIndex C i)) := by
    calc
      _ = rootDualSign C (Ground.dualIndex C i) * rootDimension C (Ground.dualIndex C i) * rootDimension C i := by ring
      _ = rootDualSign C i * rootDimension C i * rootDimension C (Ground.dualIndex C i) := he
      _ = _ := by ring
  exact mul_right_cancel₀ (mul_ne_zero hd he') hc
end PropertyF.Ground.Dimensions
