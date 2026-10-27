module
public import PropertyF.Ground.Dimensions.RootDualPairing
public import PropertyF.Ground.Dimensions.DoubleDualPairing
public import PropertyF.Ground.Dimensions.MultiplicityDefect

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The root tensor defect acts on a simple duality cup by the product of the unit-root and dual signs. -/
theorem rootTensorDefect_coevaluation (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) :
    let X := Ground.simples C i
    η_ X (Xᘁ) ≫ (rootTensorDefect C X (Xᘁ)).hom =
      (rootDimension C (Ground.unitIndex C) * rootDualSign C i) • η_ X (Xᘁ) := by
  let I := 𝟙_ C.Obj
  let : HasRightDual I := RightRigidCategory.rightDual I
  let X := Ground.simples C i
  let W := X ⊗ (Xᘁ)
  let : HasRightDual W := RightRigidCategory.rightDual W
  let a := (fourthDualRootNaturalIso C).app X
  let b := (fourthDualRootNaturalIso C).app (Xᘁ)
  let t := rootTensorIso C X (Xᘁ)
  let u := rootDimension C (Ground.unitIndex C)
  let e := rootDualSign C i
  have he : e * e = 1 := rootDualSign_sq C i
  have hc := root_components_coevaluation C i
  change η_ X (Xᘁ) ≫ (a.hom ⊗ₘ b.hom) = e • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) at hc
  have hn := (fourthDualRootNaturalIso C).hom.naturality (η_ X (Xᘁ))
  change η_ X (Xᘁ) ≫ ((fourthDualRootNaturalIso C).app W).hom =
    ((fourthDualRootNaturalIso C).app I).hom ≫ (((η_ X (Xᘁ))ᘁ)ᘁ) at hn
  have hunit := fourthDualRoot_unit_component C
  change ((fourthDualRootNaturalIso C).app I).hom = u • (doubleDualUnitIso (C := C.Obj)).hom at hunit
  have hdual := doubleDual_coevaluation X
  have ht : η_ X (Xᘁ) ≫ t.hom =
      e • ((doubleDualUnitIso (C := C.Obj)).hom ≫ (((η_ X (Xᘁ))ᘁ)ᘁ)) := by
    change η_ X (Xᘁ) ≫ ((a.hom ⊗ₘ b.hom) ≫ (doubleDualTensorIso X (Xᘁ)).hom) = _
    rw [← Category.assoc, hc]
    simp only [Linear.smul_comp]
    congr 1
    apply (cancel_mono (doubleDualTensorIso X (Xᘁ)).inv).1
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hdual.symm
  apply (cancel_mono t.hom).1
  change (η_ X (Xᘁ) ≫ (((fourthDualRootNaturalIso C).app W).hom ≫ t.inv)) ≫ t.hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Linear.smul_comp]
  rw [hn, hunit, Linear.smul_comp, ht]
  rw [← mul_smul, mul_assoc, he, mul_one]
end PropertyF.Ground.Dimensions
