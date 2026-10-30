module
public import MTC.CategoryTheory.Dimensions.DoubleDualUnitTensor
public import MTC.CategoryTheory.Dimensions.FourthDualUnit
public import MTC.CategoryTheory.Dimensions.DefectNaturality

open MTC.Braided

/-! # Unit laws for the fourth-dual root

The tensor unit and unit labels satisfy the coherence identities for the root tensor defect.

## Main results

* `rootTensorIso_unit_left`: computes the left unit component of the fourth-dual root comparison.
* `rootTensorDefect_unit_left`: computes the tensor defect at the left unit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
set_option backward.isDefEq.respectTransparency false in
/-- The root tensor map with a unit factor has the root's unit sign. -/
theorem rootTensorIso_unit_left :
    (rootTensorIso C (𝟙_ C.Obj) X).hom =
      rootDimension C (unitIndex C) • ((fourthDualRootNaturalIso C).app (𝟙_ C.Obj ⊗ X)).hom := by
  let I := 𝟙_ C.Obj
  apply (cancel_mono (rightDualIsoMap (rightDualIsoMap (λ_ X))).hom).1
  change (rootTensorIso C I X).hom ≫ (((λ_ X).homᘁ)ᘁ) =
    (rootDimension C (unitIndex C) • ((fourthDualRootNaturalIso C).app (I ⊗ X)).hom) ≫
      (((λ_ X).homᘁ)ᘁ)
  have hnat : (λ_ X).hom ≫ ((fourthDualRootNaturalIso C).app X).hom =
      ((fourthDualRootNaturalIso C).app (I ⊗ X)).hom ≫ (((λ_ X).homᘁ)ᘁ) :=
    (fourthDualRootNaturalIso C).hom.naturality (λ_ X).hom
  rw [Linear.smul_comp, ← hnat]
  change ((((fourthDualRootNaturalIso C).app I).hom ⊗ₘ
    ((fourthDualRootNaturalIso C).app X).hom) ≫ (doubleDualTensorIso I X).hom) ≫
      (((λ_ X).homᘁ)ᘁ) = _
  rw [tensorHom_def', fourthDualRoot_unit_component]
  simp only [doubleDualFunctor, Functor.id_obj, MonoidalLinear.smul_whiskerRight,
    Linear.comp_smul, Linear.smul_comp, Category.assoc]
  rw [doubleDualTensorIso_unit_left, leftUnitor_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- The ENO tensor defect with a left unit factor is its unit sign. -/
theorem rootTensorDefect_unit_left :
    (rootTensorDefect C (𝟙_ C.Obj) X).hom =
      rootDimension C (unitIndex C) • 𝟙 (𝟙_ C.Obj ⊗ X) :=
  (cancel_mono (rootTensorIso C (𝟙_ C.Obj) X).hom).1 <| by
    change (((fourthDualRootNaturalIso C).app (𝟙_ C.Obj ⊗ X)).hom ≫
      (rootTensorIso C (𝟙_ C.Obj) X).inv) ≫ (rootTensorIso C (𝟙_ C.Obj) X).hom =
        (rootDimension C (unitIndex C) • 𝟙 _) ≫ (rootTensorIso C (𝟙_ C.Obj) X).hom
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Linear.smul_comp]
    erw [rootTensorIso_unit_left, Linear.comp_smul, smul_smul, rootDimension_unit_sq,
      one_smul, Category.id_comp]

end MTC.CategoryTheory.Dimensions
