module
public import PropertyF.Ground.Dimensions.DoubleDualUnitTensor
public import PropertyF.Ground.Dimensions.RootDualPairing
public import PropertyF.Ground.Dimensions.DefectNaturality

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The root tensor map with a unit factor has the root's unit sign. -/
theorem rootTensorIso_unit_left (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (rootTensorIso C (𝟙_ C.Obj) X).hom =
      rootDimension C (Ground.unitIndex C) • ((fourthDualRootNaturalIso C).app (𝟙_ C.Obj ⊗ X)).hom := by
  let I := 𝟙_ C.Obj
  let : HasRightDual I := RightRigidCategory.rightDual I
  let : HasRightDual (Iᘁ) := RightRigidCategory.rightDual (Iᘁ)
  let a := (fourthDualRootNaturalIso C).app X
  let b := (fourthDualRootNaturalIso C).app (I ⊗ X)
  let z := rootDimension C (Ground.unitIndex C)
  let L := rightDualIsoMap (rightDualIsoMap (λ_ X))
  have hnat : (λ_ X).hom ≫ a.hom = b.hom ≫ (((λ_ X).homᘁ)ᘁ) :=
    (fourthDualRootNaturalIso C).hom.naturality (λ_ X).hom
  have hu : ((fourthDualRootNaturalIso C).app I).hom = z • (doubleDualUnitIso (C := C.Obj)).hom :=
    fourthDualRoot_unit_component C
  have ht : (rootTensorIso C I X).hom ≫ (((λ_ X).homᘁ)ᘁ) =
      z • ((λ_ X).hom ≫ a.hom) := by
    change ((((fourthDualRootNaturalIso C).app I).hom ⊗ₘ a.hom) ≫
      (doubleDualTensorIso I X).hom) ≫ (((λ_ X).homᘁ)ᘁ) = _
    rw [tensorHom_def', hu]
    simp only [doubleDualFunctor, Functor.id_obj, MonoidalLinear.smul_whiskerRight, Linear.comp_smul, Linear.smul_comp, Category.assoc]
    rw [doubleDualTensorIso_unit_left, leftUnitor_naturality]
  apply (cancel_mono L.hom).1
  change (rootTensorIso C I X).hom ≫ (((λ_ X).homᘁ)ᘁ) =
    (z • b.hom) ≫ (((λ_ X).homᘁ)ᘁ)
  calc
    _ = z • ((λ_ X).hom ≫ a.hom) := ht
    _ = _ := by
      have hh := congrArg (fun f => z • f) hnat
      simpa only [doubleDualFunctor, Functor.id_obj, Linear.smul_comp] using hh

/-- The ENO tensor defect with a left unit factor is its unit sign. -/
theorem rootTensorDefect_unit_left (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (rootTensorDefect C (𝟙_ C.Obj) X).hom =
      rootDimension C (Ground.unitIndex C) • 𝟙 (𝟙_ C.Obj ⊗ X) := by
  let I := 𝟙_ C.Obj
  let z := rootDimension C (Ground.unitIndex C)
  let T := rootTensorIso C I X
  let A := (fourthDualRootNaturalIso C).app (I ⊗ X)
  have ht : T.hom = z • A.hom := rootTensorIso_unit_left C X
  have hz : z * z = 1 := rootDimension_unit_sq C
  apply (cancel_mono T.hom).1
  change (A.hom ≫ T.inv) ≫ T.hom = (z • 𝟙 (I ⊗ X)) ≫ T.hom
  have hleft : (A.hom ≫ T.inv) ≫ T.hom = A.hom := by
    simp only [doubleDualFunctor, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hsmul : z • (z • A.hom) = A.hom := by
    rw [smul_smul, hz, one_smul]
  have hright : (z • 𝟙 (I ⊗ X)) ≫ T.hom = A.hom := by
    rw [Linear.smul_comp, Category.id_comp, ht]
    exact hsmul
  exact hleft.trans hright.symm
set_option backward.isDefEq.respectTransparency false in
/-- The root tensor map with a unit factor has the root's unit sign. -/
theorem rootTensorIso_unit_right (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (rootTensorIso C X (𝟙_ C.Obj)).hom =
      rootDimension C (Ground.unitIndex C) • ((fourthDualRootNaturalIso C).app (X ⊗ 𝟙_ C.Obj)).hom := by
  let I := 𝟙_ C.Obj
  let : HasRightDual I := RightRigidCategory.rightDual I
  let : HasRightDual (Iᘁ) := RightRigidCategory.rightDual (Iᘁ)
  let a := (fourthDualRootNaturalIso C).app X
  let b := (fourthDualRootNaturalIso C).app (X ⊗ I)
  let z := rootDimension C (Ground.unitIndex C)
  let L := rightDualIsoMap (rightDualIsoMap (ρ_ X))
  have hnat : (ρ_ X).hom ≫ a.hom = b.hom ≫ (((ρ_ X).homᘁ)ᘁ) :=
    (fourthDualRootNaturalIso C).hom.naturality (ρ_ X).hom
  have hu : ((fourthDualRootNaturalIso C).app I).hom = z • (doubleDualUnitIso (C := C.Obj)).hom :=
    fourthDualRoot_unit_component C
  have ht : (rootTensorIso C X I).hom ≫ (((ρ_ X).homᘁ)ᘁ) =
      z • ((ρ_ X).hom ≫ a.hom) := by
    change ((a.hom ⊗ₘ ((fourthDualRootNaturalIso C).app I).hom) ≫
      (doubleDualTensorIso X I).hom) ≫ (((ρ_ X).homᘁ)ᘁ) = _
    rw [tensorHom_def, hu]
    simp only [doubleDualFunctor, Functor.id_obj, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul, Linear.smul_comp, Category.assoc]
    rw [doubleDualTensorIso_unit_right, rightUnitor_naturality]
  apply (cancel_mono L.hom).1
  change (rootTensorIso C X I).hom ≫ (((ρ_ X).homᘁ)ᘁ) =
    (z • b.hom) ≫ (((ρ_ X).homᘁ)ᘁ)
  calc
    _ = z • ((ρ_ X).hom ≫ a.hom) := ht
    _ = _ := by
      have hh := congrArg (fun f => z • f) hnat
      simpa only [doubleDualFunctor, Functor.id_obj, Linear.smul_comp] using hh

/-- The ENO tensor defect with a right unit factor is its unit sign. -/
theorem rootTensorDefect_unit_right (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (rootTensorDefect C X (𝟙_ C.Obj)).hom =
      rootDimension C (Ground.unitIndex C) • 𝟙 (X ⊗ 𝟙_ C.Obj) := by
  let I := 𝟙_ C.Obj
  let z := rootDimension C (Ground.unitIndex C)
  let T := rootTensorIso C X I
  let A := (fourthDualRootNaturalIso C).app (X ⊗ I)
  have ht : T.hom = z • A.hom := rootTensorIso_unit_right C X
  have hz : z * z = 1 := rootDimension_unit_sq C
  apply (cancel_mono T.hom).1
  change (A.hom ≫ T.inv) ≫ T.hom = (z • 𝟙 (X ⊗ I)) ≫ T.hom
  have hleft : (A.hom ≫ T.inv) ≫ T.hom = A.hom := by
    simp only [doubleDualFunctor, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hsmul : z • (z • A.hom) = A.hom := by
    rw [smul_smul, hz, one_smul]
  have hright : (z • 𝟙 (X ⊗ I)) ≫ T.hom = A.hom := by
    rw [Linear.smul_comp, Category.id_comp, ht]
    exact hsmul
  exact hleft.trans hright.symm
/-- The left-unit defect formula holds for the chosen simple representative. -/
theorem rootTensorDefect_unitLabel_left (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (rootTensorDefect C (Ground.simples C (Ground.unitIndex C)) X).hom =
      rootDimension C (Ground.unitIndex C) • 𝟙 (Ground.simples C (Ground.unitIndex C) ⊗ X) := by
  obtain ⟨e⟩ := Ground.unitIndex_iso C
  let E := e ⊗ᵢ Iso.refl X
  apply (cancel_mono E.hom).1
  have h := rootTensorDefect_natural C e.hom (𝟙 X)
  change E.hom ≫ (rootTensorDefect C (𝟙_ C.Obj) X).hom =
    (rootTensorDefect C (Ground.simples C (Ground.unitIndex C)) X).hom ≫ E.hom at h
  rw [← h, rootTensorDefect_unit_left]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

/-- The right-unit defect formula holds for the chosen simple representative. -/
theorem rootTensorDefect_unitLabel_right (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (rootTensorDefect C X (Ground.simples C (Ground.unitIndex C))).hom =
      rootDimension C (Ground.unitIndex C) • 𝟙 (X ⊗ Ground.simples C (Ground.unitIndex C)) := by
  obtain ⟨e⟩ := Ground.unitIndex_iso C
  let E := Iso.refl X ⊗ᵢ e
  apply (cancel_mono E.hom).1
  have h := rootTensorDefect_natural C (𝟙 X) e.hom
  change E.hom ≫ (rootTensorDefect C X (𝟙_ C.Obj)).hom =
    (rootTensorDefect C X (Ground.simples C (Ground.unitIndex C))).hom ≫ E.hom at h
  rw [← h, rootTensorDefect_unit_right]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Squaring the root tensor map gives the tensor of the fourth-dual maps,
with the canonical iterated double-dual tensor comparison. -/
theorem rootTensor_square_eq_fourthDual_tensor (C : Ground.BraidedFusionCategory.{v,u})
    (X Y : C.Obj) :
    (rootTensorIso C X Y).hom ≫ (((rootTensorIso C X Y).homᘁ)ᘁ) =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ) := by
  have hx := congrArg (fun n => (n.app X).hom) (fourthDualRootNaturalSquare_eq C)
  have hy := congrArg (fun n => (n.app Y).hom) (fourthDualRootNaturalSquare_eq C)
  change ((fourthDualRootNaturalIso C).app X).hom ≫
    ((((fourthDualRootNaturalIso C).app X).homᘁ)ᘁ) = (fourthDualIso C X).hom at hx
  change ((fourthDualRootNaturalIso C).app Y).hom ≫
    ((((fourthDualRootNaturalIso C).app Y).homᘁ)ᘁ) = (fourthDualIso C Y).hom at hy
  rw [← hx, ← hy]
  simp only [rootTensorIso, Iso.trans_hom, tensorIso_hom, comp_rightAdjointMate,
    Category.assoc]
  have hn := doubleDualTensorIso_natural ((fourthDualRootNaturalIso C).app X).hom
    ((fourthDualRootNaturalIso C).app Y).hom
  have hn2 := congrArg (fun f =>
    (((fourthDualRootNaturalIso C).app X).hom ⊗ₘ
      ((fourthDualRootNaturalIso C).app Y).hom) ≫ f ≫
      (((doubleDualTensorIso X Y).homᘁ)ᘁ)) hn.symm
  simp only [Functor.id_obj, doubleDualFunctor, Category.assoc] at hn2
  rw [hn2]
  rw [tensorHom_comp_tensorHom_assoc]

end PropertyF.Ground.Dimensions
