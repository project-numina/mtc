module
public import PropertyF.Ground.Dimensions.DoubleDualUnitTensor
public import PropertyF.Ground.Dimensions.FourthDualUnit
public import PropertyF.Ground.Dimensions.DefectNaturality

/-! # Unit laws for the fourth-dual root

The tensor unit and unit labels satisfy the coherence identities for the root tensor defect.

## Main results

* `rootTensorIso_unit_left`: computes the left unit component of the fourth-dual root comparison.
* `rootTensorDefect_unit_right`: computes the tensor defect at the right unit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

/-- For an involutive scalar, an isomorphism is its scalar multiple precisely when
the quotient of the two isomorphisms is scalar. -/
theorem iso_comp_inv_eq_smul_iff_of_sq_one {D : Type u} [Category.{v} D]
    [Preadditive D] [Linear ℂ D] {X Y : D} (a t : X ≅ Y) (z : ℂ) (hz : z * z = 1) :
    a.hom ≫ t.inv = z • 𝟙 X ↔ t.hom = z • a.hom := by
  constructor
  · intro h
    have hcomp : z • t.hom = a.hom := by
      have h' := congrArg (fun f => f ≫ t.hom) h
      simpa [Category.assoc, Linear.smul_comp] using h'.symm
    have h' := congrArg (fun f => z • f) hcomp
    simpa [smul_smul, hz] using h'
  · intro ht
    apply (cancel_mono t.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Linear.smul_comp,
      Category.id_comp]
    rw [ht, smul_smul, hz, one_smul]

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The root tensor map with a unit factor has the root's unit sign. -/
theorem rootTensorIso_unit_left (X : C.Obj) :
    (rootTensorIso C (𝟙_ C.Obj) X).hom =
      rootDimension C (unitIndex C) • ((fourthDualRootNaturalIso C).app (𝟙_ C.Obj ⊗ X)).hom := by
  let I := 𝟙_ C.Obj
  let : HasRightDual I := RightRigidCategory.rightDual I
  let : HasRightDual (Iᘁ) := RightRigidCategory.rightDual (Iᘁ)
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

/-- The ENO tensor defect with a left unit factor is its unit sign. -/
theorem rootTensorDefect_unit_left (X : C.Obj) :
    (rootTensorDefect C (𝟙_ C.Obj) X).hom =
      rootDimension C (unitIndex C) • 𝟙 (𝟙_ C.Obj ⊗ X) :=
  (iso_comp_inv_eq_smul_iff_of_sq_one _ _ _ (rootDimension_unit_sq C)).2
    (rootTensorIso_unit_left C X)
set_option backward.isDefEq.respectTransparency false in
/-- The root tensor map with a unit factor has the root's unit sign. -/
theorem rootTensorIso_unit_right (X : C.Obj) :
    (rootTensorIso C X (𝟙_ C.Obj)).hom =
      rootDimension C (unitIndex C) • ((fourthDualRootNaturalIso C).app (X ⊗ 𝟙_ C.Obj)).hom := by
  let I := 𝟙_ C.Obj
  let : HasRightDual I := RightRigidCategory.rightDual I
  let : HasRightDual (Iᘁ) := RightRigidCategory.rightDual (Iᘁ)
  apply (cancel_mono (rightDualIsoMap (rightDualIsoMap (ρ_ X))).hom).1
  change (rootTensorIso C X I).hom ≫ (((ρ_ X).homᘁ)ᘁ) =
    (rootDimension C (unitIndex C) • ((fourthDualRootNaturalIso C).app (X ⊗ I)).hom) ≫
      (((ρ_ X).homᘁ)ᘁ)
  have hnat : (ρ_ X).hom ≫ ((fourthDualRootNaturalIso C).app X).hom =
      ((fourthDualRootNaturalIso C).app (X ⊗ I)).hom ≫ (((ρ_ X).homᘁ)ᘁ) :=
    (fourthDualRootNaturalIso C).hom.naturality (ρ_ X).hom
  rw [Linear.smul_comp, ← hnat]
  change ((((fourthDualRootNaturalIso C).app X).hom ⊗ₘ
    ((fourthDualRootNaturalIso C).app I).hom) ≫ (doubleDualTensorIso X I).hom) ≫
      (((ρ_ X).homᘁ)ᘁ) = _
  rw [tensorHom_def, fourthDualRoot_unit_component]
  simp only [doubleDualFunctor, Functor.id_obj, MonoidalLinear.whiskerLeft_smul,
    Linear.comp_smul, Linear.smul_comp, Category.assoc]
  rw [doubleDualTensorIso_unit_right, rightUnitor_naturality]

/-- The ENO tensor defect with a right unit factor is its unit sign. -/
theorem rootTensorDefect_unit_right (X : C.Obj) :
    (rootTensorDefect C X (𝟙_ C.Obj)).hom =
      rootDimension C (unitIndex C) • 𝟙 (X ⊗ 𝟙_ C.Obj) :=
  (iso_comp_inv_eq_smul_iff_of_sq_one _ _ _ (rootDimension_unit_sq C)).2
    (rootTensorIso_unit_right C X)
/-- The left-unit defect formula holds for the chosen simple representative. -/
theorem rootTensorDefect_unitLabel_left (X : C.Obj) :
    (rootTensorDefect C (simples C (unitIndex C)) X).hom =
      rootDimension C (unitIndex C) • 𝟙 (simples C (unitIndex C) ⊗ X) :=
  (unitIndex_iso C).elim fun e ↦ (cancel_mono (e.hom ▷ X)).1 (by
    simpa [rootTensorDefect_unit_left, Linear.comp_smul, Linear.smul_comp] using
      (rootTensorDefect_natural C e.hom (𝟙 X)).symm)

/-- The right-unit defect formula holds for the chosen simple representative. -/
theorem rootTensorDefect_unitLabel_right (X : C.Obj) :
    (rootTensorDefect C X (simples C (unitIndex C))).hom =
      rootDimension C (unitIndex C) • 𝟙 (X ⊗ simples C (unitIndex C)) :=
  (unitIndex_iso C).elim fun e ↦ (cancel_mono (X ◁ e.hom)).1 (by
    simpa [rootTensorDefect_unit_right, Linear.comp_smul, Linear.smul_comp] using
      (rootTensorDefect_natural C (𝟙 X) e.hom).symm)


end PropertyF.Ground.Dimensions
