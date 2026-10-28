module
public import PropertyF.Ground.Dimensions.DoubleDualUnitTensor
public import PropertyF.Ground.Dimensions.FourthDualUnit
public import PropertyF.Ground.Dimensions.DefectNaturality

/-! # Unit laws for the fourth-dual root

The tensor unit and unit labels satisfy the coherence identities for the root tensor defect.

## Main results

* `rootTensorIso_unit_left`: computes the left unit component of the fourth-dual root comparison.
* `rootTensorDefect_unit_left`: computes the tensor defect at the left unit.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

/-- For an involutive scalar, an isomorphism is its scalar multiple precisely when
the quotient of the two isomorphisms is scalar. -/
theorem iso_comp_inv_eq_smul_iff_of_sq_one {k : Type*} [CommSemiring k]
    {D : Type u} [Category.{v} D] [Preadditive D] [Linear k D]
    {X Y : D} (a t : X ≅ Y) (z : k) (hz : z * z = 1) :
    a.hom ≫ t.inv = z • 𝟙 X ↔ t.hom = z • a.hom := by
  constructor
  · intro h
    simpa [Category.assoc, Linear.smul_comp, smul_smul, hz] using
      (congrArg (fun f ↦ z • (f ≫ t.hom)) h).symm
  · intro ht
    apply (cancel_mono t.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Linear.smul_comp,
      Category.id_comp]
    rw [ht, smul_smul, hz, one_smul]

variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
set_option backward.isDefEq.respectTransparency false in
/-- The root tensor map with a unit factor has the root's unit sign. -/
theorem rootTensorIso_unit_left :
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
theorem rootTensorDefect_unit_left :
    (rootTensorDefect C (𝟙_ C.Obj) X).hom =
      rootDimension C (unitIndex C) • 𝟙 (𝟙_ C.Obj ⊗ X) :=
  (iso_comp_inv_eq_smul_iff_of_sq_one _ _ _ (rootDimension_unit_sq C)).2
    (rootTensorIso_unit_left C X)

end PropertyF.Ground.Dimensions
