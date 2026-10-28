module
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Dimensions.DefectNaturality

/-! # Fourth duals of the tensor unit

The fourth-dual maps satisfy unit identities and their roots interact with coevaluation.

## Main results

* `fourthDualIso_unit`: identifies the fourth-dual isomorphism on the unit.
* `rootDimension_unit_sq`: shows that the root dimension of the unit is a sign.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- The braided double-dual map has the canonical component on the unit. -/
theorem drinfeld_unit :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
    letI : HasRightDual ((𝟙_ C)ᘁ) := RightRigidCategory.rightDual _
    (drinfeldIso (𝟙_ C)).hom = (doubleDualUnitIso (C := C)).hom := by
  let U : C := 𝟙_ C
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let r : Uᘁ ≅ U := rightDualUnitIso
  have h : (r.inv ≫ (r.homᘁ)) ▷ (Uᘁ) ≫ ε_ (Uᘁ) ((Uᘁ)ᘁ) =
      (β_ U (Uᘁ)).hom ≫ ε_ U (Uᘁ) := by
    rw [comp_whiskerRight_assoc, rightAdjointMate_comp_evaluation]
    have hn := braiding_naturality_right U r.hom
    simp only [U, braiding_tensorUnit_left, unitors_equal, Iso.hom_inv_id,
      Category.comp_id] at hn
    rw [← whisker_exchange_assoc, ← Category.assoc, hn]
    simp only [Category.assoc, ← comp_whiskerRight_assoc, Iso.hom_inv_id,
      id_whiskerRight, Category.id_comp, U, braiding_tensorUnit_left]
  change (doubleDualUnitIso (C := C)).hom ▷ (Uᘁ) ≫ ε_ (Uᘁ) ((Uᘁ)ᘁ) = _ at h
  exact evaluation_ext ((drinfeld_eval U).trans h.symm)
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

section
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- The Drinfeld map respects duality on the tensor unit. -/
theorem drinfeld_unit_dual :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
    drinfeldIso (rightDualObject (𝟙_ C)) =
      (rightDualIsoMap (drinfeldIso (𝟙_ C))).symm := by
  let U : C := 𝟙_ C
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let : HasRightDual ((Uᘁ)ᘁ) := RightRigidCategory.rightDual ((Uᘁ)ᘁ)
  let r : Uᘁ ≅ U := rightDualUnitIso
  have hu : (drinfeldIso U).hom = (r.inv ≫ (r.homᘁ)) :=
    drinfeld_unit
  apply Iso.ext
  change (drinfeldIso (Uᘁ)).hom = ((drinfeldIso U).invᘁ)
  apply (cancel_mono (rightDualIsoMap (rightDualIsoMap r)).hom).1
  change (drinfeldIso (Uᘁ)).hom ≫ ((r.homᘁ)ᘁ) =
    ((drinfeldIso U).invᘁ) ≫ ((r.homᘁ)ᘁ)
  rw [← drinfeldIso_natural r.hom, hu, Iso.hom_inv_id_assoc]
  rw [show (drinfeldIso U).inv = (r.invᘁ) ≫ r.hom from by
      simpa only [Iso.trans_inv, Iso.symm_inv, rightDualIsoMap] using
        congrArg Iso.inv (Iso.ext hu : drinfeldIso U = r.symm ≪≫ rightDualIsoMap r),
    comp_rightAdjointMate, Category.assoc, ← comp_rightAdjointMate,
    show (r.homᘁ) ≫ (r.invᘁ) = 𝟙 (Uᘁ) from (rightDualIsoMap r).hom_inv_id,
    rightAdjointMate_id, Category.comp_id]
/-- The fourth-dual map has the canonical iterated unit component. -/
theorem fourthDualIso_unit :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    letI : HasRightDual ((𝟙_ C)ᘁ) := RightRigidCategory.rightDual ((𝟙_ C)ᘁ)
    letI : HasRightDual (((𝟙_ C)ᘁ)ᘁ) := RightRigidCategory.rightDual (((𝟙_ C)ᘁ)ᘁ)
    fourthDualIso (𝟙_ C) =
      doubleDualUnitIso (C := C) ≪≫
        rightDualIsoMap (rightDualIsoMap (doubleDualUnitIso (C := C))) := by
  let : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
  let : HasRightDual ((𝟙_ C)ᘁ) := RightRigidCategory.rightDual ((𝟙_ C)ᘁ)
  let : HasRightDual (((𝟙_ C)ᘁ)ᘁ) := RightRigidCategory.rightDual (((𝟙_ C)ᘁ)ᘁ)
  unfold fourthDualIso
  rw [show drinfeldIso ((𝟙_ C)ᘁ) =
      (rightDualIsoMap (drinfeldIso (𝟙_ C))).symm from drinfeld_unit_dual,
    show drinfeldIso (𝟙_ C) = doubleDualUnitIso from Iso.ext (drinfeld_unit (C := C))]
  apply Iso.ext
  rfl

end

variable (C : BraidedFusionCategory.{v,u})
/-- The root dimension of the unit label is the root trace of the tensor unit. -/
theorem rootDimension_unit :
    rootDimension C (unitIndex C) =
      unitScalar C (rightQuantumTrace ((fourthDualRootNaturalIso C).app (𝟙_ C.Obj))) :=
  (unitIndex_iso C).elim fun e ↦
    congrArg (unitScalar C) ((rootTrace_id_iso C e).trans (rootTrace_id C _))

set_option backward.isDefEq.respectTransparency false in
/-- The actual natural fourth-dual root is its unit dimension times the
canonical double-dual unit map. -/
theorem fourthDualRoot_unit_component :
    ((fourthDualRootNaturalIso C).app (𝟙_ C.Obj)).hom =
      rootDimension C (unitIndex C) • (doubleDualUnitIso (C := C.Obj)).hom := by
  let U := 𝟙_ C.Obj
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let : Simple U := IsFusionCategory.unit_simple
  let : FiniteDimensional ℂ (U ⟶ U) := IsFusionCategory.hom_finite _ _
  let a := (fourthDualRootNaturalIso C).app U
  let u := doubleDualIso C U
  obtain ⟨r, _, hr, _⟩ := isomorphisms_scalar (k := ℂ) u a
  have hu : u = doubleDualUnitIso (C := C.Obj) := Iso.ext (drinfeld_unit (C := C.Obj))
  rw [rootDimension_unit]
  change a.hom = unitScalar C (rightQuantumTrace a) • (doubleDualUnitIso (C := C.Obj)).hom
  rw [rightQuantumTrace_smul_hom hr, hu, rightQuantumTrace_unitIso]
  simpa only [Ground.unitScalar_eq_equiv, map_smul, map_one, smul_eq_mul, mul_one, hu] using hr

set_option backward.isDefEq.respectTransparency false in
/-- The natural-root dimension of the unit is a sign. -/
theorem rootDimension_unit_sq :
    rootDimension C (unitIndex C) * rootDimension C (unitIndex C) = 1 := by
  let U := 𝟙_ C.Obj
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let : HasRightDual ((Uᘁ)ᘁ) := RightRigidCategory.rightDual ((Uᘁ)ᘁ)
  let : Simple U := IsFusionCategory.unit_simple
  apply scalar_sq_eq_one_of_same_square (doubleDualUnitIso (C := C.Obj))
    ((fourthDualRootNaturalIso C).app U) (rootDimension C (unitIndex C))
    (fourthDualRoot_unit_component C)
  refine (show ((fourthDualRootNaturalIso C).app U).hom ≫
      ((((fourthDualRootNaturalIso C).app U).homᘁ)ᘁ) = (fourthDualIso U).hom from
    congrArg (fun n ↦ (n.app U).hom) (fourthDualRootNaturalSquare_eq C)).trans ?_
  simpa only [Iso.trans_hom, rightDualIsoMap] using
    congrArg Iso.hom (fourthDualIso_unit (C := C.Obj))

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- On a simple and its right dual the root carries the ordinary duality cup
to the double-dual cup, with the ENO sign. -/
theorem root_components_coevaluation (i : Fin (rank C)) :
    let X := simples C i
    η_ X (Xᘁ) ≫ (((fourthDualRootNaturalIso C).app X).hom ⊗ₘ
      ((fourthDualRootNaturalIso C).app (Xᘁ)).hom) =
      rootDualSign C i • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) := by
  dsimp only
  rw [rootDualSign_component C i]
  simp only [rightDualIsoMap, Iso.symm_hom, tensorHom_def,
    MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]
  congr 1
  simpa only [tensorHom_def, Category.assoc, doubleDualFunctor, Functor.id_obj] using
    coevaluation_iso_map ((fourthDualRootNaturalIso C).app (simples C i))

end PropertyF.Ground.Dimensions

end
