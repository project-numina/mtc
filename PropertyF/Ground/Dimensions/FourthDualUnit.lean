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

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The braided double-dual map has the canonical component on the unit. -/
theorem drinfeld_unit :
    (doubleDualIso C (𝟙_ C.Obj)).hom = (doubleDualUnitIso (C := C.Obj)).hom := by
  let U : C.Obj := 𝟙_ C.Obj
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let r : Uᘁ ≅ U := rightDualUnitIso
  have h : (r.inv ≫ (r.homᘁ)) ▷ (Uᘁ) ≫ ε_ (Uᘁ) ((Uᘁ)ᘁ) =
      (β_ U (Uᘁ)).hom ≫ ε_ U (Uᘁ) := by
    rw [comp_whiskerRight_assoc, rightAdjointMate_comp_evaluation]
    have hb : (β_ U U).hom = 𝟙 (U ⊗ U) := by
      change (β_ (𝟙_ C.Obj) (𝟙_ C.Obj)).hom = 𝟙 _
      rw [braiding_tensorUnit_left, unitors_equal, Iso.hom_inv_id]
    have hn := braiding_naturality_right U r.hom
    rw [hb, Category.comp_id] at hn
    have hc : U ◁ r.hom ≫ r.inv ▷ U = (β_ U (Uᘁ)).hom := by
      rw [hn, Category.assoc, ← comp_whiskerRight, Iso.hom_inv_id, id_whiskerRight, Category.comp_id]
    rw [← whisker_exchange_assoc, ← Category.assoc, hc]
  change (doubleDualUnitIso (C := C.Obj)).hom ▷ (Uᘁ) ≫ ε_ (Uᘁ) ((Uᘁ)ᘁ) = _ at h
  exact evaluation_ext ((drinfeld_eval C U).trans h.symm)
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The Drinfeld map respects duality on the tensor unit. -/
theorem drinfeld_unit_dual :
    doubleDualIso C (rightDualObject (𝟙_ C.Obj)) =
      (rightDualIsoMap (doubleDualIso C (𝟙_ C.Obj))).symm := by
  let U : C.Obj := 𝟙_ C.Obj
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let : HasRightDual ((Uᘁ)ᘁ) := RightRigidCategory.rightDual ((Uᘁ)ᘁ)
  let r : Uᘁ ≅ U := rightDualUnitIso
  have hu : (doubleDualIso C U).hom = (r.inv ≫ (r.homᘁ)) :=
    drinfeld_unit C
  have hb : (doubleDualIso C (Uᘁ)).hom ≫ ((r.homᘁ)ᘁ) = (r.homᘁ) := by
    rw [← (doubleDualIso_natural C r.hom), hu]
    simp only [Iso.hom_inv_id_assoc]
  apply Iso.ext
  simp only [rightDualIsoMap, Iso.symm_hom]
  let ee := rightDualIsoMap (rightDualIsoMap r)
  change (doubleDualIso C (Uᘁ)).hom = ((doubleDualIso C U).invᘁ)
  apply (cancel_mono ee.hom).1
  change (doubleDualIso C (Uᘁ)).hom ≫ ((r.homᘁ)ᘁ) =
    ((doubleDualIso C U).invᘁ) ≫ ((r.homᘁ)ᘁ)
  rw [hb]
  have hui : (doubleDualIso C U).inv = (r.invᘁ) ≫ r.hom := by
    have hIso : doubleDualIso C U = r.symm ≪≫ rightDualIsoMap r := Iso.ext hu
    simpa only [Iso.trans_inv, Iso.symm_inv, rightDualIsoMap] using congrArg Iso.inv hIso
  have hcancel := (rightDualIsoMap r).hom_inv_id
  change (r.homᘁ) ≫ (r.invᘁ) = 𝟙 (Uᘁ) at hcancel
  rw [hui, comp_rightAdjointMate, Category.assoc, ← comp_rightAdjointMate,
    hcancel, rightAdjointMate_id, Category.comp_id]
/-- The fourth-dual map has the canonical iterated unit component. -/
theorem fourthDualIso_unit :
    letI : HasRightDual (𝟙_ C.Obj) := RightRigidCategory.rightDual (𝟙_ C.Obj)
    letI : HasRightDual ((𝟙_ C.Obj)ᘁ) := RightRigidCategory.rightDual ((𝟙_ C.Obj)ᘁ)
    letI : HasRightDual (((𝟙_ C.Obj)ᘁ)ᘁ) := RightRigidCategory.rightDual (((𝟙_ C.Obj)ᘁ)ᘁ)
    fourthDualIso C (𝟙_ C.Obj) =
      doubleDualUnitIso (C := C.Obj) ≪≫
        rightDualIsoMap (rightDualIsoMap (doubleDualUnitIso (C := C.Obj))) := by
  let : HasRightDual (𝟙_ C.Obj) := RightRigidCategory.rightDual (𝟙_ C.Obj)
  let : HasRightDual ((𝟙_ C.Obj)ᘁ) := RightRigidCategory.rightDual ((𝟙_ C.Obj)ᘁ)
  let : HasRightDual (((𝟙_ C.Obj)ᘁ)ᘁ) := RightRigidCategory.rightDual (((𝟙_ C.Obj)ᘁ)ᘁ)
  have hu : doubleDualIso C (𝟙_ C.Obj) = doubleDualUnitIso (C := C.Obj) :=
    Iso.ext (drinfeld_unit C)
  unfold fourthDualIso
  have hdual := drinfeld_unit_dual C
  change doubleDualIso C ((𝟙_ C.Obj)ᘁ) =
    (rightDualIsoMap (doubleDualIso C (𝟙_ C.Obj))).symm at hdual
  rw [hdual, hu]
  apply Iso.ext
  rfl
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
  have hu : u = doubleDualUnitIso (C := C.Obj) := Iso.ext (drinfeld_unit C)
  have htrace : unitScalar C (rightQuantumTrace a) = r := by
    rw [rightQuantumTrace_smul_hom hr, hu, rightQuantumTrace_unitIso]
    simp only [Ground.unitScalar_eq_equiv, map_smul, map_one, smul_eq_mul, mul_one]
  simpa [a, (rootDimension_unit C).trans htrace, hu] using hr

set_option backward.isDefEq.respectTransparency false in
/-- The natural-root dimension of the unit is a sign. -/
theorem rootDimension_unit_sq :
    rootDimension C (unitIndex C) * rootDimension C (unitIndex C) = 1 := by
  let U := 𝟙_ C.Obj
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let : HasRightDual ((Uᘁ)ᘁ) := RightRigidCategory.rightDual ((Uᘁ)ᘁ)
  let : Simple U := IsFusionCategory.unit_simple
  let a := (fourthDualRootNaturalIso C).app U
  let u := doubleDualIso C U
  let r := rootDimension C (unitIndex C)
  have hu : u = doubleDualUnitIso (C := C.Obj) := Iso.ext (drinfeld_unit C)
  have hr : a.hom = r • u.hom := by
    simpa [a, r, hu] using fourthDualRoot_unit_component C
  have hsq : a.hom ≫ ((a.homᘁ)ᘁ) = (fourthDualIso C U).hom :=
    congrArg (fun n => (n.app U).hom) (fourthDualRootNaturalSquare_eq C)
  have hfourth : (fourthDualIso C U).hom = u.hom ≫ ((u.homᘁ)ᘁ) := by
    have h := congrArg Iso.hom (fourthDualIso_unit C)
    rw [hu]
    simpa only [Iso.trans_hom, rightDualIsoMap] using h
  exact scalar_sq_eq_one_of_same_square u a r hr (hsq.trans hfourth)

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
theorem root_components_coevaluation
    (i : Fin (rank C)) :
    let X := simples C i
    η_ X (Xᘁ) ≫ (((fourthDualRootNaturalIso C).app X).hom ⊗ₘ
      ((fourthDualRootNaturalIso C).app (Xᘁ)).hom) =
      rootDualSign C i • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) := by
  let X := simples C i
  let a : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  let e := rootDualSign C i
  have ha : ((fourthDualRootNaturalIso C).app (Xᘁ)).hom = e • ((a.invᘁ)) :=
    rootDualSign_component C i
  change η_ X (Xᘁ) ≫ (a.hom ⊗ₘ ((fourthDualRootNaturalIso C).app (Xᘁ)).hom) =
    e • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)
  rw [ha]
  simp only [tensorHom_def, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]
  congr 1
  simpa only [tensorHom_def, Category.assoc, doubleDualFunctor, Functor.id_obj] using
    coevaluation_iso_map a

end PropertyF.Ground.Dimensions

end
