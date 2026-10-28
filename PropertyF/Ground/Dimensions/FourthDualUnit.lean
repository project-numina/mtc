module
public import PropertyF.Ground.Dimensions.CoevaluationSliding

/-! # Fourth duals of the tensor unit

The Drinfeld and fourth-dual maps satisfy the unit identities used for root dimensions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The braided double-dual map has the canonical component on the unit. -/
theorem drinfeld_unit :
    (Ground.doubleDualIso C (𝟙_ C.Obj)).hom = (doubleDualUnitIso (C := C.Obj)).hom := by
  let U : C.Obj := 𝟙_ C.Obj
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let r : Uᘁ ≅ U := by
    change rightDualObject (𝟙_ C.Obj) ≅ 𝟙_ C.Obj
    exact rightDualUnitIso
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
    Ground.doubleDualIso C (rightDualObject (𝟙_ C.Obj)) =
      (rightDualIsoMap (Ground.doubleDualIso C (𝟙_ C.Obj))).symm := by
  let U : C.Obj := 𝟙_ C.Obj
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let : HasRightDual ((Uᘁ)ᘁ) := RightRigidCategory.rightDual ((Uᘁ)ᘁ)
  let r : Uᘁ ≅ U := by
    change rightDualObject (𝟙_ C.Obj) ≅ 𝟙_ C.Obj
    exact rightDualUnitIso
  have hu : (Ground.doubleDualIso C U).hom = (r.inv ≫ (r.homᘁ)) := by
    exact drinfeld_unit C
  have hb : (Ground.doubleDualIso C (Uᘁ)).hom ≫ ((r.homᘁ)ᘁ) = (r.homᘁ) := by
    rw [← (doubleDualIso_natural C r.hom), hu]
    simp only [Iso.hom_inv_id_assoc]
  apply Iso.ext
  simp only [rightDualIsoMap, Iso.symm_hom]
  let ee := rightDualIsoMap (rightDualIsoMap r)
  change (Ground.doubleDualIso C (Uᘁ)).hom = ((Ground.doubleDualIso C U).invᘁ)
  apply (cancel_mono ee.hom).1
  change (Ground.doubleDualIso C (Uᘁ)).hom ≫ ((r.homᘁ)ᘁ) =
    ((Ground.doubleDualIso C U).invᘁ) ≫ ((r.homᘁ)ᘁ)
  rw [hb]
  have hui : (Ground.doubleDualIso C U).inv = (r.invᘁ) ≫ r.hom := by
    have hIso : Ground.doubleDualIso C U = r.symm ≪≫ rightDualIsoMap r := Iso.ext hu
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
  have hu : Ground.doubleDualIso C (𝟙_ C.Obj) = doubleDualUnitIso (C := C.Obj) :=
    Iso.ext (drinfeld_unit C)
  unfold fourthDualIso
  have hdual := drinfeld_unit_dual C
  change Ground.doubleDualIso C ((𝟙_ C.Obj)ᘁ) =
    (rightDualIsoMap (Ground.doubleDualIso C (𝟙_ C.Obj))).symm at hdual
  rw [hdual]
  rw [hu]
  apply Iso.ext
  rfl
set_option backward.isDefEq.respectTransparency false in
/-- The natural-root dimension of the unit is a sign. -/
theorem rootDimension_unit_sq :
    rootDimension C (unitIndex C) * rootDimension C (unitIndex C) = 1 := by
  let U := 𝟙_ C.Obj
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let : HasRightDual ((Uᘁ)ᘁ) := RightRigidCategory.rightDual ((Uᘁ)ᘁ)
  let : Simple U := Ground.IsFusionCategory.unit_simple
  let : FiniteDimensional ℂ (U ⟶ U) := Ground.IsFusionCategory.hom_finite _ _
  let a := (fourthDualRootNaturalIso C).app U
  let u := Ground.doubleDualIso C U
  obtain ⟨r, _, hr, _⟩ := doubleDualIso_scalar u a
  have hsq : a.hom ≫ ((a.homᘁ)ᘁ) = (fourthDualIso C U).hom := by
    exact (congrArg (fun n => (n.app U).hom) (fourthDualRootNaturalSquare_eq C))
  have hfourth : (fourthDualIso C U).hom = u.hom ≫ ((u.homᘁ)ᘁ) := by
    have h := congrArg Iso.hom (fourthDualIso_unit C)
    have hu : u = doubleDualUnitIso (C := C.Obj) := Iso.ext (drinfeld_unit C)
    rw [hu]
    simpa only [Iso.trans_hom, rightDualIsoMap] using h
  have hs : (r * r) • (fourthDualIso C U).hom = (1 : ℂ) • (fourthDualIso C U).hom := by
    calc
      _ = (r * r) • (u.hom ≫ ((u.homᘁ)ᘁ)) := by rw [hfourth]
      _ = a.hom ≫ ((a.homᘁ)ᘁ) := by
        rw [hr]
        simp only [rightAdjointMate_smul, Linear.smul_comp, Linear.comp_smul, smul_smul]
      _ = _ := by simpa using hsq
  have hn : (fourthDualIso C U).hom ≠ 0 := by
    intro h
    have hh := congrArg (fun f => f ≫ (fourthDualIso C U).inv) h
    simp at hh
    exact id_nonzero U hh
  have hr2 : r * r = 1 := smul_left_injective ℂ hn hs
  have htrace : Ground.unitScalar C (rightQuantumTrace a) = r := by
    have ht : rightQuantumTrace a = r • rightQuantumTrace u := by
      apply End.homEquiv.injective
      simp [rightQuantumTrace, hr, tensorHom_def]
    rw [ht]
    have hunit : rightQuantumTrace u = 1 := by
      have hu : u = doubleDualUnitIso (C := C.Obj) := Iso.ext (drinfeld_unit C)
      rw [hu, rightQuantumTrace_unitIso]
    rw [hunit]
    simp only [← groundUnitScalarEquiv_apply, map_smul, map_one, smul_eq_mul, mul_one]
  have hdim : rootDimension C (unitIndex C) = r := by
    obtain ⟨e⟩ := Ground.unitIndex_iso C
    have hn := (fourthDualRootNaturalIso C).hom.naturality e.hom
    have ht := rightQuantumTrace_iso
      ((fourthDualRootNaturalIso C).app (simples C (unitIndex C))) a e
      (by simpa [doubleDualFunctor, a] using hn)
    change Ground.unitScalar C (rootTrace C (𝟙 (simples C (unitIndex C)))) = r
    have hq : rootTrace C (𝟙 (simples C (unitIndex C))) =
        rightQuantumTrace ((fourthDualRootNaturalIso C).app (simples C (unitIndex C))) := by
      apply End.homEquiv.injective
      simp [rootTrace, rightTraceWith, rightQuantumTrace, tensorHom_def]
    rw [hq, ht, htrace]
  simpa [hdim] using hr2

end PropertyF.Ground.Dimensions

end
