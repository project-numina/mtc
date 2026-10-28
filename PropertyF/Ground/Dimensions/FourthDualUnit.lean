module
public import PropertyF.Ground.Dimensions.DrinfeldUnit

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The Drinfeld map respects duality on the tensor unit. -/
theorem drinfeld_unit_dual (C : Ground.BraidedFusionCategory.{v,u}) :
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
  have hn := doubleDualIso_natural C r.hom
  have hb : (Ground.doubleDualIso C (Uᘁ)).hom ≫ ((r.homᘁ)ᘁ) = (r.homᘁ) := by
    rw [← hn, hu]
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
theorem fourthDualIso_unit (C : Ground.BraidedFusionCategory.{v,u}) :
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
theorem rootDimension_unit_sq (C : Ground.BraidedFusionCategory.{v,u}) :
    rootDimension C (Ground.unitIndex C) * rootDimension C (Ground.unitIndex C) = 1 := by
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
    have h := congrArg (fun n => (n.app U).hom) (fourthDualRootNaturalSquare_eq C)
    exact h
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
  have hdim : rootDimension C (Ground.unitIndex C) = r := by
    obtain ⟨e⟩ := Ground.unitIndex_iso C
    have hn := (fourthDualRootNaturalIso C).hom.naturality e.hom
    have ht := rightQuantumTrace_iso
      ((fourthDualRootNaturalIso C).app (Ground.simples C (Ground.unitIndex C))) a e
      (by simpa [doubleDualFunctor, a] using hn)
    change Ground.unitScalar C (rootTrace C (𝟙 (Ground.simples C (Ground.unitIndex C)))) = r
    have hq : rootTrace C (𝟙 (Ground.simples C (Ground.unitIndex C))) =
        rightQuantumTrace ((fourthDualRootNaturalIso C).app (Ground.simples C (Ground.unitIndex C))) := by
      apply End.homEquiv.injective
      simp [rootTrace, rightTraceWith, rightQuantumTrace, tensorHom_def]
    rw [hq, ht, htrace]
  simpa [hdim] using hr2

end PropertyF.Ground.Dimensions
