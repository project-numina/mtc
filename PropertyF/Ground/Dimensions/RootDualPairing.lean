module
public import PropertyF.Ground.Dimensions.FourthDualUnit

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The actual natural fourth-dual root is its unit dimension times the
canonical double-dual unit map. -/
theorem fourthDualRoot_unit_component :
    ((fourthDualRootNaturalIso C).app (𝟙_ C.Obj)).hom =
      rootDimension C (Ground.unitIndex C) • (doubleDualUnitIso (C := C.Obj)).hom := by
  let U := 𝟙_ C.Obj
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let : Simple U := Ground.IsFusionCategory.unit_simple
  let : FiniteDimensional ℂ (U ⟶ U) := Ground.IsFusionCategory.hom_finite _ _
  let a := (fourthDualRootNaturalIso C).app U
  let u := Ground.doubleDualIso C U
  obtain ⟨r, _, hr, _⟩ := doubleDualIso_scalar u a
  have htrace : Ground.unitScalar C (rightQuantumTrace a) = r := by
    have ht : rightQuantumTrace a = r • rightQuantumTrace u := by
      apply End.homEquiv.injective
      simp [rightQuantumTrace, hr, tensorHom_def]
    rw [ht]
    have hu : u = doubleDualUnitIso (C := C.Obj) := Iso.ext (drinfeld_unit C)
    rw [hu, rightQuantumTrace_unitIso]
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
  have hu : u = doubleDualUnitIso (C := C.Obj) := Iso.ext (drinfeld_unit C)
  simpa [a, hdim, hu] using hr
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- On a simple and its right dual the root carries the ordinary duality cup
to the double-dual cup, with the ENO sign. -/
theorem root_components_coevaluation
    (i : Fin (Ground.rank C)) :
    let X := Ground.simples C i
    η_ X (Xᘁ) ≫ (((fourthDualRootNaturalIso C).app X).hom ⊗ₘ
      ((fourthDualRootNaturalIso C).app (Xᘁ)).hom) =
      rootDualSign C i • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) := by
  let X := Ground.simples C i
  let a : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  let e := rootDualSign C i
  have ha : ((fourthDualRootNaturalIso C).app (Xᘁ)).hom = e • ((a.invᘁ)) := by
    exact rootDualSign_component C i
  change η_ X (Xᘁ) ≫ (a.hom ⊗ₘ ((fourthDualRootNaturalIso C).app (Xᘁ)).hom) =
    e • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)
  rw [ha]
  simp only [tensorHom_def, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]
  congr 1
  have h := coevaluation_comp_rightAdjointMate a.inv
  calc
    _ = η_ X (Xᘁ) ≫ X ◁ (a.invᘁ) ≫ a.hom ▷ (((Xᘁ)ᘁ)ᘁ) := by
      simpa only [doubleDualFunctor, Functor.id_obj, Category.assoc] using
        congrArg (fun z => η_ X (Xᘁ) ≫ z) (whisker_exchange a.hom (a.invᘁ)).symm
    _ = η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) ≫ a.inv ▷ (((Xᘁ)ᘁ)ᘁ) ≫
        a.hom ▷ (((Xᘁ)ᘁ)ᘁ) := by
      simpa only [doubleDualFunctor, Functor.id_obj, Category.assoc] using
        congrArg (fun z => z ≫ a.hom ▷ (((Xᘁ)ᘁ)ᘁ)) h
    _ = _ := by
      have hi : (a.inv ▷ (((Xᘁ)ᘁ)ᘁ)) ≫ a.hom ▷ (((Xᘁ)ᘁ)ᘁ) = 𝟙 _ := by
        rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]
      simp only [hi, Category.comp_id]
end PropertyF.Ground.Dimensions

end
