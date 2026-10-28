module
public import PropertyF.Ground.CentreCabling.ImageCore
public import PropertyF.Ground.Integrate.ActualCenterReduction
public import PropertyF.Ground.CentreInduction.ActualFusion
public import PropertyF.Ground.CentreModular.InductionDimension
public import PropertyF.Ground.CentreInduction.PivotalTransfer
public import PropertyF.Ground.Centre.Rigid
public import PropertyF.Ground.CentreInduction.ForgetDual
public import PropertyF.Ground.CentreInduction.PivotalCentrality
public import PropertyF.Ground.CentreCalculus.ActualCoreIntegrality
public import PropertyF.Ground.Centre.Modular.Vafa
public import PropertyF.Ground.CentreModular.TransparencyCriterion
public import PropertyF.Ground.CentreInduction.PivotalCentrality
public import PropertyF.Ground.CentreIntegrate.TwistBalancing
public import PropertyF.Ground.Dimensions.MonodromyTensorCap

section
/-! The constructed induction adjunction removes the centre square premise. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- The centre square follows from its actual induction adjunction as soon as
its genuine fusion structure and FP-valued spherical structure are available. -/
theorem center_globalDimension_square_of_actual_induction
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hp : p.IsSpherical)
    (hdim : Modular.HasFPSimpleDimensions (Integrate.bundledCenter C) p) :
    globalDimension (Integrate.bundledCenter C) = (globalFPDimension C : ℂ) ^ 2 :=
  CentreModular.center_globalDimension_of_adjunction C
    (CentreInduction.induction C) (CentreInduction.actualAdjunction C)
    (fun _ ↦ ⟨Iso.refl _⟩) p hp hdim



end PropertyF.Ground
end
end

section
/-! Centre fusion and sphericality from any base pivotal structure. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- The fusion instance constructed from a pivotal pseudo-unitary base. -/
theorem centerFusionOfPivotalPseudoUnitary
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hpu : PseudoUnitary C) :
    letI := CentreRigid.rigidCenter (C := C.Obj)
    IsFusionCategory (CategoryTheory.Center C.Obj) := by
  letI := CentreRigid.rigidCenter (C := C.Obj)
  exact Classical.choose (CentreInduction.center_structure_of_pivotal_pseudoUnitary C p hpu)

/-- The actual centre spherical pivotal structure constructed along the same route. -/
def centerPivotalOfPivotalPseudoUnitary
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hpu : PseudoUnitary C) :
    letI := CentreRigid.rigidCenter (C := C.Obj)
    Dimensions.PivotalStructure (C := CategoryTheory.Center C.Obj) := by
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  exact Classical.choose (Classical.choose_spec
    (CentreInduction.center_structure_of_pivotal_pseudoUnitary C p hpu))

/-- The constructed centre pivotal dimensions are its FP dimensions. -/
theorem centerPivotal_hasFPDimensions (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (hpu : PseudoUnitary C) :
    letI := CentreRigid.rigidCenter (C := C.Obj)
    letI := centerFusionOfPivotalPseudoUnitary C p hpu
    Modular.HasFPSimpleDimensions (Integrate.bundledCenter C)
      (centerPivotalOfPivotalPseudoUnitary C p hpu) := by
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  have hd := (Classical.choose_spec (Classical.choose_spec
    (CentreInduction.center_structure_of_pivotal_pseudoUnitary C p hpu))).2.1
  change CentreInduction.PivotalHasFPDimensions (Integrate.bundledCenter C)
    (centerPivotalOfPivotalPseudoUnitary C p hpu) at hd
  intro i
  simpa [Modular.simpleDimension, Dimensions.pivotalDimension, Dimensions.rightTrace_id,
    unitScalar_eq_equiv] using hd i

end PropertyF.Ground
end
end

/-! # Pivotal and balancing reductions

The pivotal, balancing and transparency arguments supply the final reduction. -/

section

/-! Trivial centre transparency is constructed from actual induction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- The actual rigid fusion centre has no non-unit transparent simple. -/
theorem center_transparent_label_eq_unit
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (k : Fin (rank (Integrate.bundledCenter C)))
    (hk : Transparent (simples (Integrate.bundledCenter C) k)) :
    k = unitIndex (Integrate.bundledCenter C) := by
  let D := Integrate.bundledCenter C
  let Y := simples D k
  letI : Simple Y := simples_simple D k
  obtain ⟨e⟩ := CentreInduction.center_transparent_simple_iso_unit C Y (by
    intro W
    exact hk W)
  obtain ⟨u⟩ := unitIndex_iso D
  exact simples_injective D ⟨e ≪≫ u.symm⟩



end PropertyF.Ground
end
end

section
/-! The proved cap diagram supplies Drinfeld tensor coherence and balancing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- The actual Drinfeld map has the tensor coherence law in any braided
fusion category. -/
theorem drinfeld_tensor (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    Modular.doubleBraiding X Y ≫ (doubleDualIso C (X ⊗ Y)).hom =
      ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ≫
        (Dimensions.doubleDualTensorIso X Y).hom :=
  CentreIntegrate.drinfeld_tensor_of_pairing_cap (doubleDualIso C)
    (Dimensions.drinfeld_eval C (X ⊗ Y)) (Dimensions.drinfeld_tensor_pairing_cap C X Y)

/-- The twist of any pivotal braided fusion category is balanced. -/
theorem pivotal_twist_balanced (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (X Y : C.Obj) :
    Modular.doubleBraiding X Y ≫
      ((Dimensions.pivotalBraidedTwist C p X).hom ⊗ₘ
        (Dimensions.pivotalBraidedTwist C p Y).hom) =
      (Dimensions.pivotalBraidedTwist C p (X ⊗ Y)).hom :=
  CentreIntegrate.pivotal_balance_of_drinfeld_tensor p (doubleDualIso C) (drinfeld_tensor C X Y)



end PropertyF.Ground
end
end
