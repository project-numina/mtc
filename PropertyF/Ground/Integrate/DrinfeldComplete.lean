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
public import PropertyF.Ground.CentreInduction.Transparent
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
    (fun _ ↦ ⟨Iso.refl _⟩) p hp fun i ↦ by
      simpa [Modular.simpleDimension, Dimensions.pivotalDimension, Dimensions.rightTrace_id,
        Dimensions.groundUnitScalarEquiv_apply, unitScalar_eq_equiv] using hdim i



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
  have hs := Classical.choose_spec (Classical.choose_spec
    (CentreInduction.center_structure_of_pivotal_pseudoUnitary C p hpu))
  obtain ⟨_, hd, _, _⟩ := hs
  change ∀ i, Dimensions.pivotalDimension (Integrate.bundledCenter C)
    (centerPivotalOfPivotalPseudoUnitary C p hpu)
    (simples (Integrate.bundledCenter C) i) = (fpSimple (Integrate.bundledCenter C) i : ℂ) at hd
  intro i
  simpa [Modular.simpleDimension, Dimensions.pivotalDimension, Dimensions.rightTrace_id,
    Dimensions.groundUnitScalarEquiv_apply, unitScalar_eq_equiv] using hd i

end PropertyF.Ground
end
end

/-! # Pivotal and balancing reductions

The pivotal, balancing and transparency arguments supply the final reduction. -/

section
/-! The actual core and mixed-monodromy obligations from pivotal balancing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- For a pseudo-unitary base with a pivotal structure, the actual centre is
rigid, fusion and positive spherical. If its pivotal twist is balanced, its
symmetric core is integral and the required mixed monodromy has finite order.
The base pivotal structure, balancing and S invertibility are still explicit
premises. -/
theorem target_of_pivotal_base_modular_balanced_center
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}) (hpu : PseudoUnitary C),
      HasPropertyF C.Obj →
      ∃ (p : Dimensions.PivotalStructure (C := C.Obj)),
        letI := CentreRigid.rigidCenter (C := C.Obj)
        letI := centerFusionOfPivotalPseudoUnitary C p hpu
        let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
        let D := Integrate.bundledCenter C
        (Modular.categoricalS D pZ).det ≠ 0 ∧
        (CentreModular.IsPivotalTwistBalanced D pZ)) : TargetStatement.{v,u} := by
  apply target_of_actual_center
  intro C hpu hF
  obtain ⟨p, hdet, hbalance⟩ := hCenter C hpu hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
  have hs := Classical.choose_spec (Classical.choose_spec
    (CentreInduction.center_structure_of_pivotal_pseudoUnitary C p hpu))
  obtain ⟨hspherical, _, _, _⟩ := hs
  have hdim := centerPivotal_hasFPDimensions C p hpu
  have hfinite : CentreCabling.HasFiniteImageCentralizerMonodromy C pZ := by
    intro y _ a _
    exact CentreModular.mixed_monodromy_finite_of_pivotal_balancing
      (Integrate.bundledCenter C) pZ hbalance _ _
  refine ⟨CentreRigid.rigidCenter, inferInstance, pZ, CentreCabling.symmetricCore C,
    (↑(CentreCabling.productLabels C) : Set _), hspherical, hdim, hdet,
    center_globalDimension_square_of_actual_induction C pZ hspherical hdim,
    CentreCalculus.actual_symmetricCore_integrality C pZ hspherical hdim, ?_, ?_⟩
  · intro y hy
    exact (CentreCabling.mem_productLabels C y).mpr
      (CentreCabling.productLabels_doubleCentralizer_of_image_monodromy C pZ hspherical hdet hdim hfinite y hy)
  · intro y hy
    exact (CentreCabling.mem_productLabels C y).mp hy

end PropertyF.Ground
end
end

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

/-- The frozen target follows from base pivotal existence and balancing of
its constructed centre twist. These two obligations remain explicit. -/
theorem target_of_pivotal_base_and_center_balancing
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}) (hpu : PseudoUnitary C),
      HasPropertyF C.Obj →
      ∃ (p : Dimensions.PivotalStructure (C := C.Obj)),
        letI := CentreRigid.rigidCenter (C := C.Obj)
        letI := centerFusionOfPivotalPseudoUnitary C p hpu
        let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
        let D := Integrate.bundledCenter C
        CentreModular.IsPivotalTwistBalanced D pZ) : TargetStatement.{v,u} := by
  apply target_of_pivotal_base_modular_balanced_center
  intro C hpu hF
  obtain ⟨p, hbalance⟩ := hCenter C hpu hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
  have hdim := centerPivotal_hasFPDimensions C p hpu
  exact ⟨p, CentreModular.categoricalS_det_ne_zero_of_trivial_transparency
    (Integrate.bundledCenter C) pZ hdim hbalance (center_transparent_label_eq_unit C), hbalance⟩

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
  CentreIntegrate.drinfeld_tensor_of_pairing_cap C X Y
    (Dimensions.drinfeld_tensor_pairing_cap C X Y)

/-- The twist of any pivotal braided fusion category is balanced. -/
theorem pivotal_twist_balanced (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (X Y : C.Obj) :
    Modular.doubleBraiding X Y ≫
      ((Dimensions.pivotalBraidedTwist C p X).hom ⊗ₘ
        (Dimensions.pivotalBraidedTwist C p Y).hom) =
      (Dimensions.pivotalBraidedTwist C p (X ⊗ Y)).hom :=
  CentreIntegrate.pivotal_balance_of_drinfeld_tensor C p X Y (drinfeld_tensor C X Y)

/-- The frozen target follows once the pseudo-unitary property-F base is
shown to admit a pivotal structure. That existence is the sole premise. -/
theorem target_of_pseudoUnitary_pivotal_existence
    (hPivotal : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj → Nonempty (Dimensions.PivotalStructure (C := C.Obj))) :
    TargetStatement.{v,u} := by
  apply target_of_pivotal_base_and_center_balancing
  intro C hpu hF
  obtain ⟨p⟩ := hPivotal C hpu hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  refine ⟨p, ?_⟩
  dsimp only
  intro X Y
  exact pivotal_twist_balanced (Integrate.bundledCenter C)
    (centerPivotalOfPivotalPseudoUnitary C p hpu) X Y

end PropertyF.Ground
end
end
