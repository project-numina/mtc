module
public import PropertyF.Ground.Integrate.FourthDualCenterReduction
public import PropertyF.Ground.Dimensions.MonodromyTensorCap

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
  apply target_of_pivotal_base_and_center_cap
  intro C hpu hF
  obtain ⟨p⟩ := hPivotal C hpu hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  refine ⟨p, ?_⟩
  dsimp only
  intro X Y
  exact Dimensions.drinfeld_tensor_pairing_cap (Integrate.bundledCenter C) X Y

end PropertyF.Ground
