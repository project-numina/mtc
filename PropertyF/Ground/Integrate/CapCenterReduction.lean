module
public import PropertyF.Ground.Integrate.PivotalBalancedReduction
public import PropertyF.Ground.CentreIntegrate.TwistBalancing

/-! Reduce centre balancing to the concrete tensor-pairing cap diagram. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- Base pivotal existence and the concrete centre cap identity suffice for
the target. Both are explicit, unproved hypotheses. -/
theorem target_of_pivotal_base_and_center_cap
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}) (hpu : PseudoUnitary C),
      HasPropertyF C.Obj →
      ∃ (p : Dimensions.PivotalStructure (C := C.Obj)),
        letI := CentreRigid.rigidCenter (C := C.Obj)
        letI := centerFusionOfPivotalPseudoUnitary C p hpu
        let D := Integrate.bundledCenter C
        ∀ X Y : D.Obj,
          let W := X ⊗ Y
          let V := (Yᘁ) ⊗ (Xᘁ)
          let q : ExactPairing W V := ExactPairing.tensor
          let r : ExactPairing V (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := ExactPairing.tensor
          (Modular.doubleBraiding X Y ▷ V) ≫ (β_ W V).hom ≫
            @ExactPairing.evaluation D.Obj _ _ W V q =
          ((doubleDualIso D X).hom ⊗ₘ (doubleDualIso D Y).hom) ▷ V ≫
            @ExactPairing.evaluation D.Obj _ _ V _ r) : TargetStatement.{v,u} := by
  apply target_of_pivotal_base_and_center_balancing
  intro C hpu hF
  obtain ⟨p, hcap⟩ := hCenter C hpu hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  refine ⟨p, ?_⟩
  dsimp only
  intro X Y
  apply CentreIntegrate.pivotal_balance_of_drinfeld_tensor
  exact CentreIntegrate.drinfeld_tensor_of_pairing_cap (Integrate.bundledCenter C) X Y (hcap X Y)

end PropertyF.Ground
