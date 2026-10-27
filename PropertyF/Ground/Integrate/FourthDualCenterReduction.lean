module
public import PropertyF.Ground.Integrate.CapCenterReduction
public import PropertyF.Ground.Dimensions.DefectSliding

/-! Pseudo-unitary pivotal existence reduces to the fourth-dual tensor law. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- The base's fourth-dual tensor law and the centre cap identity suffice for
the target. Both coherence identities remain explicit premises. -/
theorem target_of_fourthDual_tensor_and_center_cap
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}) (hpu : PseudoUnitary C),
      HasPropertyF C.Obj →
      ∃ (hfourth : ∀ X Y : C.Obj, (Dimensions.fourthDualIso C (X ⊗ Y)).hom =
        ((Dimensions.fourthDualIso C X).hom ⊗ₘ (Dimensions.fourthDualIso C Y).hom) ≫
          (Dimensions.doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
            (((Dimensions.doubleDualTensorIso X Y).homᘁ)ᘁ)),
        let p := Classical.choose (Dimensions.eno_pseudoUnitary_yields_positive_spherical_of_fourthDual_tensor C hfourth hpu)
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
  apply target_of_pivotal_base_and_center_cap
  intro C hpu hF
  obtain ⟨hfourth, hcap⟩ := hCenter C hpu hF
  let p := Classical.choose (Dimensions.eno_pseudoUnitary_yields_positive_spherical_of_fourthDual_tensor C hfourth hpu)
  exact ⟨p, hcap⟩

end PropertyF.Ground
