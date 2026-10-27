module
public import PropertyF.Ground.Dimensions.PivotalPairing

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Right dual tensor comparison is compatible with the left unitor. -/
theorem rightDualTensorIso_unit_left {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    ((λ_ X).homᘁ) ≫ (rightDualTensorIso (𝟙_ C) X).hom =
      (ρ_ (Xᘁ)).inv ≫ ((Xᘁ) ◁ (rightDualUnitIso (C := C)).inv) := by
  let : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let r : Iᘁ ≅ I := by
    change rightDualObject (𝟙_ C) ≅ 𝟙_ C
    exact rightDualUnitIso
  let J := (Xᘁ) ⊗ (Iᘁ)
  let l : (Xᘁ) ⟶ J := ((λ_ X).homᘁ) ≫ (rightDualTensorIso I X).hom
  let s : (Xᘁ) ⟶ J := (ρ_ (Xᘁ)).inv ≫ (Xᘁ) ◁ r.inv
  have hl : l ▷ (I ⊗ X) ≫ ε_ (I ⊗ X) J = (Xᘁ) ◁ (λ_ X).hom ≫ ε_ X (Xᘁ) := by
    have he := rightDualIso_evaluation
      (@HasRightDual.exact C _ _ (I ⊗ X) (RightRigidCategory.rightDual _))
      (ExactPairing.tensor (X₁ := I) (X₂ := X) (Y₁ := Iᘁ) (Y₂ := Xᘁ))
    change (rightDualTensorIso I X).hom ▷ (I ⊗ X) ≫ ε_ (I ⊗ X) J =
      ε_ (I ⊗ X) ((I ⊗ X)ᘁ) at he
    dsimp only [l]
    rw [comp_whiskerRight_assoc, he, rightAdjointMate_comp_evaluation]
  have hs : s ▷ (I ⊗ X) ≫ ε_ (I ⊗ X) J = (Xᘁ) ◁ (λ_ X).hom ≫ ε_ X (Xᘁ) := by
    have he := rightDualIso_inv_evaluation
      (@HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
      (inferInstance : ExactPairing I I)
    change r.inv ▷ I ≫ ε_ I (Iᘁ) = ε_ I I at he
    change ((ρ_ (Xᘁ)).inv ≫ (Xᘁ) ◁ r.inv) ▷ (I ⊗ X) ≫
      (𝟙 _ ⊗≫ (Xᘁ) ◁ (ε_ I (Iᘁ) ▷ X) ⊗≫ ε_ X (Xᘁ)) = _
    calc
      _ = 𝟙 _ ⊗≫ (Xᘁ : C) ◁ ((r.inv ▷ I ≫ ε_ I (Iᘁ)) ▷ X) ⊗≫ ε_ X (Xᘁ) := by
        simp only [comp_whiskerRight, whiskerLeft_comp]
        monoidal
      _ = 𝟙 _ ⊗≫ (Xᘁ : C) ◁ (ε_ I I ▷ X) ⊗≫ ε_ X (Xᘁ) := by rw [he]
      _ = _ := by
        change 𝟙 _ ⊗≫ (Xᘁ : C) ◁ ((ρ_ I).hom ▷ X) ⊗≫ ε_ X (Xᘁ) = _
        monoidal
  have h : l ▷ (I ⊗ X) ≫ ε_ (I ⊗ X) J = s ▷ (I ⊗ X) ≫ ε_ (I ⊗ X) J := hl.trans hs.symm
  let : HasRightDual (I ⊗ X) := { rightDual := J, exact := ExactPairing.tensor }
  have hh := congrArg (tensorRightHomEquiv (Xᘁ) (I ⊗ X) J I) h
  have hL := @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ (I ⊗ X) (Xᘁ) this l
  have hR := @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ (I ⊗ X) (Xᘁ) this s
  change (tensorRightHomEquiv (Xᘁ) (I ⊗ X) J I)
    (l ▷ (I ⊗ X) ≫ ε_ (I ⊗ X) J) = l ≫ (λ_ J).inv at hL
  change (tensorRightHomEquiv (Xᘁ) (I ⊗ X) J I)
    (s ▷ (I ⊗ X) ≫ ε_ (I ⊗ X) J) = s ≫ (λ_ J).inv at hR
  rw [hL, hR] at hh
  exact (cancel_mono (λ_ J).inv).1 hh
end PropertyF.Ground.Dimensions
