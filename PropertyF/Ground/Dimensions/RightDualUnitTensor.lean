module
public import PropertyF.Ground.Dimensions.RootDualPairing
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import PropertyF.Ground.Dimensions.PivotalTwist
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.PositiveCanonical
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
/-- Right dual tensor comparison is compatible with the right unitor. -/
theorem rightDualTensorIso_unit_right {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (X : C) :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    ((ρ_ X).homᘁ) ≫ (rightDualTensorIso X (𝟙_ C)).hom =
      (λ_ (Xᘁ)).inv ≫ ((rightDualUnitIso (C := C)).inv ▷ (Xᘁ)) := by
  let : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let r : Iᘁ ≅ I := by
    change rightDualObject (𝟙_ C) ≅ 𝟙_ C
    exact rightDualUnitIso
  let J := (Iᘁ) ⊗ (Xᘁ)
  let l : (Xᘁ) ⟶ J := ((ρ_ X).homᘁ) ≫ (rightDualTensorIso X I).hom
  let s : (Xᘁ) ⟶ J := (λ_ (Xᘁ)).inv ≫ r.inv ▷ (Xᘁ)
  have hl : l ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) J = (Xᘁ) ◁ (ρ_ X).hom ≫ ε_ X (Xᘁ) := by
    have he := rightDualIso_evaluation
      (@HasRightDual.exact C _ _ (X ⊗ I) (RightRigidCategory.rightDual _))
      (ExactPairing.tensor (X₁ := X) (X₂ := I) (Y₁ := Xᘁ) (Y₂ := Iᘁ))
    change (rightDualTensorIso X I).hom ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) J =
      ε_ (X ⊗ I) ((X ⊗ I)ᘁ) at he
    dsimp only [l]
    rw [comp_whiskerRight_assoc, he, rightAdjointMate_comp_evaluation]
  have hs : s ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) J = (Xᘁ) ◁ (ρ_ X).hom ≫ ε_ X (Xᘁ) := by
    have he := rightDualIso_inv_evaluation
      (@HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
      (inferInstance : ExactPairing I I)
    change r.inv ▷ I ≫ ε_ I (Iᘁ) = ε_ I I at he
    change ((λ_ (Xᘁ)).inv ≫ r.inv ▷ (Xᘁ)) ▷ (X ⊗ I) ≫
      (𝟙 _ ⊗≫ (Iᘁ) ◁ (ε_ X (Xᘁ) ▷ I) ⊗≫ ε_ I (Iᘁ)) = _
    calc
      _ = 𝟙 _ ⊗≫ ((r.inv ▷ ((Xᘁ ⊗ X) ⊗ I)) ≫
        (Iᘁ : C) ◁ (ε_ X (Xᘁ) ▷ I)) ⊗≫ ε_ I (Iᘁ) := by
          simp only [comp_whiskerRight]
          monoidal
      _ = 𝟙 _ ⊗≫ ((I : C) ◁ (ε_ X (Xᘁ) ▷ I) ≫
        r.inv ▷ ((𝟙_ C) ⊗ I)) ⊗≫ ε_ I (Iᘁ) := by
          rw [← whisker_exchange]
      _ = 𝟙 _ ⊗≫ (ε_ X (Xᘁ) ▷ I) ⊗≫ (r.inv ▷ I ≫ ε_ I (Iᘁ)) := by monoidal
      _ = 𝟙 _ ⊗≫ (ε_ X (Xᘁ) ▷ I) ⊗≫ ε_ I I := by rw [he]
      _ = _ := by
        change 𝟙 _ ⊗≫ (ε_ X (Xᘁ) ▷ I) ⊗≫ (ρ_ I).hom = _
        monoidal
  have h : l ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) J = s ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) J := hl.trans hs.symm
  let : HasRightDual (X ⊗ I) := { rightDual := J, exact := ExactPairing.tensor }
  have hh := congrArg (tensorRightHomEquiv (Xᘁ) (X ⊗ I) J I) h
  have hL := @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ (X ⊗ I) (Xᘁ) this l
  have hR := @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ (X ⊗ I) (Xᘁ) this s
  change (tensorRightHomEquiv (Xᘁ) (X ⊗ I) J I)
    (l ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) J) = l ≫ (λ_ J).inv at hL
  change (tensorRightHomEquiv (Xᘁ) (X ⊗ I) J I)
    (s ▷ (X ⊗ I) ≫ ε_ (X ⊗ I) J) = s ≫ (λ_ J).inv at hR
  rw [hL, hR] at hh
  exact (cancel_mono (λ_ J).inv).1 hh

end PropertyF.Ground.Dimensions
