module
public import PropertyF.Ground.Dimensions.DoubleDualUnitTensor

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Canonical right-dual tensor comparisons respect associativity. -/
theorem rightDualTensorIso_associativity {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (X Y Z : C) :
    (rightDualTensorIso (X ⊗ Y) Z).hom ≫
      (Zᘁ) ◁ (rightDualTensorIso X Y).hom =
    ((α_ X Y Z).invᘁ) ≫ (rightDualTensorIso X (Y ⊗ Z)).hom ≫
      (rightDualTensorIso Y Z).hom ▷ (Xᘁ) ≫ (α_ (Zᘁ) (Yᘁ) (Xᘁ)).hom := by
  let A := (X ⊗ Y) ⊗ Z
  let K := Aᘁ
  let B := (Zᘁ) ⊗ ((Yᘁ) ⊗ (Xᘁ))
  let l : K ⟶ B := (rightDualTensorIso (X ⊗ Y) Z).hom ≫
      (Zᘁ) ◁ (rightDualTensorIso X Y).hom
  let r : K ⟶ B := ((α_ X Y Z).invᘁ) ≫ (rightDualTensorIso X (Y ⊗ Z)).hom ≫
      (rightDualTensorIso Y Z).hom ▷ (Xᘁ) ≫ (α_ (Zᘁ) (Yᘁ) (Xᘁ)).hom
  let qXY : ExactPairing (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := ExactPairing.tensor
  let : ExactPairing (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := qXY
  let qA : ExactPairing A B := @ExactPairing.tensor C _ _ (X ⊗ Y) Z ((Yᘁ) ⊗ (Xᘁ)) (Zᘁ)
    qXY HasRightDual.exact
  let : ExactPairing A B := qA
  have hl : l ▷ A ≫ ε_ A B = ε_ A (Aᘁ) := by
    have heXY := rightDualIso_evaluation
      (@HasRightDual.exact C _ _ (X ⊗ Y) (RightRigidCategory.rightDual _))
      (ExactPairing.tensor (X₁ := X) (X₂ := Y) (Y₁ := Xᘁ) (Y₂ := Yᘁ))
    change (rightDualTensorIso X Y).hom ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      ε_ (X ⊗ Y) ((X ⊗ Y)ᘁ) at heXY
    have heA := rightDualIso_evaluation
      (@HasRightDual.exact C _ _ A (RightRigidCategory.rightDual _))
      (ExactPairing.tensor (X₁ := X ⊗ Y) (X₂ := Z) (Y₁ := (X ⊗ Y)ᘁ) (Y₂ := Zᘁ))
    change (rightDualTensorIso (X ⊗ Y) Z).hom ▷ A ≫ ε_ A ((Zᘁ) ⊗ ((X ⊗ Y)ᘁ)) =
      ε_ A (Aᘁ) at heA
    have he' : ((Zᘁ) ◁ (rightDualTensorIso X Y).hom) ▷ A ≫ ε_ A B =
        ε_ A ((Zᘁ) ⊗ ((X ⊗ Y)ᘁ)) := by
      change ((Zᘁ) ◁ (rightDualTensorIso X Y).hom) ▷ A ≫
        @ExactPairing.evaluation C _ _ A B qA = _
      have hq : @ExactPairing.evaluation C _ _ A B qA =
        (𝟙 _ ⊗≫ (Zᘁ : C) ◁ (@ExactPairing.evaluation C _ _ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) qXY ▷ Z) ⊗≫ ε_ Z (Zᘁ)) := by
        change (@ExactPairing.tensor C _ _ (X ⊗ Y) Z ((Yᘁ) ⊗ (Xᘁ)) (Zᘁ) qXY HasRightDual.exact).evaluation' = _
        unfold ExactPairing.tensor
        dsimp
        monoidal
      have hq2 : ε_ A ((Zᘁ) ⊗ ((X ⊗ Y)ᘁ)) =
        (𝟙 _ ⊗≫ (Zᘁ : C) ◁ (ε_ (X ⊗ Y) ((X ⊗ Y)ᘁ) ▷ Z) ⊗≫ ε_ Z (Zᘁ)) := by
        change (@ExactPairing.tensor C _ _ (X ⊗ Y) Z ((X ⊗ Y)ᘁ) (Zᘁ)
          HasRightDual.exact HasRightDual.exact).evaluation' = _
        unfold ExactPairing.tensor
        dsimp
      rw [hq, hq2]
      calc
        _ = 𝟙 _ ⊗≫ (Zᘁ : C) ◁ (((rightDualTensorIso X Y).hom ▷ (X ⊗ Y) ≫
          ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ))) ▷ Z) ⊗≫ ε_ Z (Zᘁ) := by
            simp only [comp_whiskerRight, whiskerLeft_comp]
            monoidal
        _ = _ := by rw [heXY]
    change ((rightDualTensorIso (X ⊗ Y) Z).hom ≫
      (Zᘁ) ◁ (rightDualTensorIso X Y).hom) ▷ A ≫ ε_ A B = _
    rw [comp_whiskerRight_assoc, he', heA]
  have hr : r ▷ A ≫ ε_ A B = ε_ A (Aᘁ) := by
    let D := X ⊗ (Y ⊗ Z)
    let E := ((Zᘁ) ⊗ (Yᘁ)) ⊗ (Xᘁ)
    let qYZ : ExactPairing (Y ⊗ Z) ((Zᘁ) ⊗ (Yᘁ)) := ExactPairing.tensor
    let qD : ExactPairing D E := @ExactPairing.tensor C _ _ X (Y ⊗ Z) (Xᘁ) ((Zᘁ) ⊗ (Yᘁ))
      HasRightDual.exact qYZ
    have ha : (α_ (Zᘁ) (Yᘁ) (Xᘁ)).hom ▷ A ≫
        @ExactPairing.evaluation C _ _ A B qA =
      E ◁ (α_ X Y Z).hom ≫ @ExactPairing.evaluation C _ _ D E qD := by
      change (α_ (Zᘁ) (Yᘁ) (Xᘁ)).hom ▷ A ≫
        (@ExactPairing.tensor C _ _ (X ⊗ Y) Z ((Yᘁ) ⊗ (Xᘁ)) (Zᘁ) qXY HasRightDual.exact).evaluation' =
      E ◁ (α_ X Y Z).hom ≫
        (@ExactPairing.tensor C _ _ X (Y ⊗ Z) (Xᘁ) ((Zᘁ) ⊗ (Yᘁ)) HasRightDual.exact qYZ).evaluation'
      have hxy : @ExactPairing.evaluation C _ _ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) qXY =
          (𝟙 _ ⊗≫ (Yᘁ : C) ◁ (ε_ X (Xᘁ) ▷ Y) ⊗≫ ε_ Y (Yᘁ)) := by
        change (@ExactPairing.tensor C _ _ X Y (Xᘁ) (Yᘁ) HasRightDual.exact HasRightDual.exact).evaluation' = _
        unfold ExactPairing.tensor
        dsimp
      have hyz : @ExactPairing.evaluation C _ _ (Y ⊗ Z) ((Zᘁ) ⊗ (Yᘁ)) qYZ =
          (𝟙 _ ⊗≫ (Zᘁ : C) ◁ (ε_ Y (Yᘁ) ▷ Z) ⊗≫ ε_ Z (Zᘁ)) := by
        change (@ExactPairing.tensor C _ _ Y Z (Yᘁ) (Zᘁ) HasRightDual.exact HasRightDual.exact).evaluation' = _
        unfold ExactPairing.tensor
        dsimp
      unfold ExactPairing.tensor
      dsimp [A, B, D, E]
      rw [hxy, hyz]
      monoidal
    let F := ((Y ⊗ Z)ᘁ) ⊗ (Xᘁ)
    let qD₀ : ExactPairing D F := @ExactPairing.tensor C _ _ X (Y ⊗ Z) (Xᘁ) ((Y ⊗ Z)ᘁ)
      HasRightDual.exact HasRightDual.exact
    have heYZ := rightDualIso_evaluation
      (@HasRightDual.exact C _ _ (Y ⊗ Z) (RightRigidCategory.rightDual _)) qYZ
    change (rightDualTensorIso Y Z).hom ▷ (Y ⊗ Z) ≫
      @ExactPairing.evaluation C _ _ (Y ⊗ Z) ((Zᘁ) ⊗ (Yᘁ)) qYZ =
      ε_ (Y ⊗ Z) ((Y ⊗ Z)ᘁ) at heYZ
    have hqD : @ExactPairing.evaluation C _ _ D E qD =
        (𝟙 _ ⊗≫ ((Zᘁ : C) ⊗ (Yᘁ : C)) ◁ (ε_ X (Xᘁ) ▷ (Y ⊗ Z)) ⊗≫
          @ExactPairing.evaluation C _ _ (Y ⊗ Z) ((Zᘁ) ⊗ (Yᘁ)) qYZ) := by
      change (@ExactPairing.tensor C _ _ X (Y ⊗ Z) (Xᘁ) ((Zᘁ) ⊗ (Yᘁ))
        HasRightDual.exact qYZ).evaluation' = _
      unfold ExactPairing.tensor
      dsimp
      monoidal
    have hqD₀ : @ExactPairing.evaluation C _ _ D F qD₀ =
        (𝟙 _ ⊗≫ ((Y ⊗ Z)ᘁ : C) ◁ (ε_ X (Xᘁ) ▷ (Y ⊗ Z)) ⊗≫ ε_ (Y ⊗ Z) ((Y ⊗ Z)ᘁ)) := by
      change (@ExactPairing.tensor C _ _ X (Y ⊗ Z) (Xᘁ) ((Y ⊗ Z)ᘁ)
        HasRightDual.exact HasRightDual.exact).evaluation' = _
      unfold ExactPairing.tensor
      dsimp
      monoidal
    have hT : ((rightDualTensorIso Y Z).hom ▷ (Xᘁ)) ▷ D ≫
        @ExactPairing.evaluation C _ _ D E qD = @ExactPairing.evaluation C _ _ D F qD₀ := by
      rw [hqD, hqD₀]
      calc
        _ = 𝟙 _ ⊗≫ (((rightDualTensorIso Y Z).hom ▷ (((Xᘁ) ⊗ X) ⊗ (Y ⊗ Z))) ≫
          (((Zᘁ : C) ⊗ (Yᘁ : C)) ◁ (ε_ X (Xᘁ) ▷ (Y ⊗ Z)))) ⊗≫
            @ExactPairing.evaluation C _ _ (Y ⊗ Z) ((Zᘁ) ⊗ (Yᘁ)) qYZ := by monoidal
        _ = 𝟙 _ ⊗≫ ((((Y ⊗ Z)ᘁ : C) ◁ (ε_ X (Xᘁ) ▷ (Y ⊗ Z))) ≫
          (rightDualTensorIso Y Z).hom ▷ ((𝟙_ C) ⊗ (Y ⊗ Z))) ⊗≫
            @ExactPairing.evaluation C _ _ (Y ⊗ Z) ((Zᘁ) ⊗ (Yᘁ)) qYZ := by
              rw [← whisker_exchange]
        _ = 𝟙 _ ⊗≫ (((Y ⊗ Z)ᘁ : C) ◁ (ε_ X (Xᘁ) ▷ (Y ⊗ Z))) ⊗≫
          ((rightDualTensorIso Y Z).hom ▷ (Y ⊗ Z) ≫
            @ExactPairing.evaluation C _ _ (Y ⊗ Z) ((Zᘁ) ⊗ (Yᘁ)) qYZ) := by monoidal
        _ = _ := by rw [heYZ]
    have heD := rightDualIso_evaluation
      (@HasRightDual.exact C _ _ D (RightRigidCategory.rightDual _)) qD₀
    change (rightDualTensorIso X (Y ⊗ Z)).hom ▷ D ≫
      @ExactPairing.evaluation C _ _ D F qD₀ = ε_ D (Dᘁ) at heD
    change (((α_ X Y Z).invᘁ) ≫ (rightDualTensorIso X (Y ⊗ Z)).hom ≫
      (rightDualTensorIso Y Z).hom ▷ (Xᘁ) ≫ (α_ (Zᘁ) (Yᘁ) (Xᘁ)).hom) ▷ A ≫
        @ExactPairing.evaluation C _ _ A B qA = ε_ A (Aᘁ)
    simp only [comp_whiskerRight_assoc]
    rw [ha, ← whisker_exchange_assoc, hT, ← whisker_exchange_assoc, heD,
      ← whisker_exchange_assoc, rightAdjointMate_comp_evaluation]
    rw [← Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
  have he := hl.trans hr.symm
  let : HasRightDual A := { rightDual := B, exact := ExactPairing.tensor }
  have hh := congrArg (tensorRightHomEquiv K A B (𝟙_ C)) he
  have hL := @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ A K this l
  have hR := @tensorRightHomEquiv_whiskerRight_comp_evaluation C _ _ A K this r
  change (tensorRightHomEquiv K A B (𝟙_ C)) (l ▷ A ≫ ε_ A B) = l ≫ (λ_ B).inv at hL
  change (tensorRightHomEquiv K A B (𝟙_ C)) (r ▷ A ≫ ε_ A B) = r ≫ (λ_ B).inv at hR
  rw [hL, hR] at hh
  exact (cancel_mono (λ_ B).inv).1 hh
end PropertyF.Ground.Dimensions
