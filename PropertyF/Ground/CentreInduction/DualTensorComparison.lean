module
public import PropertyF.Ground.CentreInduction.ForgetDualNaturality
public import PropertyF.Ground.Dimensions.DualTensorNaturality

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- The canonical comparison of duals preserves tensor products of pairings. -/
theorem rightDualIso_tensor {X Y A B A' B' : D}
    (pX : ExactPairing X A) (qX : ExactPairing X A')
    (pY : ExactPairing Y B) (qY : ExactPairing Y B') :
    letI := pX
    letI := pY
    let p := (inferInstance : ExactPairing (X ⊗ Y) (B ⊗ A))
    letI := qX
    letI := qY
    let q := (inferInstance : ExactPairing (X ⊗ Y) (B' ⊗ A'))
    (rightDualIso p q).hom = (rightDualIso pY qY).hom ⊗ₘ (rightDualIso pX qX).hom := by
  dsimp only
  letI : ExactPairing X A := pX
  letI : ExactPairing Y B := pY
  letI : ExactPairing X A' := qX
  letI : ExactPairing Y B' := qY
  have hX := Dimensions.rightDualIso_evaluation pX qX
  have hY := Dimensions.rightDualIso_evaluation pY qY
  have h := Dimensions.rightDualIso_evaluation
    (inferInstance : ExactPairing (X ⊗ Y) (B ⊗ A))
    (inferInstance : ExactPairing (X ⊗ Y) (B' ⊗ A'))
  let a := (rightDualIso pX qX).hom
  let b := (rightDualIso pY qY).hom
  have ht : (b ⊗ₘ a) ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (B' ⊗ A') =
      ε_ (X ⊗ Y) (B ⊗ A) := by
    change (b ⊗ₘ a) ▷ (X ⊗ Y) ≫
      (𝟙 _ ⊗≫ B' ◁ (ε_ X A' ▷ Y) ⊗≫ ε_ Y B') =
      (𝟙 _ ⊗≫ B ◁ (ε_ X A ▷ Y) ⊗≫ ε_ Y B)
    calc
      _ = 𝟙 _ ⊗≫ (b ▷ ((A ⊗ X) ⊗ Y)) ⊗≫
          B' ◁ ((a ▷ X ≫ ε_ X A') ▷ Y) ⊗≫ ε_ Y B' := by
        simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
        monoidal
      _ = 𝟙 _ ⊗≫ ((b ▷ ((A ⊗ X) ⊗ Y)) ≫
          B' ◁ ((a ▷ X ≫ ε_ X A') ▷ Y)) ⊗≫ ε_ Y B' := by monoidal
      _ = 𝟙 _ ⊗≫ (B ◁ ((a ▷ X ≫ ε_ X A') ▷ Y) ≫
          b ▷ ((𝟙_ D) ⊗ Y)) ⊗≫ ε_ Y B' := by rw [whisker_exchange]
      _ = 𝟙 _ ⊗≫ B ◁ ((a ▷ X ≫ ε_ X A') ▷ Y) ⊗≫
          (b ▷ ((𝟙_ D) ⊗ Y)) ⊗≫ ε_ Y B' := by monoidal
      _ = 𝟙 _ ⊗≫ B ◁ ((a ▷ X ≫ ε_ X A') ▷ Y) ⊗≫
          (b ▷ Y ≫ ε_ Y B') := by monoidal
      _ = _ := by rw [hX, hY]
  have hh := h.trans ht.symm
  let l := (rightDualIso (inferInstance : ExactPairing (X ⊗ Y) (B ⊗ A))
    (inferInstance : ExactPairing (X ⊗ Y) (B' ⊗ A'))).hom
  let r := b ⊗ₘ a
  change l ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (B' ⊗ A') =
    r ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (B' ⊗ A') at hh
  letI : HasRightDual (X ⊗ Y) := { rightDual := B' ⊗ A', exact := inferInstance }
  have he := congrArg (tensorRightHomEquiv (B ⊗ A) (X ⊗ Y) (B' ⊗ A') (𝟙_ D)) hh
  have hL := @tensorRightHomEquiv_whiskerRight_comp_evaluation D _ _ (X ⊗ Y) (B ⊗ A) this l
  have hR := @tensorRightHomEquiv_whiskerRight_comp_evaluation D _ _ (X ⊗ Y) (B ⊗ A) this r
  change (tensorRightHomEquiv (B ⊗ A) (X ⊗ Y) (B' ⊗ A') (𝟙_ D))
    (l ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (B' ⊗ A')) = l ≫ (λ_ (B' ⊗ A')).inv at hL
  change (tensorRightHomEquiv (B ⊗ A) (X ⊗ Y) (B' ⊗ A') (𝟙_ D))
    (r ▷ (X ⊗ Y) ≫ ε_ (X ⊗ Y) (B' ⊗ A')) = r ≫ (λ_ (B' ⊗ A')).inv at hR
  rw [hL, hR] at he
  exact (cancel_mono (λ_ (B' ⊗ A')).inv).1 he
end PropertyF.Ground.CentreInduction
