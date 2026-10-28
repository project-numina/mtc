module
public import PropertyF.Ground.CentreInduction.CrossingUnit

/-! Composition of the dual mates and blocks in the induction crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ExactPairing
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- A map to a right dual is determined by its evaluation. -/
theorem dual_map_ext {V : C.Obj} (S : C.Obj) (f g : V ⟶ Sᘁ)
    (h : f ▷ S ≫ ε_ S (Sᘁ) = g ▷ S ≫ ε_ S (Sᘁ)) : f = g := by
  apply (cancel_mono (λ_ (Sᘁ)).inv).1
  simpa only [tensorRightHomEquiv_whiskerRight_comp_evaluation] using
    congrArg (tensorRightHomEquiv V S (Sᘁ) (𝟙_ C.Obj)) h

set_option backward.isDefEq.respectTransparency false in
/-- Closing a composite fusion map is the composite of the two closed maps. -/
theorem closeFusionMap_tensor {T U S K R : C.Obj} (f : T ⊗ K ⟶ R) (g : U ⊗ S ⟶ K) :
  closeFusionMap C (T ⊗ U) S R ((α_ T U S).hom ≫ (T ◁ g) ≫ f) =
    𝟙 _ ⊗≫ (closeFusionMap C T K R f ▷ U) ⊗≫ closeFusionMap C U S K g := by
  apply dual_map_ext C
  rw [closeFusionMap_evaluation]
  calc
    _ = 𝟙 _ ⊗≫ ((Rᘁ : C.Obj) ◁ ((α_ T U S).hom ≫ (T ◁ g) ≫ f)) ⊗≫ ε_ R (Rᘁ) := rfl
    _ = 𝟙 _ ⊗≫ ((Rᘁ : C.Obj) ◁ T ◁ g) ⊗≫ ((Rᘁ : C.Obj) ◁ f) ⊗≫ ε_ R (Rᘁ) := by
      simp only [whiskerLeft_comp]; monoidal
    _ = 𝟙 _ ⊗≫ ((Rᘁ : C.Obj) ◁ T ◁ g) ⊗≫
      (𝟙 (((Rᘁ : C.Obj) ⊗ T) ⊗ K) ⊗≫ ((Rᘁ : C.Obj) ◁ f) ⊗≫ ε_ R (Rᘁ)) := by monoidal
    _ = 𝟙 _ ⊗≫ ((Rᘁ : C.Obj) ◁ T ◁ g) ⊗≫
      (closeFusionMap C T K R f ▷ K ≫ ε_ K (Kᘁ)) := by rw [closeFusionMap_evaluation]
    _ = 𝟙 _ ⊗≫ ((((Rᘁ : C.Obj) ⊗ T) ◁ g) ≫ (closeFusionMap C T K R f ▷ K)) ⊗≫ ε_ K (Kᘁ) := by monoidal
    _ = 𝟙 _ ⊗≫ ((closeFusionMap C T K R f ▷ (U ⊗ S)) ≫ ((Kᘁ : C.Obj) ◁ g)) ⊗≫ ε_ K (Kᘁ) := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (closeFusionMap C T K R f ▷ (U ⊗ S)) ⊗≫
      (𝟙 (((Kᘁ : C.Obj) ⊗ U) ⊗ S) ⊗≫ ((Kᘁ : C.Obj) ◁ g) ⊗≫ ε_ K (Kᘁ)) := by monoidal
    _ = 𝟙 _ ⊗≫ (closeFusionMap C T K R f ▷ (U ⊗ S)) ⊗≫
      (closeFusionMap C U S K g ▷ S ≫ ε_ S (Sᘁ)) := by rw [closeFusionMap_evaluation]
    _ = _ := by monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Two crossing blocks compose to the block of their composite fusion maps. -/
theorem crossingBlock_tensor (X : C.Obj) {T U S K R : C.Obj}
    (g₁ : R ⟶ T ⊗ K) (g₂ : K ⟶ U ⊗ S)
    (f₁ : T ⊗ K ⟶ R) (f₂ : U ⊗ S ⟶ K) :
  crossingBlock C X (T ⊗ U) R S (g₁ ≫ (T ◁ g₂) ≫ (α_ T U S).inv)
      ((α_ T U S).hom ≫ (T ◁ f₂) ≫ f₁) =
    𝟙 _ ⊗≫ (crossingBlock C X T R K g₁ f₁ ▷ U) ⊗≫
      (T ◁ crossingBlock C X U K S g₂ f₂) ⊗≫ 𝟙 _ := by
  let q := closeFusionMap C T K R f₁
  let z := closeFusionMap C U S K f₂
  calc
    _ = 𝟙 _ ⊗≫ (g₁ ▷ (X ⊗ (((Rᘁ : C.Obj) ⊗ T) ⊗ U))) ⊗≫
      ((((T ◁ g₂) ▷ X) ▷ (((Rᘁ : C.Obj) ⊗ T) ⊗ U)) ≫
        (((T ⊗ (U ⊗ S)) ⊗ X) ◁ (q ▷ U))) ⊗≫
      (((T ⊗ (U ⊗ S)) ⊗ X) ◁ z) ⊗≫ 𝟙 _ := by
        dsimp only [crossingBlock]
        rw [closeFusionMap_tensor]
        simp only [tensorHom_def, comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ (g₁ ▷ (X ⊗ (((Rᘁ : C.Obj) ⊗ T) ⊗ U))) ⊗≫
      (((((T ⊗ K) ⊗ X) ◁ (q ▷ U))) ≫
        (((T ◁ g₂) ▷ X) ▷ ((Kᘁ : C.Obj) ⊗ U))) ⊗≫
      (((T ⊗ (U ⊗ S)) ⊗ X) ◁ z) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = _ := by
      dsimp only [crossingBlock]
      simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
      monoidal

end PropertyF.Ground.CentreInduction
