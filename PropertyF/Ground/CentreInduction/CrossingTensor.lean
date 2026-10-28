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
theorem dual_map_ext {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [RightRigidCategory D] {V : D} (S : D) (f g : V ⟶ Sᘁ)
    (h : f ▷ S ≫ ε_ S (Sᘁ) = g ▷ S ≫ ε_ S (Sᘁ)) : f = g := by
  apply (cancel_mono (λ_ (Sᘁ)).inv).1
  simpa only [tensorRightHomEquiv_whiskerRight_comp_evaluation] using
    congrArg (tensorRightHomEquiv V S (Sᘁ) (𝟙_ D)) h

set_option backward.isDefEq.respectTransparency false in
/-- Closing a composite fusion map is the composite of the two closed maps. -/
theorem closeFusionMap_tensor {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [RightRigidCategory D] {T U S K R : D} (f : T ⊗ K ⟶ R) (g : U ⊗ S ⟶ K) :
  closeFusionMap (T ⊗ U) S R ((α_ T U S).hom ≫ (T ◁ g) ≫ f) =
    𝟙 _ ⊗≫ (closeFusionMap T K R f ▷ U) ⊗≫ closeFusionMap U S K g := by
  apply dual_map_ext
  rw [closeFusionMap_evaluation]
  calc
    _ = 𝟙 _ ⊗≫ ((Rᘁ : D) ◁ ((α_ T U S).hom ≫ (T ◁ g) ≫ f)) ⊗≫ ε_ R (Rᘁ) := rfl
    _ = 𝟙 _ ⊗≫ ((Rᘁ : D) ◁ T ◁ g) ⊗≫ ((Rᘁ : D) ◁ f) ⊗≫ ε_ R (Rᘁ) := by
      simp only [whiskerLeft_comp]; monoidal
    _ = 𝟙 _ ⊗≫ ((Rᘁ : D) ◁ T ◁ g) ⊗≫
      (𝟙 (((Rᘁ : D) ⊗ T) ⊗ K) ⊗≫ ((Rᘁ : D) ◁ f) ⊗≫ ε_ R (Rᘁ)) := by monoidal
    _ = 𝟙 _ ⊗≫ ((Rᘁ : D) ◁ T ◁ g) ⊗≫
      (closeFusionMap T K R f ▷ K ≫ ε_ K (Kᘁ)) := by rw [closeFusionMap_evaluation]
    _ = 𝟙 _ ⊗≫ ((((Rᘁ : D) ⊗ T) ◁ g) ≫ (closeFusionMap T K R f ▷ K)) ⊗≫ ε_ K (Kᘁ) := by monoidal
    _ = 𝟙 _ ⊗≫ ((closeFusionMap T K R f ▷ (U ⊗ S)) ≫ ((Kᘁ : D) ◁ g)) ⊗≫ ε_ K (Kᘁ) := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (closeFusionMap T K R f ▷ (U ⊗ S)) ⊗≫
      (𝟙 (((Kᘁ : D) ⊗ U) ⊗ S) ⊗≫ ((Kᘁ : D) ◁ g) ⊗≫ ε_ K (Kᘁ)) := by monoidal
    _ = 𝟙 _ ⊗≫ (closeFusionMap T K R f ▷ (U ⊗ S)) ⊗≫
      (closeFusionMap U S K g ▷ S ≫ ε_ S (Sᘁ)) := by rw [closeFusionMap_evaluation]
    _ = _ := by monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Two crossing blocks compose to the block of their composite fusion maps. -/
theorem crossingBlock_tensor {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
    (X : D) {T U S K R : D}
    (g₁ : R ⟶ T ⊗ K) (g₂ : K ⟶ U ⊗ S)
    (f₁ : T ⊗ K ⟶ R) (f₂ : U ⊗ S ⟶ K) :
  crossingBlock X (T ⊗ U) R S (g₁ ≫ (T ◁ g₂) ≫ (α_ T U S).inv)
      ((α_ T U S).hom ≫ (T ◁ f₂) ≫ f₁) =
    𝟙 _ ⊗≫ (crossingBlock X T R K g₁ f₁ ▷ U) ⊗≫
      (T ◁ crossingBlock X U K S g₂ f₂) ⊗≫ 𝟙 _ := by
  let q := closeFusionMap T K R f₁
  let z := closeFusionMap U S K f₂
  calc
    _ = 𝟙 _ ⊗≫ (g₁ ▷ (X ⊗ (((Rᘁ : D) ⊗ T) ⊗ U))) ⊗≫
      ((((T ◁ g₂) ▷ X) ▷ (((Rᘁ : D) ⊗ T) ⊗ U)) ≫
        (((T ⊗ (U ⊗ S)) ⊗ X) ◁ (q ▷ U))) ⊗≫
      (((T ⊗ (U ⊗ S)) ⊗ X) ◁ z) ⊗≫ 𝟙 _ := by
        dsimp only [crossingBlock]
        rw [closeFusionMap_tensor]
        simp only [tensorHom_def, comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ (g₁ ▷ (X ⊗ (((Rᘁ : D) ⊗ T) ⊗ U))) ⊗≫
      (((((T ⊗ K) ⊗ X) ◁ (q ▷ U))) ≫
        (((T ◁ g₂) ▷ X) ▷ ((Kᘁ : D) ⊗ U))) ⊗≫
      (((T ⊗ (U ⊗ S)) ⊗ X) ◁ z) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = _ := by
      dsimp only [crossingBlock]
      simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
      monoidal

end PropertyF.Ground.CentreInduction
