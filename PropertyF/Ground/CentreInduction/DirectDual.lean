module
public import PropertyF.Ground.CentreInduction.WeakHalfBraiding
public import PropertyF.Ground.CentreRigid.Unit

/-! A direct candidate for the half-braiding on centre duals. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ExactPairing
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]

/-- Bend the inverse half-braiding around the chosen right dual. -/
def directDualCrossing (Z : CategoryTheory.Center D) (T : D) : (Z.1ᘁ : D) ⊗ T ⟶ T ⊗ (Z.1ᘁ : D) :=
  𝟙 _ ⊗≫ ((Z.1ᘁ : D) ⊗ T) ◁ η_ Z.1 (Z.1ᘁ : D) ⊗≫
    ((Z.1ᘁ : D) ◁ (Z.2.β T).inv) ▷ (Z.1ᘁ : D) ⊗≫
    (ε_ Z.1 (Z.1ᘁ : D) ▷ (T ⊗ (Z.1ᘁ : D))) ⊗≫ 𝟙 _

/-- The direct dual crossing is natural in the test object. -/
theorem directDualCrossing_natural (Z : CategoryTheory.Center D) {T U : D} (f : T ⟶ U) :
    ((Z.1ᘁ : D) ◁ f) ≫ directDualCrossing Z U = directDualCrossing Z T ≫ (f ▷ (Z.1ᘁ : D)) := by
  have h : (T ◁ 𝟙 Z.1) ≫ (Z.2.β T).inv ≫ (Z.1 ◁ f) =
      (f ▷ Z.1) ≫ (Z.2.β U).inv := by
    simp only [whiskerLeft_id, Category.id_comp]
    apply (cancel_epi (Z.2.β T).hom).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Z.2.naturality_assoc]
    simp
  calc
    _ = 𝟙 _ ⊗≫ (((((Z.1ᘁ : D) ◁ f) ▷ (𝟙_ D))) ≫
          (((Z.1ᘁ : D) ⊗ U) ◁ η_ Z.1 (Z.1ᘁ : D))) ⊗≫
        ((Z.1ᘁ : D) ◁ (Z.2.β U).inv) ▷ (Z.1ᘁ : D) ⊗≫
        ε_ Z.1 (Z.1ᘁ : D) ▷ (U ⊗ (Z.1ᘁ : D)) ⊗≫ 𝟙 _ := by
      dsimp [directDualCrossing]
      monoidal
    _ = 𝟙 _ ⊗≫ ((((Z.1ᘁ : D) ⊗ T) ◁ η_ Z.1 (Z.1ᘁ : D)) ≫
          (((Z.1ᘁ : D) ◁ f) ▷ (Z.1 ⊗ (Z.1ᘁ : D)))) ⊗≫
        ((Z.1ᘁ : D) ◁ (Z.2.β U).inv) ▷ (Z.1ᘁ : D) ⊗≫
        ε_ Z.1 (Z.1ᘁ : D) ▷ (U ⊗ (Z.1ᘁ : D)) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ ((Z.1ᘁ : D) ⊗ T) ◁ η_ Z.1 (Z.1ᘁ : D) ⊗≫
        ((Z.1ᘁ : D) ◁ ((f ▷ Z.1) ≫ (Z.2.β U).inv)) ▷ (Z.1ᘁ : D) ⊗≫
        ε_ Z.1 (Z.1ᘁ : D) ▷ (U ⊗ (Z.1ᘁ : D)) ⊗≫ 𝟙 _ := by
      simp only [whiskerLeft_comp, comp_whiskerRight]
      monoidal
    _ = 𝟙 _ ⊗≫ ((Z.1ᘁ : D) ⊗ T) ◁ η_ Z.1 (Z.1ᘁ : D) ⊗≫
        ((Z.1ᘁ : D) ◁ ((Z.2.β T).inv ≫ (Z.1 ◁ f))) ▷ (Z.1ᘁ : D) ⊗≫
        ε_ Z.1 (Z.1ᘁ : D) ▷ (U ⊗ (Z.1ᘁ : D)) ⊗≫ 𝟙 _ := by
      simp only [whiskerLeft_id, Category.id_comp] at h
      rw [← h]
    _ = 𝟙 _ ⊗≫ ((Z.1ᘁ : D) ⊗ T) ◁ η_ Z.1 (Z.1ᘁ : D) ⊗≫
        ((Z.1ᘁ : D) ◁ (Z.2.β T).inv) ▷ (Z.1ᘁ : D) ⊗≫
        (((((Z.1ᘁ : D) ⊗ Z.1) ◁ f) ≫ (ε_ Z.1 (Z.1ᘁ : D) ▷ U)) ▷ (Z.1ᘁ : D)) ⊗≫ 𝟙 _ := by
      simp only [whiskerLeft_comp, comp_whiskerRight]
      monoidal
    _ = 𝟙 _ ⊗≫ ((Z.1ᘁ : D) ⊗ T) ◁ η_ Z.1 (Z.1ᘁ : D) ⊗≫
        ((Z.1ᘁ : D) ◁ (Z.2.β T).inv) ▷ (Z.1ᘁ : D) ⊗≫
        (((ε_ Z.1 (Z.1ᘁ : D) ▷ T) ≫ ((𝟙_ D) ◁ f)) ▷ (Z.1ᘁ : D)) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = _ := by
      dsimp [directDualCrossing]
      simp only [whiskerLeft_comp, comp_whiskerRight]
      monoidal
/-- The direct dual crossing is normalized on the unit. -/
theorem directDualCrossing_unit (Z : CategoryTheory.Center D) :
    directDualCrossing Z (𝟙_ D) = (ρ_ (Z.1ᘁ)).hom ≫ (λ_ (Z.1ᘁ)).inv := by
  have hb : (Z.2.β (𝟙_ D)).inv = (λ_ Z.1).hom ≫ (ρ_ Z.1).inv := by
    apply (cancel_epi (Z.2.β (𝟙_ D)).hom).1
    simp only [Iso.hom_inv_id]
    rw [CentreRigid.halfBraiding_unit]
    simp [Category.assoc]
  calc
    _ = 𝟙 _ ⊗≫ (Z.1ᘁ : D) ◁ η_ Z.1 (Z.1ᘁ : D) ⊗≫
        ε_ Z.1 (Z.1ᘁ : D) ▷ (Z.1ᘁ : D) ⊗≫ 𝟙 _ := by
      dsimp [directDualCrossing]
      rw [hb]
      simp only [whiskerLeft_comp, comp_whiskerRight]
      monoidal
    _ = 𝟙 _ ⊗≫ ((Z.1ᘁ : D) ◁ η_ Z.1 (Z.1ᘁ : D) ⊗≫
        ε_ Z.1 (Z.1ᘁ : D) ▷ (Z.1ᘁ : D)) ⊗≫ 𝟙 _ := by monoidal
    _ = _ := by rw [coevaluation_evaluation'']; monoidal

/-- The inverse half-braiding factors in reverse order. -/
theorem halfBraiding_inv_tensor (Z : CategoryTheory.Center D) (T U : D) :
    (Z.2.β (T ⊗ U)).inv =
      (α_ T U Z.1).hom ≫ (T ◁ (Z.2.β U).inv) ≫
        (α_ T Z.1 U).inv ≫ ((Z.2.β T).inv ▷ U) ≫ (α_ Z.1 T U).hom := by
  apply (cancel_epi (Z.2.β (T ⊗ U)).hom).1
  simp only [Iso.hom_inv_id]
  rw [Z.2.monoidal]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← whiskerLeft_comp_assoc,
    Iso.hom_inv_id, whiskerLeft_id, Category.id_comp, ← comp_whiskerRight_assoc,
    Iso.hom_inv_id_assoc, id_whiskerRight]
  simp

end PropertyF.Ground.CentreInduction
