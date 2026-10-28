module
public import PropertyF.Ground.CentreInduction.CrossingNaturality
public import PropertyF.Ground.CentreInduction.SimpleDetection

section
/-! The induction crossing tensor law is detected on pairs of simple objects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
local notation "A" => underlying C X
local notation "b" => crossingCandidate C X

/-- The composite of two crossings, with the associators inserted. -/
def crossingTensorComposite (T U : C.Obj) : A ⊗ (T ⊗ U) ⟶ (T ⊗ U) ⊗ A :=
  (α_ _ _ _).inv ≫ (b T ▷ U) ≫ (α_ _ _ _).hom ≫
    (T ◁ b U) ≫ (α_ _ _ _).inv














end PropertyF.Ground.CentreInduction

end
end

/-! A natural tensor-compatible crossing is invertible in a rigid category. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ExactPairing
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (A : C) (b : ∀ T : C, A ⊗ T ⟶ T ⊗ A)
variable (hn : ∀ {T U} (f : T ⟶ U), (A ◁ f) ≫ b U = b T ≫ (f ▷ A))
variable (ht : ∀ T U, b (T ⊗ U) =
    (α_ _ _ _).inv ≫ (b T ▷ U) ≫ (α_ _ _ _).hom ≫ (T ◁ b U) ≫ (α_ _ _ _).inv)
variable (hu : b (𝟙_ C) = (ρ_ A).hom ≫ (λ_ A).inv)
variable (X Y : C) [ExactPairing X Y]

/-- Bend the dual crossed strand to form the inverse crossing. -/
def weakInverse : Y ⊗ A ⟶ A ⊗ Y :=
  𝟙 _ ⊗≫ (Y ⊗ A) ◁ η_ X Y ⊗≫ (Y ◁ b X) ▷ Y ⊗≫ (ε_ X Y ▷ A) ▷ Y ⊗≫ 𝟙 _

include hn ht hu in
/-- The bent crossing is a right inverse. -/
theorem weak_left : b Y ≫ weakInverse A b X Y = 𝟙 (A ⊗ Y) := by
  have he : b (Y ⊗ X) ≫ (ε_ X Y ▷ A) =
      (A ◁ ε_ X Y) ≫ ((ρ_ A).hom ≫ (λ_ A).inv) := by
    rw [← hn (ε_ X Y), hu]
  calc
    _ = 𝟙 _ ⊗≫ ((b Y ▷ (𝟙_ C)) ≫ ((Y ⊗ A) ◁ η_ X Y)) ⊗≫
      (Y ◁ b X) ▷ Y ⊗≫ (ε_ X Y ▷ A) ▷ Y ⊗≫ 𝟙 _ := by
      dsimp [weakInverse]; monoidal
    _ = 𝟙 _ ⊗≫ (((A ⊗ Y) ◁ η_ X Y) ≫ (b Y ▷ (X ⊗ Y))) ⊗≫
      (Y ◁ b X) ▷ Y ⊗≫ (ε_ X Y ▷ A) ▷ Y ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (A ◁ (Y ◁ η_ X Y)) ⊗≫ (b (Y ⊗ X) ▷ Y) ⊗≫
      ((ε_ X Y ▷ A) ▷ Y) ⊗≫ 𝟙 _ := by rw [ht Y X]; monoidal
    _ = 𝟙 _ ⊗≫ (A ◁ (Y ◁ η_ X Y)) ⊗≫
      ((b (Y ⊗ X) ≫ ε_ X Y ▷ A) ▷ Y) ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ (A ◁ (Y ◁ η_ X Y)) ⊗≫
      ((A ◁ ε_ X Y ≫ (ρ_ A).hom ≫ (λ_ A).inv) ▷ Y) ⊗≫ 𝟙 _ := by rw [he]
    _ = 𝟙 _ ⊗≫ (A ◁ (Y ◁ η_ X Y ⊗≫ ε_ X Y ▷ Y)) ⊗≫ 𝟙 _ := by monoidal
    _ = _ := by rw [coevaluation_evaluation'']; monoidal

include hn ht hu in
/-- The bent crossing is a left inverse. -/
theorem weak_right : weakInverse A b X Y ≫ b Y = 𝟙 (Y ⊗ A) := by
  have hc : (A ◁ η_ X Y) ≫ b (X ⊗ Y) =
      ((ρ_ A).hom ≫ (λ_ A).inv) ≫ (η_ X Y ▷ A) := by
    rw [hn (η_ X Y), hu]
  calc
    _ = 𝟙 _ ⊗≫ (Y ⊗ A) ◁ η_ X Y ⊗≫ (Y ◁ b X) ▷ Y ⊗≫
      ((ε_ X Y ▷ (A ⊗ Y)) ≫ ((𝟙_ C) ◁ b Y)) ⊗≫ 𝟙 _ := by
      dsimp [weakInverse]; monoidal
    _ = 𝟙 _ ⊗≫ (Y ⊗ A) ◁ η_ X Y ⊗≫ (Y ◁ b X) ▷ Y ⊗≫
      (((Y ⊗ X) ◁ b Y) ≫ (ε_ X Y ▷ (Y ⊗ A))) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (Y ◁ ((A ◁ η_ X Y) ≫ b (X ⊗ Y))) ⊗≫
      (ε_ X Y ▷ (Y ⊗ A)) ⊗≫ 𝟙 _ := by rw [ht X Y]; monoidal
    _ = 𝟙 _ ⊗≫ (Y ◁ (((ρ_ A).hom ≫ (λ_ A).inv) ≫ (η_ X Y ▷ A))) ⊗≫
      (ε_ X Y ▷ (Y ⊗ A)) ⊗≫ 𝟙 _ := by rw [hc]
    _ = 𝟙 _ ⊗≫ ((Y ◁ η_ X Y ⊗≫ ε_ X Y ▷ Y) ▷ A) ⊗≫ 𝟙 _ := by monoidal
    _ = _ := by rw [coevaluation_evaluation'']; monoidal


include hn ht hu in
/-- Tensor compatibility, naturality, and unit normalization imply that the
crossing is invertible on every object admitting a left dual. -/
theorem weak_isIso (X : C) [ExactPairing X Y] : IsIso (b Y) := by
  let e : A ⊗ Y ≅ Y ⊗ A :=
    { hom := b Y
      inv := weakInverse A b X Y
      hom_inv_id := weak_left A b hn ht hu X Y
      inv_hom_id := weak_right A b hn ht hu X Y }
  exact e.isIso_hom

end PropertyF.Ground.CentreInduction
