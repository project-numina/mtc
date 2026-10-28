module
public import PropertyF.Ground.CentreInduction.CrossingUnit
public import Mathlib.CategoryTheory.Monoidal.Center
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! # Induction crossing

Rigidity makes a natural tensor-compatible crossing invertible. The matrix crossings of the
induction object therefore define its half-braiding and the centre induction functor.
-/

section
/-! A natural tensor-compatible crossing is invertible in a rigid category. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ExactPairing
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {A : C} (b : ∀ T : C, A ⊗ T ⟶ T ⊗ A)
variable (hn : ∀ {T U} (f : T ⟶ U), (A ◁ f) ≫ b U = b T ≫ (f ▷ A))
variable (ht : ∀ T U, b (T ⊗ U) =
    (α_ _ _ _).inv ≫ (b T ▷ U) ≫ (α_ _ _ _).hom ≫ (T ◁ b U) ≫ (α_ _ _ _).inv)
variable (hu : b (𝟙_ C) = (ρ_ A).hom ≫ (λ_ A).inv)
variable (X Y : C) [ExactPairing X Y]

/-- Bend the dual crossed strand to form the inverse crossing. -/
def weakInverse : Y ⊗ A ⟶ A ⊗ Y :=
  𝟙 _ ⊗≫ (Y ⊗ A) ◁ η_ X Y ⊗≫ (Y ◁ b X) ▷ Y ⊗≫ (ε_ X Y ▷ A) ▷ Y ⊗≫ 𝟙 _

include hu in
/-- The bent crossing is a right inverse when it is natural at evaluation. -/
theorem weak_left
    (hε : (A ◁ ε_ X Y) ≫ b (𝟙_ C) = b (Y ⊗ X) ≫ (ε_ X Y ▷ A))
    (hYX : b (Y ⊗ X) = (α_ _ _ _).inv ≫ (b Y ▷ X) ≫
      (α_ _ _ _).hom ≫ (Y ◁ b X) ≫ (α_ _ _ _).inv) :
    b Y ≫ weakInverse b X Y = 𝟙 (A ⊗ Y) := by
  calc
    _ = 𝟙 _ ⊗≫ ((b Y ▷ (𝟙_ C)) ≫ ((Y ⊗ A) ◁ η_ X Y)) ⊗≫
      (Y ◁ b X) ▷ Y ⊗≫ (ε_ X Y ▷ A) ▷ Y ⊗≫ 𝟙 _ := by
      dsimp [weakInverse]; monoidal
    _ = 𝟙 _ ⊗≫ (((A ⊗ Y) ◁ η_ X Y) ≫ (b Y ▷ (X ⊗ Y))) ⊗≫
      (Y ◁ b X) ▷ Y ⊗≫ (ε_ X Y ▷ A) ▷ Y ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (A ◁ (Y ◁ η_ X Y)) ⊗≫
      ((b (Y ⊗ X) ≫ ε_ X Y ▷ A) ▷ Y) ⊗≫ 𝟙 _ := by rw [hYX]; monoidal
    _ = 𝟙 _ ⊗≫ (A ◁ (Y ◁ η_ X Y ⊗≫ ε_ X Y ▷ Y)) ⊗≫ 𝟙 _ := by
      rw [← hε, hu]
      monoidal
    _ = _ := by rw [coevaluation_evaluation'']; monoidal

include hu in
/-- The bent crossing is a left inverse when it is natural at coevaluation. -/
theorem weak_right
    (hη : (A ◁ η_ X Y) ≫ b (X ⊗ Y) = b (𝟙_ C) ≫ (η_ X Y ▷ A))
    (hXY : b (X ⊗ Y) = (α_ _ _ _).inv ≫ (b X ▷ Y) ≫
      (α_ _ _ _).hom ≫ (X ◁ b Y) ≫ (α_ _ _ _).inv) :
    weakInverse b X Y ≫ b Y = 𝟙 (Y ⊗ A) := by
  calc
    _ = 𝟙 _ ⊗≫ (Y ⊗ A) ◁ η_ X Y ⊗≫ (Y ◁ b X) ▷ Y ⊗≫
      ((ε_ X Y ▷ (A ⊗ Y)) ≫ ((𝟙_ C) ◁ b Y)) ⊗≫ 𝟙 _ := by
      dsimp [weakInverse]; monoidal
    _ = 𝟙 _ ⊗≫ (Y ⊗ A) ◁ η_ X Y ⊗≫ (Y ◁ b X) ▷ Y ⊗≫
      (((Y ⊗ X) ◁ b Y) ≫ (ε_ X Y ▷ (Y ⊗ A))) ⊗≫ 𝟙 _ := by
      rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ (Y ◁ ((A ◁ η_ X Y) ≫ b (X ⊗ Y))) ⊗≫
      (ε_ X Y ▷ (Y ⊗ A)) ⊗≫ 𝟙 _ := by rw [hXY]; monoidal
    _ = 𝟙 _ ⊗≫ ((Y ◁ η_ X Y ⊗≫ ε_ X Y ▷ Y) ▷ A) ⊗≫ 𝟙 _ := by
      rw [hη, hu]
      monoidal
    _ = _ := by rw [coevaluation_evaluation'']; monoidal

include hn ht hu in
/-- Tensor compatibility, naturality, and unit normalization imply that the
crossing is invertible on every object admitting a left dual. -/
theorem weak_isIso (X : C) [ExactPairing X Y] : IsIso (b Y) :=
  ⟨⟨weakInverse b X Y, weak_left b hu X Y (hn (ε_ X Y)) (ht Y X),
    weak_right b hu X Y (hn (η_ X Y)) (ht X Y)⟩⟩

end PropertyF.Ground.CentreInduction
end
end

/-! Tensor coherence of the actual induction crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u}) (X T U : C.Obj) (i j : Fin (rank C))
-- Chosen simple representatives of the base category.
local notation "Sᶜ" => simples C
-- The simple-indexed summands of the induced object.
local notation "Vᶜ" => inductionSummand C X
-- The induction crossing on X.
local notation "βᶜ" => crossingCandidate C X

set_option backward.isDefEq.respectTransparency false in
/-- The matrix coefficients of the actual induction crossing. -/
theorem crossingCandidate_matrix :
  (biproduct.ι Vᶜ i ▷ T) ≫ βᶜ T ≫ (T ◁ biproduct.π Vᶜ j) =
    ∑ a, crossingSummand C X T i j a := by
  simp [crossingCandidate_on_summand_assoc, Preadditive.sum_comp, Category.assoc,
    ← whiskerLeft_comp, biproduct.ι_π, whiskerLeft_dite, comp_dite, crossingSummand]

set_option backward.isDefEq.respectTransparency false in
/-- Two crossings on a summand expand into nested fusion blocks. -/
theorem crossingComposite_summand :
  (biproduct.ι Vᶜ i ▷ (T ⊗ U)) ≫ crossingTensorComposite C X T U =
    ∑ k, ∑ a : crossingIndex C T i k, ∑ j, ∑ b : crossingIndex C U k j,
      nestedCrossingBlock C X T U i k j a b ≫ ((T ⊗ U) ◁ biproduct.ι Vᶜ j) := by
  dsimp only [nestedCrossingBlock]
  let V := inductionSummand C X
  let b (A : C.Obj) : (⨁ V) ⊗ A ⟶ A ⊗ (⨁ V) := βᶜ A
  calc
    _ = 𝟙 _ ⊗≫ (((biproduct.ι V i ▷ T) ≫ b T) ▷ U) ⊗≫
      (T ◁ b U) ⊗≫ 𝟙 ((T ⊗ U) ⊗ (⨁ V)) := by
      dsimp only [crossingTensorComposite]
      monoidal
    _ = ∑ k, ∑ a : crossingIndex C T i k,
      𝟙 _ ⊗≫ (crossingBlock X T (Sᶜ k)
          (crossingInclusion C T i k a) (crossingProjection C T i k a) ▷ U) ⊗≫
        (T ◁ ((biproduct.ι V k ▷ U) ≫ b U)) ⊗≫ 𝟙 ((T ⊗ U) ⊗ (⨁ V)) := by
      dsimp only [b]
      rw [crossingCandidate_on_summand]
      simp [monoidalComp, sum_whiskerRight, Preadditive.sum_comp, Preadditive.comp_sum,
        crossingSummand, V]
    _ = _ := by
      dsimp only [b, V, underlying]
      simp_rw [crossingCandidate_on_summand]
      simp [whiskerLeft_sum, monoidalComp, Preadditive.comp_sum, Preadditive.sum_comp,
        crossingBlock_tensor, crossingSummand, V]

set_option backward.isDefEq.respectTransparency false in
/-- The induction crossing obeys the half-braiding tensor law. -/
theorem crossingCandidate_tensor :
    βᶜ (T ⊗ U) = crossingTensorComposite C X T U :=
  rightDistributor_ext_left (f := inductionSummand C X) fun i => by
    rw [crossingCandidate_on_summand, crossingComposite_summand]
    simp_rw [← Preadditive.sum_comp, ← crossingBlock_refinement C X T U i]
    simp only [Fintype.sum_sigma, Preadditive.sum_comp]
    dsimp only [underlying] at *
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (crossingIndex C U _ _)))
      (t := (Finset.univ : Finset (crossingIndex C T i _))),
      Finset.sum_comm (s := (Finset.univ : Finset (Fin (rank C))))
        (t := (Finset.univ : Finset (crossingIndex C T i _)))]

/-- The explicit matrix crossings form an actual half-braiding on the
induction sum, with no additional coherence assumptions. -/
def halfBraidingOfCrossingCandidate :
    HalfBraiding (underlying C X) where
  β T := by
    letI := weak_isIso βᶜ (crossingCandidate_natural_test C X)
      (crossingCandidate_tensor C X) (crossingCandidate_unit C X) T (ᘁT)
    exact asIso (βᶜ T)
  monoidal T U := crossingCandidate_tensor C X T U
  naturality f := crossingCandidate_natural_test C X f

/-- The actual induction functor to Mathlib's Drinfeld centre. -/
def induction : C.Obj ⥤ Center C.Obj where
  obj X := ⟨underlying C X, halfBraidingOfCrossingCandidate C X⟩
  map f := ⟨(underlyingFunctor C).map f, crossingCandidate_natural_middle C f⟩
  map_id X := Center.ext _ _ ((underlyingFunctor C).map_id X)
  map_comp f g := Center.ext _ _ ((underlyingFunctor C).map_comp f g)

end PropertyF.Ground.CentreInduction
