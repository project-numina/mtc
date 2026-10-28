module
public import PropertyF.Ground.CentreInduction.CrossingUnit
public import Mathlib.CategoryTheory.Monoidal.Center

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

set_option backward.isDefEq.respectTransparency false in
/-- The matrix coefficients of the actual induction crossing. -/
theorem crossingCandidate_matrix :
  (biproduct.ι Vᶜ i ▷ T) ≫ crossingCandidate C X T ≫ (T ◁ biproduct.π Vᶜ j) =
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
  let bT : (⨁ V) ⊗ T ⟶ T ⊗ (⨁ V) := crossingCandidate C X T
  let bU : (⨁ V) ⊗ U ⟶ U ⊗ (⨁ V) := crossingCandidate C X U
  calc
    _ = 𝟙 _ ⊗≫ (((biproduct.ι V i ▷ T) ≫ bT) ▷ U) ⊗≫
      (T ◁ bU) ⊗≫ 𝟙 ((T ⊗ U) ⊗ (⨁ V)) := by
      dsimp only [crossingTensorComposite]
      monoidal
    _ = ∑ k, ∑ a : crossingIndex C T i k,
      𝟙 _ ⊗≫ (crossingBlock X T (Sᶜ k)
          (crossingInclusion C T i k a) (crossingProjection C T i k a) ▷ U) ⊗≫
        (T ◁ ((biproduct.ι V k ▷ U) ≫ bU)) ⊗≫ 𝟙 ((T ⊗ U) ⊗ (⨁ V)) := by
      dsimp only [bT]
      rw [crossingCandidate_on_summand]
      simp [monoidalComp, sum_whiskerRight, Preadditive.sum_comp, Preadditive.comp_sum,
        crossingSummand, V]
    _ = _ := by
      dsimp only [bU, V, underlying]
      simp_rw [crossingCandidate_on_summand]
      simp [whiskerLeft_sum, monoidalComp, Preadditive.comp_sum, Preadditive.sum_comp,
        crossingBlock_tensor, crossingSummand, V]

set_option backward.isDefEq.respectTransparency false in
/-- The induction crossing obeys the half-braiding tensor law. -/
theorem crossingCandidate_tensor :
    crossingCandidate C X (T ⊗ U) = crossingTensorComposite C X T U :=
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

/-- The actual matrix crossing is invertible by rigidity. -/
theorem crossingCandidate_isIso :
    IsIso (crossingCandidate C X T) :=
  weak_isIso (crossingCandidate C X) (crossingCandidate_natural_test C X)
    (crossingCandidate_tensor C X) (crossingCandidate_unit C X) T (ᘁT)

/-- The explicit matrix crossings form an actual half-braiding on the
induction sum, with no additional coherence assumptions. -/
def halfBraidingOfCrossingCandidate :
    HalfBraiding (underlying C X) where
  β T := by letI := crossingCandidate_isIso C X T; exact asIso (crossingCandidate C X T)
  monoidal T U := crossingCandidate_tensor C X T U
  naturality f := crossingCandidate_natural_test C X f

/-- The actual induction functor to Mathlib's Drinfeld centre. -/
def induction : C.Obj ⥤ Center C.Obj where
  obj X := ⟨underlying C X, halfBraidingOfCrossingCandidate C X⟩
  map f := ⟨(underlyingFunctor C).map f, crossingCandidate_natural_middle C f⟩
  map_id X := Center.ext _ _ ((underlyingFunctor C).map_id X)
  map_comp f g := Center.ext _ _ ((underlyingFunctor C).map_comp f g)

end PropertyF.Ground.CentreInduction
