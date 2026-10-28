module
public import PropertyF.Ground.CentreInduction.CrossingUnit

/-! Tensor coherence of the actual induction crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u}) (X T : C.Obj)

set_option backward.isDefEq.respectTransparency false in
/-- The matrix coefficients of the actual induction crossing. -/
theorem crossingCandidate_matrix (i j : Fin (rank C)) :
  let V := inductionSummand C X
  (biproduct.ι V i ▷ T) ≫ crossingCandidate C X T ≫ (T ◁ biproduct.π V j) =
    ∑ a, crossingSummand C X T i j a := by
  simp [crossingCandidate_on_summand_assoc, Preadditive.sum_comp, Category.assoc,
    ← whiskerLeft_comp, biproduct.ι_π, whiskerLeft_dite, comp_dite, crossingSummand]

set_option backward.isDefEq.respectTransparency false in
/-- Two crossings on a summand expand into nested fusion blocks. -/
theorem crossingComposite_summand (U : C.Obj) (i : Fin (rank C)) :
  let V := inductionSummand C X
  (biproduct.ι V i ▷ (T ⊗ U)) ≫ crossingTensorComposite C X T U =
    ∑ k, ∑ a : crossingIndex C T i k, ∑ j, ∑ b : crossingIndex C U k j,
      nestedCrossingBlock C X T U i k j a b ≫ ((T ⊗ U) ◁ biproduct.ι V j) := by
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
      𝟙 _ ⊗≫ (crossingBlock X T (simples C k)
          (crossingInclusion C T i k a) (crossingProjection C T i k a) ▷ U) ⊗≫
        (T ◁ ((biproduct.ι V k ▷ U) ≫ bU)) ⊗≫ 𝟙 ((T ⊗ U) ⊗ (⨁ V)) := by
      dsimp only [bT]
      rw [crossingCandidate_on_summand]
      simp only [monoidalComp, sum_whiskerRight, Preadditive.sum_comp, Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
      monoidal
    _ = _ := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => ?_
      dsimp only [bU]
      rw [crossingCandidate_on_summand]
      simp only [whiskerLeft_sum, monoidalComp, Preadditive.comp_sum, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
      rw [crossingBlock_tensor]
      monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The induction crossing obeys the half-braiding tensor law. -/
theorem crossingCandidate_tensor (U : C.Obj) :
    crossingCandidate C X (T ⊗ U) = crossingTensorComposite C X T U := by
  let V := inductionSummand C X
  refine rightDistributor_ext_left (f := V) fun i => ?_
  rw [crossingCandidate_on_summand, crossingComposite_summand]
  simp_rw [← Preadditive.sum_comp, ← crossingBlock_refinement C X T U i]
  simp only [Fintype.sum_sigma, Preadditive.sum_comp]
  dsimp only [underlying, V] at *
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (crossingIndex C U k _)))
    (t := (Finset.univ : Finset (crossingIndex C T i k)))]
  rw [Finset.sum_comm]

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
