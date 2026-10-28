module
public import PropertyF.Ground.CentreInduction.CrossingUnit

/-! Tensor coherence of the actual induction crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- The matrix coefficients of the actual induction crossing. -/
theorem crossingCandidate_matrix (X T : C.Obj) (i j : Fin (rank C)) :
  let V := inductionSummand C X
  (biproduct.ι V i ▷ T) ≫ crossingCandidate C X T ≫ (T ◁ biproduct.π V j) =
    ∑ a, crossingBlock X T (simples C i) (simples C j)
      (crossingInclusion C T i j a) (crossingProjection C T i j a) := by
  classical
  dsimp
  rw [crossingCandidate_on_summand_assoc]
  rw [Preadditive.sum_comp, Finset.sum_eq_single j]
  · simp only [Preadditive.sum_comp, Category.assoc, ← whiskerLeft_comp,
      biproduct.ι_π_self, whiskerLeft_id, Category.comp_id]
  · intro k _ hne
    simp only [Preadditive.sum_comp, Category.assoc, ← whiskerLeft_comp]
    simp [biproduct.ι_π_ne _ hne]
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- Two crossings on a summand expand into nested fusion blocks. -/
theorem crossingComposite_summand (X T U : C.Obj) (i : Fin (rank C)) :
  let V := inductionSummand C X
  (biproduct.ι V i ▷ (T ⊗ U)) ≫ crossingTensorComposite C X T U =
    ∑ k, ∑ a : crossingIndex C T i k,
      ∑ j, ∑ b : crossingIndex C U k j,
        crossingBlock X (T ⊗ U) (simples C i) (simples C j)
          (crossingInclusion C T i k a ≫ (T ◁ crossingInclusion C U k j b) ≫
            (α_ T U (simples C j)).inv)
          ((α_ T U (simples C j)).hom ≫ (T ◁ crossingProjection C U k j b) ≫
            crossingProjection C T i k a) ≫ ((T ⊗ U) ◁ biproduct.ι V j) := by
  classical
  let V := inductionSummand C X
  let bT : (⨁ V) ⊗ T ⟶ T ⊗ (⨁ V) := crossingCandidate C X T
  let bU : (⨁ V) ⊗ U ⟶ U ⊗ (⨁ V) := crossingCandidate C X U
  change (biproduct.ι V i ▷ (T ⊗ U)) ≫ crossingTensorComposite C X T U = _
  calc
    _ = 𝟙 _ ⊗≫ (((biproduct.ι V i ▷ T) ≫ bT) ▷ U) ⊗≫
      (T ◁ bU) ⊗≫ 𝟙 ((T ⊗ U) ⊗ (⨁ V)) := by
      change (biproduct.ι V i ▷ (T ⊗ U)) ≫
        ((α_ (⨁ V) T U).inv ≫ (bT ▷ U) ≫ (α_ T (⨁ V) U).hom ≫
          (T ◁ bU) ≫ (α_ T U (⨁ V)).inv) = _
      monoidal
    _ = ∑ k, ∑ a : crossingIndex C T i k,
      𝟙 _ ⊗≫ (crossingBlock X T (simples C i) (simples C k)
          (crossingInclusion C T i k a) (crossingProjection C T i k a) ▷ U) ⊗≫
        (T ◁ ((biproduct.ι V k ▷ U) ≫ bU)) ⊗≫ 𝟙 ((T ⊗ U) ⊗ (⨁ V)) := by
      dsimp only [bT]
      rw [crossingCandidate_on_summand]
      simp only [monoidalComp, sum_whiskerRight, Preadditive.sum_comp, Preadditive.comp_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      simp only [comp_whiskerRight, whiskerLeft_comp]
      monoidal
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [bU]
      rw [crossingCandidate_on_summand]
      simp only [whiskerLeft_sum, monoidalComp, Preadditive.comp_sum, Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro b _
      rw [crossingBlock_tensor]
      simp only [whiskerLeft_comp]
      monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The induction crossing obeys the half-braiding tensor law. -/
theorem crossingCandidate_tensor (X T U : C.Obj) :
    crossingCandidate C X (T ⊗ U) = crossingTensorComposite C X T U := by
  classical
  let V := inductionSummand C X
  apply (cancel_epi (rightDistributor V (T ⊗ U)).inv).1
  apply biproduct.hom_ext'
  intro i
  simp only [biproduct_ι_comp_rightDistributor_inv_assoc]
  rw [crossingCandidate_on_summand, crossingComposite_summand]
  simp only [← Preadditive.sum_comp]
  simp_rw [← crossingBlock_refinement C X T U i]
  simp only [Fintype.sum_sigma, Preadditive.sum_comp]
  dsimp only [underlying, V] at *
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  conv_lhs =>
    enter [2, j]
    rw [Finset.sum_comm (s := (Finset.univ : Finset (crossingIndex C U k j)))
      (t := (Finset.univ : Finset (crossingIndex C T i k)))]
  rw [Finset.sum_comm]



/-- The actual matrix crossing is invertible by rigidity. -/
theorem crossingCandidate_isIso (X T : C.Obj) :
    IsIso (crossingCandidate C X T) :=
  weak_isIso (crossingCandidate C X)
    (fun f => crossingCandidate_natural_test C X f)
    (fun T U => crossingCandidate_tensor C X T U)
    (crossingCandidate_unit C X) T (ᘁT)

/-- The explicit matrix crossings form an actual half-braiding on the
induction sum, with no additional coherence assumptions. -/
def halfBraidingOfCrossingCandidate (X : C.Obj) :
    HalfBraiding (underlying C X) where
  β T := by letI := crossingCandidate_isIso C X T; exact asIso (crossingCandidate C X T)
  monoidal T U := crossingCandidate_tensor C X T U
  naturality f := crossingCandidate_natural_test C X f

/-- The actual induction functor to Mathlib's Drinfeld centre. -/
def induction : C.Obj ⥤ CategoryTheory.Center C.Obj where
  obj X := ⟨underlying C X, halfBraidingOfCrossingCandidate C X⟩
  map f := ⟨(underlyingFunctor C).map f, crossingCandidate_natural_middle C f⟩
  map_id X := by
    apply CategoryTheory.Center.ext
    change (underlyingFunctor C).map (𝟙 X) = 𝟙 ((underlyingFunctor C).obj X)
    exact (underlyingFunctor C).map_id X
  map_comp f g := by
    apply CategoryTheory.Center.ext
    change (underlyingFunctor C).map (f ≫ g) =
      (underlyingFunctor C).map f ≫ (underlyingFunctor C).map g
    exact (underlyingFunctor C).map_comp f g


end PropertyF.Ground.CentreInduction
