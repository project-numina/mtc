module
public import PropertyF.Ground.CentreInduction.CrossingCoherence
public import PropertyF.Ground.CentreInduction.AdjunctionAssembly

open PropertyF.Ground.Dimensions

/-! Duality identities for the induction counit and triangle. -/
/-! Matrix reductions for the induction adjunction. -/
section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
-- The chosen simple representatives of the base fusion category.
local notation "S" => simples C
-- The induction crossing on the object X.
local notation "b" => crossingCandidate C X
-- Its simple-indexed summands.
local notation "V" => inductionSummand C X
variable (T : C.Obj) (i j : Fin (rank C))

set_option backward.isDefEq.respectTransparency false in
/-- Composing a crossing with the unit-summand counit selects one matrix column. -/
theorem crossing_counit_matrix :
  (biproduct.ι V i ▷ T) ≫ b T ≫ (T ◁ (underlyingCounit C).app X) =
    (∑ a, crossingSummand C X T i (unitIndex C) a) ≫ (T ◁ (unitSummandIso C X).hom) := by
  simpa only [underlyingCounit, unitSummandRetract, whiskerLeft_comp, Category.assoc] using
    congrArg (· ≫ (T ◁ (unitSummandIso C X).hom)) (crossingCandidate_matrix C X T i (unitIndex C))

/-! The unit-column matrix of the induction crossing. -/

/-- Tensoring a simple by the chosen unit representative changes it by an isomorphism. -/
def simpleTensorUnitIso : S j ⊗ S (unitIndex C) ≅ S j :=
  let e : S (unitIndex C) ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  whiskerLeftIso (S j) e ≪≫ ρ_ (S j)

set_option backward.isDefEq.respectTransparency false in
/-- The counit crossing column has only diagonal simple summands. -/
theorem counit_column_finrank :
    Module.finrank ℂ (S i ⟶ S j ⊗ S (unitIndex C)) = if i = j then 1 else 0 :=
  (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (simpleTensorUnitIso C j)).finrank_eq.trans
    (finrank_simples_hom C i j)

set_option backward.isDefEq.respectTransparency false in
/-- Off-diagonal counit crossing entries vanish. -/
theorem crossing_counit_offdiag {i j : Fin (rank C)} (hne : i ≠ j) :
  (biproduct.ι V i ▷ S j) ≫ b (S j) ≫
    (S j ◁ (underlyingCounit C).app X) = 0 :=
  letI : IsEmpty (crossingIndex C (S j) i (unitIndex C)) := by
    simpa only [crossingIndex, counit_column_finrank, hne, ↓reduceIte] using (inferInstance : IsEmpty (Fin 0))
  by simp only [crossing_counit_matrix, Fintype.sum_empty, zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal entry is the canonical unit isomorphism block. -/
theorem crossing_counit_diagonal :
  (biproduct.ι V i ▷ S i) ≫ b (S i) ≫
    (S i ◁ (underlyingCounit C).app X) =
      crossingBlock X (S i) (S (unitIndex C))
        (simpleTensorUnitIso C i).inv (simpleTensorUnitIso C i).hom ≫
          (S i ◁ (unitSummandIso C X).hom) := by
  let : Unique (crossingIndex C (S i) i (unitIndex C)) := by
    simpa only [crossingIndex, counit_column_finrank, ↓reduceIte] using
      (inferInstance : Unique (Fin 1))
  let : Simple (S i) := simples_simple C i
  let : FiniteDimensional ℂ (S i ⟶ S i) := IsFusionCategory.hom_finite _ _
  simpa only [crossing_counit_matrix, Fintype.sum_unique, crossingSummand,
    Iso.symm_hom, Iso.symm_inv] using
    congrArg (· ≫ (S i ◁ (unitSummandIso C X).hom))
      (crossingBlock_of_simple_split (k := ℂ) X (simpleTensorUnitIso C i).symm _ _
        (crossingInclusion_projection default))

end PropertyF.Ground.CentreInduction

end
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.ExactPairing
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable {A : D}

set_option backward.isDefEq.respectTransparency false in
/-- The unit component followed by a map can be expressed through a crossing. -/
theorem unitComponent_reduce {M N X S : D} [HasRightDual S] (b : N ⊗ S ⟶ S ⊗ N) (t : M ⟶ N) (w : N ⟶ X) :
    t ≫ ((ρ_ N).inv ≫ (N ◁ η_ S (Sᘁ)) ≫ (α_ N S (Sᘁ)).inv ≫ (b ▷ Sᘁ)) ≫
      ((S ◁ w) ▷ Sᘁ) =
    𝟙 _ ⊗≫ (M ◁ η_ S (Sᘁ)) ⊗≫ ((t ▷ S ≫ b ≫ (S ◁ w)) ▷ Sᘁ) ⊗≫ 𝟙 _ := by
  simp only [monoidalComp, Category.assoc, rightUnitor_inv_naturality_assoc,
    ← whisker_exchange_assoc]
  monoidal

variable (X T : D)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Closing the right unit isomorphism gives ordinary evaluation. -/
theorem close_rightUnit_eval [HasRightDual A] [HasRightDual T] (e : A ≅ 𝟙_ D) :
    closeFusionMap T A ((T ◁ e.hom) ≫ (ρ_ T).hom) ≫
      (rightDualIsoMap e.symm).hom = ε_ T (Tᘁ) := by
  let d : Aᘁ ⟶ 𝟙_ D := (rightDualIsoMap e.symm).hom
  let z := closeFusionMap T A ((T ◁ e.hom) ≫ (ρ_ T).hom)
  have h := closeFusionMap_evaluation ((T ◁ e.hom) ≫ (ρ_ T).hom)
  simp only [← evaluation_iso_map e, tensorHom_def', monoidalComp, whiskerLeft_comp,
    Category.assoc, whisker_exchange_assoc, ← comp_whiskerRight_assoc] at h
  change (z ≫ d) ▷ A ≫ (𝟙_ D ◁ e.hom) ≫ (ρ_ (𝟙_ D)).hom = _ at h
  change z ≫ d = ε_ T (Tᘁ)
  apply (cancel_epi ((((Tᘁ : D) ⊗ T) ◁ e.hom) ≫ (ρ_ (Tᘁ ⊗ T)).hom)).1
  calc
    _ = ((z ≫ d) ▷ A) ≫ ((𝟙_ D) ◁ e.hom) ≫ (ρ_ (𝟙_ D)).hom := by
      simp only [Category.assoc, ← rightUnitor_naturality, ← whisker_exchange_assoc,
        comp_whiskerRight]
    _ = _ := by
      rw [h]
      monoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical unit-column crossing block contracts by evaluation. -/
theorem crossingUnitBlock_eval [HasRightDual A] [HasRightDual T] (e : A ≅ 𝟙_ D) :
  let te : T ⊗ A ≅ T := whiskerLeftIso T e ≪≫ ρ_ T
  crossingBlock X T A te.inv te.hom ≫ (T ◁ (unitTensorIso e X).hom) =
    𝟙 _ ⊗≫ ((T ⊗ X) ◁ ε_ T (Tᘁ)) ⊗≫ 𝟙 _ := by
  dsimp only [unitTensorIso]
  set δ : Aᘁ ≅ 𝟙_ D := rightDualIsoMap e.symm
  have hq : closeFusionMap T A ((T ◁ e.hom) ≫ (ρ_ T).hom) ≫ δ.hom = ε_ T (Tᘁ) :=
    close_rightUnit_eval T e
  clear_value δ
  simp only [crossingBlock, mixedCrossing, Iso.trans_hom, Iso.trans_inv, whiskerLeftIso_hom,
    whiskerLeftIso_inv, tensorIso_hom, Iso.refl_hom, tensorHom_def, whiskerLeft_id,
    Category.comp_id]
  set d : Aᘁ ⟶ 𝟙_ D := δ.hom
  set q : Tᘁ ⊗ T ⟶ Aᘁ := closeFusionMap T A ((T ◁ e.hom) ≫ (ρ_ T).hom)
  set f : A ⟶ 𝟙_ D := e.hom
  set g : 𝟙_ D ⟶ A := e.inv
  clear_value d q
  calc
    _ = 𝟙 _ ⊗≫ ((((ρ_ T).inv ≫ T ◁ g) ▷ X) ▷ ((Tᘁ : D) ⊗ T)) ⊗≫
      (((((T ⊗ A) ⊗ X) ◁ q) ≫ (((T ◁ f) ▷ X) ▷ Aᘁ))) ⊗≫
      (((T ⊗ (𝟙_ D)) ⊗ X) ◁ d) ⊗≫ 𝟙 _ := by
        monoidal
    _ = 𝟙 _ ⊗≫ ((((ρ_ T).inv ≫ (T ◁ (g ≫ f))) ▷ X) ▷ ((Tᘁ : D) ⊗ T)) ⊗≫
      (((T ⊗ (𝟙_ D)) ⊗ X) ◁ (q ≫ d)) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
        simp [monoidalComp, Category.assoc, whiskerLeft_comp, comp_whiskerRight]
    _ = _ := by rw [hq, e.inv_hom_id]; simp; monoidal

end PropertyF.Ground.CentreInduction

end
end

/-! The second induction triangle for the actual centre crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.ExactPairing
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
-- The chosen simple representatives of the base fusion category.
local notation "S" => simples C
-- The induction crossing on the object X.
local notation "b" => crossingCandidate C X
-- Unit components of the induced object.
local notation "u" => unitComponent C (Functor.obj (induction C) X)
-- Its simple-indexed summands.
local notation "V" => inductionSummand C X
variable (i j : Fin (rank C))

set_option backward.isDefEq.respectTransparency false in
/-- A unit component reduces to the corresponding counit-crossing matrix entry. -/
theorem unit_matrix_reduce :
  biproduct.ι V i ≫ u j ≫
    ((S j ◁ (underlyingCounit C).app X) ▷ (S j)ᘁ) =
  𝟙 _ ⊗≫ ((V i) ◁ η_ (S j) ((S j)ᘁ)) ⊗≫
    (((biproduct.ι V i ▷ (S j)) ≫ b (S j) ≫
      ((S j) ◁ (underlyingCounit C).app X)) ▷ (S j)ᘁ) ⊗≫ 𝟙 _ := by
  simpa [unitComponent, unitComponentAt, induction, halfBraidingOfCrossingCandidate,
    underlying, underlyingFunctor, inductionSummand, monoidalComp, Category.assoc] using
    unitComponent_reduce (b (S j)) (biproduct.ι _ i) ((underlyingCounit C).app X)

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal components of the second triangle are identities. -/
theorem unit_diag :
  biproduct.ι V i ≫ u i ≫
    ((S i ◁ (underlyingCounit C).app X) ▷ (S i)ᘁ) = 𝟙 (V i) := by
  simp only [unit_matrix_reduce, crossing_counit_diagonal C X i]
  erw [crossingUnitBlock_eval X (S i) (Classical.choice (unitIndex_iso C))]
  dsimp only [Functor.id_obj]
  convert congrArg (fun (t : (S i)ᘁ ⊗ 𝟙_ C.Obj ⟶ 𝟙_ C.Obj ⊗ (S i)ᘁ) =>
    𝟙 (V i) ⊗≫ ((S i ⊗ X) ◁ t) ⊗≫ 𝟙 (V i))
    (coevaluation_evaluation'' (S i) ((S i)ᘁ)) using 1 <;> monoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every matrix entry of the second triangle has the expected value. -/
theorem secondTriangle_entry :
  biproduct.ι V i ≫ (unitCandidate C ((induction C).obj X) ≫
    (underlyingFunctor C).map ((underlyingCounit C).app X)) ≫ biproduct.π V j =
      biproduct.ι V i ≫ biproduct.π V j := by
  dsimp [unitCandidate, underlyingFunctor, induction, underlying]
  simp only [Category.assoc, biproduct.map_π, biproduct.lift_π_assoc]
  by_cases h : i = j
  · subst j
    simpa [Category.assoc, induction, underlyingFunctor, underlying] using unit_diag C X i
  · simpa [monoidalComp, crossing_counit_offdiag C X h, biproduct.ι_π_ne _ h,
      induction, underlying, underlyingFunctor] using unit_matrix_reduce C X i j


end PropertyF.Ground.CentreInduction
