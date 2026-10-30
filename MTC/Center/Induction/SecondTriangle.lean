module
public import MTC.Center.Induction.CrossingCoherence
public import MTC.Center.Induction.AdjunctionAssembly

open MTC.Dimensions

/-! Duality identities for the induction counit and triangle. -/
/-! Matrix reductions for the induction adjunction. -/
section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace MTC.Center.Induction
attribute [local instance] IsFusionCategory.hom_finite
variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
-- The chosen simple representatives of the base fusion category.
local notation "S" => simples C
local instance (i : Fin (rank C)) : Simple (S i) := simples_simple C i
-- The induction crossing on the object X.
local notation "b" => crossingCandidate X
-- Its simple-indexed summands.
local notation "V" => inductionSummand X
variable (T : C.Obj) (i j : Fin (rank C))

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- Composing a crossing with the unit-summand counit selects one matrix column. -/
theorem crossing_counit_matrix :
  (biproduct.ι V i ▷ T) ≫ b T ≫ (T ◁ (underlyingCounit C).app X) =
    (∑ a, crossingSummand X T i (unitIndex C) a) ≫ (T ◁ (unitSummandIso X).hom) := by
  simpa [underlyingCounit, unitSummandRetract] using
    congrArg (· ≫ (T ◁ (unitSummandIso X).hom)) (crossingCandidate_matrix X T i (unitIndex C))

/-! The unit-column matrix of the induction crossing. -/

/-- Tensoring a simple by the chosen unit representative changes it by an isomorphism. -/
def simpleTensorUnitIso : S j ⊗ S (unitIndex C) ≅ S j :=
  let e : S (unitIndex C) ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  whiskerLeftIso (S j) e ≪≫ ρ_ (S j)

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- Off-diagonal counit crossing entries vanish. -/
theorem crossing_counit_offdiag {i j : Fin (rank C)} (hne : i ≠ j) :
  (biproduct.ι V i ▷ S j) ≫ b (S j) ≫
    (S j ◁ (underlyingCounit C).app X) = 0 :=
  by
    rw [crossing_counit_matrix]
    simp [crossingIndex, finrank_hom_simple_of_iso i j (simpleTensorUnitIso C j), hne]

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The diagonal entry is the canonical unit isomorphism block. -/
theorem crossing_counit_diagonal :
  (biproduct.ι V i ▷ S i) ≫ b (S i) ≫
    (S i ◁ (underlyingCounit C).app X) =
      crossingBlock X (S i) (S (unitIndex C))
        (simpleTensorUnitIso C i).inv (simpleTensorUnitIso C i).hom ≫
          (S i ◁ (unitSummandIso X).hom) := by
  let : Unique (crossingIndex (S i) i (unitIndex C)) := by
    simpa [crossingIndex, finrank_hom_simple_of_iso i i (simpleTensorUnitIso C i)] using
      (inferInstance : Unique (Fin 1))
  simpa only [crossing_counit_matrix, Fintype.sum_unique, crossingSummand,
    crossingInclusion, crossingProjection, Iso.symm_hom, Iso.symm_inv] using
    congrArg (· ≫ (S i ◁ (unitSummandIso X).hom))
      (crossingBlock_of_simple_split (k := ℂ) X (simpleTensorUnitIso C i).symm _ _
        (simpleInclusion_projection default))

end MTC.Center.Induction

end
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.ExactPairing
universe v u
@[expose] public noncomputable section
namespace MTC.Center.Induction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
variable {A : D}

variable (X T : D) [HasRightDual A] [HasRightDual T]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Closing the right unit isomorphism gives ordinary evaluation. -/
theorem close_rightUnit_eval (e : A ≅ 𝟙_ D) :
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
  convert h using 1
  · rw [Category.assoc, ← rightUnitor_naturality, ← whisker_exchange_assoc, comp_whiskerRight]
  · monoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A split unit factor contracts a crossing whenever its closed map is evaluation. -/
theorem crossingBlock_unit_of_split (f : A ⟶ 𝟙_ D) (g : 𝟙_ D ⟶ A) (d : Aᘁ ⟶ 𝟙_ D)
    (hfg : g ≫ f = 𝟙 (𝟙_ D))
    (hq : closeFusionMap T A ((T ◁ f) ≫ (ρ_ T).hom) ≫ d = ε_ T (Tᘁ)) :
    crossingBlock X T A ((ρ_ T).inv ≫ (T ◁ g)) ((T ◁ f) ≫ (ρ_ T).hom) ≫
        (T ◁ unitTensorHom f d X) =
      𝟙 _ ⊗≫ ((T ⊗ X) ◁ ε_ T (Tᘁ)) ⊗≫ 𝟙 _ := by
  simp only [crossingBlock, mixedCrossing, unitTensorHom, tensorHom_def,
    whiskerLeft_id, Category.comp_id]
  set q : Tᘁ ⊗ T ⟶ Aᘁ := closeFusionMap T A ((T ◁ f) ≫ (ρ_ T).hom)
  change q ≫ d = _ at hq
  clear_value q
  calc
    _ = 𝟙 _ ⊗≫ ((((ρ_ T).inv ≫ T ◁ g) ▷ X) ▷ ((Tᘁ : D) ⊗ T)) ⊗≫
      (((((T ⊗ A) ⊗ X) ◁ q) ≫ (((T ◁ f) ▷ X) ▷ Aᘁ))) ⊗≫
      (((T ⊗ (𝟙_ D)) ⊗ X) ◁ d) ⊗≫ 𝟙 _ := by
        monoidal
    _ = 𝟙 _ ⊗≫ ((((ρ_ T).inv ≫ (T ◁ (g ≫ f))) ▷ X) ▷ ((Tᘁ : D) ⊗ T)) ⊗≫
      (((T ⊗ (𝟙_ D)) ⊗ X) ◁ (q ≫ d)) ⊗≫ 𝟙 _ := by
        rw [whisker_exchange]
        simp [monoidalComp, Category.assoc, whiskerLeft_comp, comp_whiskerRight]
    _ = _ := by rw [hq, hfg]; simp; monoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical unit-column crossing block contracts by evaluation. -/
theorem crossingUnitBlock_eval (e : A ≅ 𝟙_ D) :
  let te : T ⊗ A ≅ T := whiskerLeftIso T e ≪≫ ρ_ T
  crossingBlock X T A te.inv te.hom ≫ (T ◁ (unitTensorIso e X).hom) =
    𝟙 _ ⊗≫ ((T ⊗ X) ◁ ε_ T (Tᘁ)) ⊗≫ 𝟙 _ :=
  crossingBlock_unit_of_split X T e.hom e.inv
    (rightDualIsoMap e.symm).hom e.inv_hom_id (close_rightUnit_eval T e)

end MTC.Center.Induction

end
end

/-! The second induction triangle for the actual centre crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.ExactPairing
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace MTC.Center.Induction
variable {C : BraidedFusionCategory.{v,u}} (X : C.Obj)
-- The chosen simple representatives of the base fusion category.
local notation "S" => simples C
-- The induction crossing on the object X.
local notation "b" => crossingCandidate X
-- Unit components of the induced object.
local notation "u" => unitComponent (Functor.obj (induction C) X)
-- Its simple-indexed summands.
local notation "V" => inductionSummand X
variable (i j : Fin (rank C))

set_option backward.isDefEq.respectTransparency false in
/-- A unit component reduces to the corresponding counit-crossing matrix entry. -/
theorem unit_matrix_reduce :
  biproduct.ι V i ≫ u j ≫
    ((S j ◁ (underlyingCounit C).app X) ▷ (S j)ᘁ) =
  𝟙 _ ⊗≫ ((V i) ◁ η_ (S j) ((S j)ᘁ)) ⊗≫
    (((biproduct.ι V i ▷ (S j)) ≫ b (S j) ≫
      ((S j) ◁ (underlyingCounit C).app X)) ▷ (S j)ᘁ) ⊗≫ 𝟙 _ := by
  simp [unitComponent, unitComponentAt, induction, halfBraidingOfCrossingCandidate,
    underlying, underlyingFunctor, monoidalComp,
    rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, -whiskerRight_id]

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal components of the second triangle are identities. -/
theorem unit_diag :
  biproduct.ι V i ≫ u i ≫
    ((S i ◁ (underlyingCounit C).app X) ▷ (S i)ᘁ) = 𝟙 (V i) := by
  simp only [unit_matrix_reduce, crossing_counit_diagonal X i, simpleTensorUnitIso, unitSummandIso,
    crossingUnitBlock_eval X (S i) (Classical.choice (unitIndex_iso C)), Functor.id_obj]
  convert congrArg (fun (t : (S i)ᘁ ⊗ 𝟙_ C.Obj ⟶ 𝟙_ C.Obj ⊗ (S i)ᘁ) =>
    𝟙 (V i) ⊗≫ ((S i ⊗ X) ◁ t) ⊗≫ 𝟙 (V i))
    (coevaluation_evaluation'' (S i) ((S i)ᘁ)) using 1 <;> monoidal


end MTC.Center.Induction
