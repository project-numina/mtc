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
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- Composing a crossing with the unit-summand counit selects one matrix column. -/
theorem crossing_counit_matrix (X T : C.Obj) (i : Fin (rank C)) :
  let V := inductionSummand C X
  (biproduct.ι V i ▷ T) ≫ crossingCandidate C X T ≫ (T ◁ (underlyingCounit C).app X) =
    (∑ a, crossingSummand C X T i (unitIndex C) a) ≫ (T ◁ (unitSummandIso C X).hom) := by
  simpa only [underlyingCounit, unitSummandRetract, whiskerLeft_comp, Category.assoc] using
    congrArg (fun k => k ≫ (T ◁ (unitSummandIso C X).hom))
      (crossingCandidate_matrix C X T i (unitIndex C))

end PropertyF.Ground.CentreInduction

end
end

section
/-! The unit-column matrix of the induction crossing. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

/-- Tensoring a simple by the chosen unit representative changes it by an isomorphism. -/
def simpleTensorUnitIso (j : Fin (rank C)) : simples C j ⊗ simples C (unitIndex C) ≅ simples C j :=
  let e : simples C (unitIndex C) ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  whiskerLeftIso (simples C j) e ≪≫ ρ_ (simples C j)

set_option backward.isDefEq.respectTransparency false in
/-- The counit crossing column has only diagonal simple summands. -/
theorem counit_column_finrank (i j : Fin (rank C)) :
    Module.finrank ℂ (simples C i ⟶ simples C j ⊗ simples C (unitIndex C)) = if i = j then 1 else 0 :=
  (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (simpleTensorUnitIso C j)).finrank_eq.trans
    (finrank_simples_hom C i j)

variable (X : C.Obj)

set_option backward.isDefEq.respectTransparency false in
/-- Off-diagonal counit crossing entries vanish. -/
theorem crossing_counit_offdiag {i j : Fin (rank C)} (hne : i ≠ j) :
  let V := inductionSummand C X
  (biproduct.ι V i ▷ simples C j) ≫ crossingCandidate C X (simples C j) ≫
    (simples C j ◁ (underlyingCounit C).app X) = 0 := by
  let : IsEmpty (crossingIndex C (simples C j) i (unitIndex C)) := by
    simpa only [crossingIndex, counit_column_finrank, hne, ↓reduceIte] using (inferInstance : IsEmpty (Fin 0))
  simpa only [Fintype.sum_empty, zero_comp] using crossing_counit_matrix C X (simples C j) i

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal entry is the canonical unit isomorphism block. -/
theorem crossing_counit_diagonal (i : Fin (rank C)) :
  let V := inductionSummand C X
  (biproduct.ι V i ▷ simples C i) ≫ crossingCandidate C X (simples C i) ≫
    (simples C i ◁ (underlyingCounit C).app X) =
      crossingBlock X (simples C i) (simples C (unitIndex C))
        (simpleTensorUnitIso C i).inv (simpleTensorUnitIso C i).hom ≫
          (simples C i ◁ (unitSummandIso C X).hom) := by
  let : Unique (crossingIndex C (simples C i) i (unitIndex C)) := by
    simpa only [crossingIndex, counit_column_finrank, ↓reduceIte] using
      (inferInstance : Unique (Fin 1))
  dsimp only
  rw [crossing_counit_matrix C X (simples C i) i, Fintype.sum_unique]
  dsimp only [crossingSummand]
  let : Simple (simples C i) := simples_simple C i
  let : FiniteDimensional ℂ (simples C i ⟶ simples C i) := IsFusionCategory.hom_finite _ _
  rw [crossingBlock_of_simple_split X (simpleTensorUnitIso C i).symm _ _
    (crossingInclusion_projection default)]
  rfl

end PropertyF.Ground.CentreInduction

end
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.ExactPairing
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
variable {A : D}

set_option backward.isDefEq.respectTransparency false in
/-- The unit component followed by a map can be expressed through a crossing. -/
theorem unitComponent_reduce {M N X S : D} (b : N ⊗ S ⟶ S ⊗ N) (t : M ⟶ N) (w : N ⟶ X) :
    t ≫ ((ρ_ N).inv ≫ (N ◁ η_ S (Sᘁ)) ≫ (α_ N S (Sᘁ)).inv ≫ (b ▷ Sᘁ)) ≫
      ((S ◁ w) ▷ Sᘁ) =
    𝟙 _ ⊗≫ (M ◁ η_ S (Sᘁ)) ⊗≫ ((t ▷ S ≫ b ≫ (S ◁ w)) ▷ Sᘁ) ⊗≫ 𝟙 _ := by
  calc
    _ = 𝟙 _ ⊗≫ ((t ▷ (𝟙_ D)) ≫ (N ◁ η_ S (Sᘁ))) ⊗≫
      (b ▷ Sᘁ) ⊗≫ ((S ◁ w) ▷ Sᘁ) ⊗≫ 𝟙 _ := by monoidal
    _ = _ := by
      rw [← whisker_exchange]
      monoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluation is normalized along an isomorphism with the tensor unit. -/
theorem evaluation_iso_unit (e : A ≅ 𝟙_ D) :
    ((rightDualIsoMap e.symm ≪≫ rightDualUnitIso).hom ⊗ₘ e.hom) ≫
      (ρ_ (𝟙_ D)).hom = ε_ A (Aᘁ) := by
  let : HasRightDual (𝟙_ D) := RightRigidCategory.rightDual (𝟙_ D)
  simp only [Iso.trans_hom, rightDualIsoMap, Iso.symm_hom,
    tensorHom_def', comp_whiskerRight, Category.assoc]
  rw [show rightDualUnitIso.hom ▷ (𝟙_ D) ≫ (ρ_ (𝟙_ D)).hom =
    ε_ (𝟙_ D) ((𝟙_ D)ᘁ) from rightDualIso_evaluation HasRightDual.exact exactPairingUnit,
    rightAdjointMate_comp_evaluation, ← whiskerLeft_comp_assoc, Iso.hom_inv_id,
    whiskerLeft_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Closing the right unit isomorphism gives ordinary evaluation. -/
theorem close_rightUnit_eval (T : D) (e : A ≅ 𝟙_ D) :
    closeFusionMap T A ((T ◁ e.hom) ≫ (ρ_ T).hom) ≫
      (rightDualIsoMap e.symm ≪≫ rightDualUnitIso).hom = ε_ T (Tᘁ) := by
  let d := (rightDualIsoMap e.symm ≪≫ rightDualUnitIso).hom
  let z := closeFusionMap T A ((T ◁ e.hom) ≫ (ρ_ T).hom)
  have h := closeFusionMap_evaluation ((T ◁ e.hom) ≫ (ρ_ T).hom)
  rw [← evaluation_iso_unit e] at h
  simp only [tensorHom_def', monoidalComp, whiskerLeft_comp, Category.assoc] at h
  rw [whisker_exchange_assoc, ← comp_whiskerRight_assoc] at h
  change z ≫ d = ε_ T (Tᘁ)
  apply (cancel_epi ((((Tᘁ : D) ⊗ T) ◁ e.hom) ≫ (ρ_ (Tᘁ ⊗ T)).hom)).1
  calc
    _ = ((z ≫ d) ▷ A) ≫ ((𝟙_ D) ◁ e.hom) ≫ (ρ_ (𝟙_ D)).hom := by
      simp only [Category.assoc]
      rw [← Category.assoc (ρ_ (Tᘁ ⊗ T)).hom z d, ← rightUnitor_naturality,
        ← whisker_exchange_assoc]
      simp only [Category.assoc, ← rightUnitor_naturality, comp_whiskerRight]
    _ = _ := by
      rw [h]
      monoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical unit-column crossing block contracts by evaluation. -/
theorem crossingUnitBlock_eval (X T : D) (e : A ≅ 𝟙_ D) :
  let d : Aᘁ ≅ 𝟙_ D := rightDualIsoMap e.symm ≪≫ rightDualUnitIso
  let us : (A ⊗ X) ⊗ Aᘁ ≅ X := ((e ⊗ᵢ Iso.refl X) ⊗ᵢ d) ≪≫
    ((λ_ X) ⊗ᵢ Iso.refl (𝟙_ D)) ≪≫ ρ_ X
  let te : T ⊗ A ≅ T := whiskerLeftIso T e ≪≫ ρ_ T
  crossingBlock X T A te.inv te.hom ≫ (T ◁ us.hom) =
    𝟙 _ ⊗≫ ((T ⊗ X) ◁ ε_ T (Tᘁ)) ⊗≫ 𝟙 _ := by
  dsimp only
  set δ : Aᘁ ≅ 𝟙_ D := rightDualIsoMap e.symm ≪≫ rightDualUnitIso
  have hq : closeFusionMap T A ((T ◁ e.hom) ≫ (ρ_ T).hom) ≫ δ.hom = ε_ T (Tᘁ) :=
    close_rightUnit_eval T e
  clear_value δ
  simp only [crossingBlock, Iso.trans_hom, Iso.trans_inv, whiskerLeftIso_hom,
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
    _ = 𝟙 _ ⊗≫ ((((ρ_ T).inv ≫ T ◁ g) ▷ X) ▷ ((Tᘁ : D) ⊗ T)) ⊗≫
      (((((T ◁ f) ▷ X) ▷ ((Tᘁ : D) ⊗ T)) ≫
        (((T ⊗ (𝟙_ D)) ⊗ X) ◁ q))) ⊗≫
      (((T ⊗ (𝟙_ D)) ⊗ X) ◁ d) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ ((((ρ_ T).inv ≫ (T ◁ (g ≫ f))) ▷ X) ▷ ((Tᘁ : D) ⊗ T)) ⊗≫
      (((T ⊗ (𝟙_ D)) ⊗ X) ◁ (q ≫ d)) ⊗≫ 𝟙 _ := by
        simp only [whiskerLeft_comp, comp_whiskerRight]
        simp [monoidalComp, Category.assoc]
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

set_option backward.isDefEq.respectTransparency false in
/-- A unit component reduces to the corresponding counit-crossing matrix entry. -/
theorem unit_matrix_reduce (i j : Fin (rank C)) :
  let V := inductionSummand C X
  biproduct.ι V i ≫ unitComponent C ((induction C).obj X) j ≫
    ((simples C j ◁ (underlyingCounit C).app X) ▷ (simples C j)ᘁ) =
  𝟙 _ ⊗≫ ((V i) ◁ η_ (simples C j) ((simples C j)ᘁ)) ⊗≫
    (((biproduct.ι V i ▷ (simples C j)) ≫ crossingCandidate C X (simples C j) ≫
      ((simples C j) ◁ (underlyingCounit C).app X)) ▷ (simples C j)ᘁ) ⊗≫ 𝟙 _ := by
  simpa [unitComponent, unitComponentAt, induction, halfBraidingOfCrossingCandidate,
    underlying, underlyingFunctor, inductionSummand, monoidalComp, Category.assoc] using
    unitComponent_reduce (crossingCandidate C X (simples C j)) (biproduct.ι (inductionSummand C X) i)
      ((underlyingCounit C).app X)

set_option backward.isDefEq.respectTransparency false in
/-- The off-diagonal components of the second triangle vanish. -/
theorem unit_offdiag {i j : Fin (rank C)} (hne : i ≠ j) :
  let V := inductionSummand C X
  biproduct.ι V i ≫ unitComponent C ((induction C).obj X) j ≫
    ((simples C j ◁ (underlyingCounit C).app X) ▷ (simples C j)ᘁ) = 0 := by
  dsimp only
  rw [unit_matrix_reduce, crossing_counit_offdiag C X hne]
  simp [monoidalComp]

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal components of the second triangle are identities. -/
theorem unit_diag (i : Fin (rank C)) :
  let V := inductionSummand C X
  biproduct.ι V i ≫ unitComponent C ((induction C).obj X) i ≫
    ((simples C i ◁ (underlyingCounit C).app X) ▷ (simples C i)ᘁ) = 𝟙 (V i) := by
  have h := unit_matrix_reduce C X i i
  dsimp only at h
  rw [crossing_counit_diagonal C X i] at h
  let e : simples C (unitIndex C) ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  rw [show crossingBlock X (simples C i) (simples C (unitIndex C))
      (simpleTensorUnitIso C i).inv (simpleTensorUnitIso C i).hom ≫
        (simples C i ◁ (unitSummandIso C X).hom) = _ from
      crossingUnitBlock_eval X (simples C i) e] at h
  dsimp only [Functor.id_obj] at h ⊢
  apply h.trans
  calc
    _ = 𝟙 _ ⊗≫ ((simples C i ⊗ X) ◁ (((simples C i)ᘁ ◁ η_ (simples C i) ((simples C i)ᘁ)) ⊗≫
      (ε_ (simples C i) ((simples C i)ᘁ) ▷ (simples C i)ᘁ))) ⊗≫ 𝟙 _ := by monoidal
    _ = _ := by rw [coevaluation_evaluation'']; monoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every matrix entry of the second triangle has the expected value. -/
theorem secondTriangle_entry (i j : Fin (rank C)) : let V := inductionSummand C X
  biproduct.ι V i ≫ (unitCandidate C ((induction C).obj X) ≫
    (underlyingFunctor C).map ((underlyingCounit C).app X)) ≫ biproduct.π V j =
      biproduct.ι V i ≫ biproduct.π V j := by
  dsimp [unitCandidate, underlyingFunctor, induction, underlying]
  simp only [Category.assoc, biproduct.map_π, biproduct.lift_π_assoc]
  by_cases h : i = j
  · subst j
    simpa [Category.assoc, induction, underlyingFunctor, underlying] using unit_diag C X i
  · rw [biproduct.ι_π_ne _ h]
    exact unit_offdiag C X h


end PropertyF.Ground.CentreInduction
