module
public import PropertyF.Ground.CentreInduction.CounitColumn

/-! Duality identities for the induction counit and triangle. -/
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.ExactPairing
universe v u
@[expose] public noncomputable section
namespace PropertyF.Ground.CentreInduction
variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- The unit component followed by a map can be expressed through a crossing. -/
theorem unitComponent_reduce (M N X S : C.Obj) (b : N ⊗ S ⟶ S ⊗ N)
    (t : M ⟶ N) (w : N ⟶ X) :
    t ≫ ((ρ_ N).inv ≫ (N ◁ η_ S (Sᘁ)) ≫ (α_ N S (Sᘁ)).inv ≫ (b ▷ Sᘁ)) ≫
      ((S ◁ w) ▷ Sᘁ) =
    𝟙 _ ⊗≫ (M ◁ η_ S (Sᘁ)) ⊗≫ ((t ▷ S ≫ b ≫ (S ◁ w)) ▷ Sᘁ) ⊗≫ 𝟙 _ := by
  calc
    _ = 𝟙 _ ⊗≫ ((t ▷ (𝟙_ C.Obj)) ≫ (N ◁ η_ S (Sᘁ))) ⊗≫
      (b ▷ Sᘁ) ⊗≫ ((S ◁ w) ▷ Sᘁ) ⊗≫ 𝟙 _ := by monoidal
    _ = 𝟙 _ ⊗≫ ((M ◁ η_ S (Sᘁ)) ≫ (t ▷ (S ⊗ Sᘁ))) ⊗≫
      (b ▷ Sᘁ) ⊗≫ ((S ◁ w) ▷ Sᘁ) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = _ := by simp only [comp_whiskerRight]; monoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluation is normalized along an isomorphism with the tensor unit. -/
theorem evaluation_iso_unit (A : C.Obj) (e : A ≅ 𝟙_ C.Obj) :
    ((Dimensions.rightDualIsoMap e.symm ≪≫ Dimensions.rightDualUnitIso).hom ⊗ₘ e.hom) ≫
      (ρ_ (𝟙_ C.Obj)).hom = ε_ A (Aᘁ) := by
  letI : HasRightDual (𝟙_ C.Obj) := RightRigidCategory.rightDual (𝟙_ C.Obj)
  let p : ExactPairing (𝟙_ C.Obj) ((𝟙_ C.Obj)ᘁ) := HasRightDual.exact
  let q : ExactPairing (𝟙_ C.Obj) (𝟙_ C.Obj) := exactPairingUnit
  have hu := Dimensions.rightDualIso_evaluation p q
  change Dimensions.rightDualUnitIso.hom ▷ (𝟙_ C.Obj) ≫ (ρ_ (𝟙_ C.Obj)).hom =
    ε_ (𝟙_ C.Obj) ((𝟙_ C.Obj)ᘁ) at hu
  have he := rightAdjointMate_comp_evaluation e.inv
  let du : (𝟙_ C.Obj)ᘁ ⟶ 𝟙_ C.Obj := Dimensions.rightDualUnitIso.hom
  change ((e.invᘁ ≫ du) ⊗ₘ e.hom) ≫ (ρ_ (𝟙_ C.Obj)).hom = ε_ A (Aᘁ)
  change du ▷ (𝟙_ C.Obj) ≫ (ρ_ (𝟙_ C.Obj)).hom =
    ε_ (𝟙_ C.Obj) ((𝟙_ C.Obj)ᘁ) at hu
  calc
    _ = 𝟙 _ ⊗≫ ((Aᘁ : C.Obj) ◁ e.hom) ⊗≫ ((e.invᘁ) ▷ (𝟙_ C.Obj)) ⊗≫
      (du ▷ (𝟙_ C.Obj)) ⊗≫ (ρ_ (𝟙_ C.Obj)).hom := by
        simp only [tensorHom_def', comp_whiskerRight]
        monoidal
    _ = 𝟙 _ ⊗≫ ((Aᘁ : C.Obj) ◁ e.hom) ⊗≫ ((e.invᘁ) ▷ (𝟙_ C.Obj)) ⊗≫
      (du ▷ (𝟙_ C.Obj) ≫ (ρ_ (𝟙_ C.Obj)).hom) := by monoidal
    _ = 𝟙 _ ⊗≫ ((Aᘁ : C.Obj) ◁ e.hom) ⊗≫
      ((e.invᘁ) ▷ (𝟙_ C.Obj) ≫ ε_ (𝟙_ C.Obj) ((𝟙_ C.Obj)ᘁ)) := by rw [hu]; monoidal
    _ = 𝟙 _ ⊗≫ ((Aᘁ : C.Obj) ◁ e.hom) ⊗≫
      (((Aᘁ : C.Obj) ◁ e.inv) ≫ ε_ A (Aᘁ)) := by rw [he]
    _ = 𝟙 _ ⊗≫ ((((Aᘁ : C.Obj) ◁ e.hom) ≫ ((Aᘁ : C.Obj) ◁ e.inv)) ≫ ε_ A (Aᘁ)) := by monoidal
    _ = _ := by rw [← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]; monoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Closing the right unit isomorphism gives ordinary evaluation. -/
theorem close_rightUnit_eval (T A : C.Obj) (e : A ≅ 𝟙_ C.Obj) :
    closeFusionMap C T A T ((T ◁ e.hom) ≫ (ρ_ T).hom) ≫
      (Dimensions.rightDualIsoMap e.symm ≪≫ Dimensions.rightDualUnitIso).hom = ε_ T (Tᘁ) := by
  let d : Aᘁ ⟶ 𝟙_ C.Obj := (Dimensions.rightDualIsoMap e.symm ≪≫ Dimensions.rightDualUnitIso).hom
  let z := closeFusionMap C T A T ((T ◁ e.hom) ≫ (ρ_ T).hom)
  have he : (d ⊗ₘ e.hom) ≫ (ρ_ (𝟙_ C.Obj)).hom = ε_ A (Aᘁ) := evaluation_iso_unit C A e
  have hz := closeFusionMap_evaluation C T A T ((T ◁ e.hom) ≫ (ρ_ T).hom)
  change (z ▷ A) ≫ ε_ A (Aᘁ) =
    𝟙 _ ⊗≫ ((Tᘁ : C.Obj) ◁ ((T ◁ e.hom) ≫ (ρ_ T).hom)) ⊗≫ ε_ T (Tᘁ) at hz
  change z ≫ d = ε_ T (Tᘁ)
  have hleft : (𝟙 (Tᘁ ⊗ T) ⊗≫ (((Tᘁ : C.Obj) ⊗ T) ◁ e.inv) ⊗≫
      (z ▷ A) ⊗≫ (d ⊗ₘ e.hom) ⊗≫ (ρ_ (𝟙_ C.Obj)).hom) = z ≫ d := by
    calc
      _ = 𝟙 _ ⊗≫ ((((Tᘁ : C.Obj) ⊗ T) ◁ e.inv) ≫ (z ▷ A)) ⊗≫
        (d ⊗ₘ e.hom) ⊗≫ (ρ_ (𝟙_ C.Obj)).hom := by simp [monoidalComp, tensorHom_def', Category.assoc]
      _ = 𝟙 _ ⊗≫ ((z ▷ (𝟙_ C.Obj)) ≫ ((Aᘁ : C.Obj) ◁ e.inv)) ⊗≫
        (d ⊗ₘ e.hom) ⊗≫ (ρ_ (𝟙_ C.Obj)).hom := by rw [whisker_exchange]
      _ = 𝟙 _ ⊗≫ (z ▷ (𝟙_ C.Obj)) ⊗≫
        (((Aᘁ : C.Obj) ◁ (e.inv ≫ e.hom)) ≫ (d ▷ (𝟙_ C.Obj))) ⊗≫
          (ρ_ (𝟙_ C.Obj)).hom := by
        simp only [tensorHom_def', whiskerLeft_comp]
        simp [monoidalComp, Category.assoc]
      _ = _ := by rw [Iso.inv_hom_id, whiskerLeft_id, Category.id_comp]; dsimp [d]; monoidal
  calc
    _ = 𝟙 _ ⊗≫ (((Tᘁ : C.Obj) ⊗ T) ◁ e.inv) ⊗≫
      (z ▷ A) ⊗≫ (d ⊗ₘ e.hom) ⊗≫ (ρ_ (𝟙_ C.Obj)).hom := hleft.symm
    _ = 𝟙 _ ⊗≫ (((Tᘁ : C.Obj) ⊗ T) ◁ e.inv) ⊗≫
      (z ▷ A) ⊗≫ ((d ⊗ₘ e.hom) ≫ (ρ_ (𝟙_ C.Obj)).hom) := by simp [monoidalComp, tensorHom_def', Category.assoc]
    _ = 𝟙 _ ⊗≫ (((Tᘁ : C.Obj) ⊗ T) ◁ e.inv) ⊗≫
      ((z ▷ A) ≫ ε_ A (Aᘁ)) := by rw [he]; monoidal
    _ = 𝟙 _ ⊗≫ (((Tᘁ : C.Obj) ⊗ T) ◁ e.inv) ⊗≫
      (𝟙 _ ⊗≫ ((Tᘁ : C.Obj) ◁ ((T ◁ e.hom) ≫ (ρ_ T).hom)) ⊗≫ ε_ T (Tᘁ)) := by rw [hz]
    _ = 𝟙 _ ⊗≫ ((Tᘁ : C.Obj) ◁ (T ◁ (e.inv ≫ e.hom))) ⊗≫ ε_ T (Tᘁ) := by
      simp only [whiskerLeft_comp]; monoidal
    _ = _ := by rw [Iso.inv_hom_id]; simp; monoidal

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical unit-column crossing block contracts by evaluation. -/
theorem crossingUnitBlock_eval (X T A : C.Obj) (e : A ≅ 𝟙_ C.Obj) :
  let d : Aᘁ ≅ 𝟙_ C.Obj := Dimensions.rightDualIsoMap e.symm ≪≫ Dimensions.rightDualUnitIso
  let us : (A ⊗ X) ⊗ Aᘁ ≅ X := ((e ⊗ᵢ Iso.refl X) ⊗ᵢ d) ≪≫
    ((λ_ X) ⊗ᵢ Iso.refl (𝟙_ C.Obj)) ≪≫ ρ_ X
  let te : T ⊗ A ≅ T := whiskerLeftIso T e ≪≫ ρ_ T
  crossingBlock C X T T A te.inv te.hom ≫ (T ◁ us.hom) =
    𝟙 _ ⊗≫ ((T ⊗ X) ◁ ε_ T (Tᘁ)) ⊗≫ 𝟙 _ := by
  dsimp only
  let d : Aᘁ ⟶ 𝟙_ C.Obj := (Dimensions.rightDualIsoMap e.symm ≪≫ Dimensions.rightDualUnitIso).hom
  let q : Tᘁ ⊗ T ⟶ Aᘁ := closeFusionMap C T A T ((T ◁ e.hom) ≫ (ρ_ T).hom)
  have hq : q ≫ d = ε_ T (Tᘁ) := close_rightUnit_eval C T A e
  simp only [crossingBlock, Iso.trans_hom, Iso.trans_inv, whiskerLeftIso_hom,
    whiskerLeftIso_inv, tensorIso_hom, Iso.refl_hom, tensorHom_def, whiskerLeft_id,
    Category.comp_id]
  let f : A ⟶ 𝟙_ C.Obj := e.hom
  let g : 𝟙_ C.Obj ⟶ A := e.inv
  have hgf : g ≫ f = 𝟙 (𝟙_ C.Obj) := e.inv_hom_id
  change ((α_ (T ⊗ X) (Tᘁ) T).hom ≫
    ((((ρ_ T).inv ≫ T ◁ g) ▷ X ▷ ((Tᘁ : C.Obj) ⊗ T)) ≫
      (((T ⊗ A) ⊗ X) ◁ q)) ≫
      (α_ (T ⊗ A) X (Aᘁ)).hom ≫ (α_ T A (X ⊗ Aᘁ)).hom ≫
      T ◁ (α_ A X (Aᘁ)).inv) ≫
    T ◁ (((f ▷ X ▷ (Aᘁ)) ≫ ((𝟙_ C.Obj ⊗ X) ◁ d)) ≫
      ((λ_ X).hom ▷ (𝟙_ C.Obj)) ≫ (ρ_ X).hom) = _
  clear_value f g d q
  calc
    _ = 𝟙 _ ⊗≫ ((((ρ_ T).inv ≫ T ◁ g) ▷ X) ▷ ((Tᘁ : C.Obj) ⊗ T)) ⊗≫
      (((((T ⊗ A) ⊗ X) ◁ q) ≫ (((T ◁ f) ▷ X) ▷ Aᘁ))) ⊗≫
      (((T ⊗ (𝟙_ C.Obj)) ⊗ X) ◁ d) ⊗≫ 𝟙 _ := by
        simp only [comp_whiskerRight, whiskerLeft_comp]
        monoidal
    _ = 𝟙 _ ⊗≫ ((((ρ_ T).inv ≫ T ◁ g) ▷ X) ▷ ((Tᘁ : C.Obj) ⊗ T)) ⊗≫
      (((((T ◁ f) ▷ X) ▷ ((Tᘁ : C.Obj) ⊗ T)) ≫
        (((T ⊗ (𝟙_ C.Obj)) ⊗ X) ◁ q))) ⊗≫
      (((T ⊗ (𝟙_ C.Obj)) ⊗ X) ◁ d) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
    _ = 𝟙 _ ⊗≫ ((((ρ_ T).inv ≫ (T ◁ (g ≫ f))) ▷ X) ▷ ((Tᘁ : C.Obj) ⊗ T)) ⊗≫
      (((T ⊗ (𝟙_ C.Obj)) ⊗ X) ◁ (q ≫ d)) ⊗≫ 𝟙 _ := by
        simp only [whiskerLeft_comp, comp_whiskerRight]
        simp [monoidalComp, Category.assoc]
    _ = _ := by rw [hq, hgf]; simp; monoidal

end PropertyF.Ground.CentreInduction
