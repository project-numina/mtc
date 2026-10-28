module
public import PropertyF.Ground.CentreInduction.Underlying
public import PropertyF.Ground.Dimensions.Pivotal

/-! The unit summand of the underlying induction object. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The unit-labelled summand is isomorphic to the middle object. -/
def unitSummandIso (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (simples C (unitIndex C) ⊗ X) ⊗ (simples C (unitIndex C))ᘁ ≅ X := by
  let e : simples C (unitIndex C) ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  let d : (simples C (unitIndex C))ᘁ ≅ 𝟙_ C.Obj :=
    Dimensions.rightDualIsoMap e.symm ≪≫ Dimensions.rightDualUnitIso
  exact ((e ⊗ᵢ Iso.refl X) ⊗ᵢ d) ≪≫ ((λ_ X) ⊗ᵢ Iso.refl (𝟙_ C.Obj)) ≪≫ ρ_ X

set_option backward.isDefEq.respectTransparency false in
/-- Every object is a retract of its underlying induction sum through the
unit-labelled component. -/
def unitSummandRetract (C : BraidedFusionCategory.{v,u}) (X : C.Obj) :
    Retract X (underlying C X) where
  i := (unitSummandIso C X).inv ≫ biproduct.ι (fun i : Fin (rank C) => (simples C i ⊗ X) ⊗ (simples C i)ᘁ) (unitIndex C)
  r := biproduct.π (fun i : Fin (rank C) => (simples C i ⊗ X) ⊗ (simples C i)ᘁ) (unitIndex C) ≫ (unitSummandIso C X).hom
  retract := by simp [underlying, Category.assoc]

/-- A fixed map on either outer tensor factor commutes with a map on the
middle factor. -/
@[reassoc]
theorem tensor_middle_natural (C : BraidedFusionCategory.{v,u})
    {A B U V X Y : C.Obj} (a : A ⟶ B) (d : U ⟶ V) (f : X ⟶ Y) :
    (((𝟙 A ⊗ₘ f) ⊗ₘ 𝟙 U)) ≫ ((a ⊗ₘ 𝟙 Y) ⊗ₘ d) =
      ((a ⊗ₘ 𝟙 X) ⊗ₘ d) ≫ (((𝟙 B ⊗ₘ f) ⊗ₘ 𝟙 V)) := by
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The unit summand isomorphism is natural in the middle factor. -/
theorem unitSummandIso_natural (C : BraidedFusionCategory.{v,u})
    {X Y : C.Obj} (f : X ⟶ Y) :
    ((simples C (unitIndex C) ◁ f) ▷ (simples C (unitIndex C))ᘁ) ≫
        (unitSummandIso C Y).hom = (unitSummandIso C X).hom ≫ f := by
  let A := simples C (unitIndex C)
  let e : A ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  let d : Aᘁ ≅ 𝟙_ C.Obj := Dimensions.rightDualIsoMap e.symm ≪≫ Dimensions.rightDualUnitIso
  change ((A ◁ f) ▷ Aᘁ) ≫
      (((e ⊗ᵢ Iso.refl Y) ⊗ᵢ d) ≪≫ ((λ_ Y) ⊗ᵢ Iso.refl (𝟙_ C.Obj)) ≪≫ ρ_ Y).hom =
      (((e ⊗ᵢ Iso.refl X) ⊗ᵢ d) ≪≫ ((λ_ X) ⊗ᵢ Iso.refl (𝟙_ C.Obj)) ≪≫ ρ_ X).hom ≫ f
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
  rw [← id_tensorHom, ← tensorHom_id]
  rw [tensor_middle_natural_assoc C]
  simp only [← tensorHom_comp_tensorHom_assoc, id_tensorHom, Category.id_comp,
    leftUnitor_naturality_assoc, tensorHom_id, rightUnitor_naturality]
  rw [rightUnitor_naturality_assoc, leftUnitor_naturality]
  rw [rightUnitor_naturality_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The unit-summand projection is natural. This is the candidate underlying
counit for the centre-forgetful right adjunction. -/
def underlyingCounit (C : BraidedFusionCategory.{v,u}) : underlyingFunctor C ⟶ 𝟭 C.Obj where
  app X := (unitSummandRetract C X).r
  naturality {X Y} f := by
    dsimp only [underlyingFunctor, unitSummandRetract, Functor.id_map]
    simp only [Category.assoc, biproduct.map_π_assoc]
    simpa only [Category.assoc] using congrArg (fun g =>
      biproduct.π (fun i : Fin (rank C) => (simples C i ⊗ X) ⊗ (simples C i)ᘁ)
        (unitIndex C) ≫ g) (unitSummandIso_natural C f)



end PropertyF.Ground.CentreInduction
