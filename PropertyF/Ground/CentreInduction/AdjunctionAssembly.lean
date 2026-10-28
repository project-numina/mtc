module
public import PropertyF.Ground.CentreInduction.CrossingBlocks
public import PropertyF.Ground.Dimensions.Pivotal
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Centre.Rigid
public import PropertyF.Ground.CentreInduction.Representatives
public import PropertyF.Ground.CentreBundle.Fusion

open PropertyF.Ground.Dimensions

/-! The unit summand of the underlying induction object. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
local notation "Sᶜ" => simples C
attribute [local instance] Abelian.hasFiniteBiproducts
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- A tensor factor isomorphic to the unit and its dual cancel around any object. -/
def unitTensorIso {A : D} [HasRightDual A] (e : A ≅ 𝟙_ D) (X : D) :
    (A ⊗ X) ⊗ Aᘁ ≅ X :=
  letI : HasRightDual (𝟙_ D) := hasRightDualUnit
  ((e ⊗ᵢ Iso.refl X) ⊗ᵢ rightDualIsoMap e.symm) ≪≫
    ((λ_ X) ⊗ᵢ Iso.refl (𝟙_ D)) ≪≫ ρ_ X

/-- The unit-labelled summand is isomorphic to the middle object. -/
def unitSummandIso :
    (Sᶜ (unitIndex C) ⊗ X) ⊗ (Sᶜ (unitIndex C))ᘁ ≅ X :=
  unitTensorIso (Classical.choice (unitIndex_iso C)) X

set_option backward.isDefEq.respectTransparency false in
/-- Every object is a retract of its underlying induction sum through the
unit-labelled component. -/
def unitSummandRetract :
    Retract X (underlying C X) where
  i := (unitSummandIso C X).inv ≫ biproduct.ι (inductionSummand C X) (unitIndex C)
  r := biproduct.π (inductionSummand C X) (unitIndex C) ≫ (unitSummandIso C X).hom
  retract := by simp [underlying, Category.assoc]

variable {A B U V M N : D}

/-- A fixed map on either outer tensor factor commutes with a map on the
middle factor. -/
@[reassoc]
theorem tensor_middle_natural (a : A ⟶ B) (d : U ⟶ V) (f : M ⟶ N) :
    (((𝟙 A ⊗ₘ f) ⊗ₘ 𝟙 U)) ≫ ((a ⊗ₘ 𝟙 N) ⊗ₘ d) =
      ((a ⊗ₘ 𝟙 M) ⊗ₘ d) ≫ (((𝟙 B ⊗ₘ f) ⊗ₘ 𝟙 V)) := by
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Cancelling tensor-unit factors is natural in the middle object. -/
theorem unitTensorIso_natural [HasRightDual A] (e : A ≅ 𝟙_ D) (f : M ⟶ N) :
    ((A ◁ f) ▷ Aᘁ) ≫ (unitTensorIso e N).hom = (unitTensorIso e M).hom ≫ f := by
  dsimp [unitTensorIso, hasRightDualUnit]
  rw [Category.assoc, ← id_tensorHom, ← tensorHom_id, tensor_middle_natural_assoc]
  simp only [id_tensorHom, tensorHom_id]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The unit-summand projection is natural. This is the candidate underlying
counit for the centre-forgetful right adjunction. -/
def underlyingCounit : underlyingFunctor C ⟶ 𝟭 C.Obj where
  app X := (unitSummandRetract C X).r
  naturality {X Y} f := by
    simpa only [underlyingFunctor, unitSummandRetract, unitSummandIso, Functor.id_map,
      Category.assoc, biproduct.map_π_assoc] using congrArg (fun g =>
      biproduct.π (inductionSummand C X)
        (unitIndex C) ≫ g) (unitTensorIso_natural (Classical.choice (unitIndex_iso C)) f)

end PropertyF.Ground.CentreInduction

end

/-! Coevaluation transported along an isomorphism with the unit. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An object isomorphic to the tensor unit has its coevaluation normalized
by the induced identification of its right dual with the unit. -/
theorem coevaluation_iso_unit {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {A : D} [HasRightDual A] (e : A ≅ 𝟙_ D) :
    letI : HasRightDual (𝟙_ D) := hasRightDualUnit
    η_ A Aᘁ ≫ (e.hom ▷ Aᘁ) ≫ (λ_ Aᘁ).hom ≫
      (rightDualIsoMap e.symm).hom = 𝟙 (𝟙_ D) := by
  let : HasRightDual (𝟙_ D) := hasRightDualUnit
  rw [← leftUnitor_naturality, ← tensorHom_def_assoc, ← Category.assoc,
    show η_ A Aᘁ ≫ (e.hom ⊗ₘ (rightDualIsoMap e.symm).hom) = (ρ_ (𝟙_ D)).inv from
      coevaluation_iso_map e]
  monoidal_coherence

end PropertyF.Ground.CentreInduction

end

/-! Candidate underlying unit of the centre induction adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u})
local notation "Sᶜ" => simples C
local notation "𝒵" => Center C.Obj
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Insert a coevaluation and move its object past the centre half-braiding. -/
def unitComponentAt {D : Type u} [Category.{v} D] [MonoidalCategory D]
    (Z : Center D) (S : D) [HasRightDual S] : Z.1 ⟶ (S ⊗ Z.1) ⊗ Sᘁ :=
  (ρ_ Z.1).inv ≫ (Z.1 ◁ η_ S (Sᘁ)) ≫ (α_ Z.1 S (Sᘁ)).inv ≫ ((Z.2.β S).hom ▷ Sᘁ)

/-- The unit component indexed by a simple object. -/
def unitComponent (Z : 𝒵) (i : Fin (rank C)) :
    Z.1 ⟶ (Sᶜ i ⊗ Z.1) ⊗ (Sᶜ i)ᘁ :=
  unitComponentAt Z (Sᶜ i)

/-- The underlying map of the proposed adjunction unit. Centrality depends
on constructing the induction half-braiding and is not asserted. -/
def unitCandidate (Z : 𝒵) :
    Z.1 ⟶ underlying C Z.1 :=
  biproduct.lift (unitComponent C Z)

set_option backward.isDefEq.respectTransparency false in
/-- The unit component is natural for centre maps. -/
theorem unitComponentAt_natural {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {S : D} [HasRightDual S] {X Y : Center D} (f : X ⟶ Y) :
    f.f ≫ unitComponentAt Y S = unitComponentAt X S ≫ ((S ◁ f.f) ▷ Sᘁ) := by
  simp only [unitComponentAt, Category.assoc, rightUnitor_inv_naturality_assoc,
    ← whisker_exchange_assoc, associator_inv_naturality_left_assoc, ← comp_whiskerRight, f.comm]


end PropertyF.Ground.CentreInduction

end

/-! The first underlying triangle for the proposed centre adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The unit component associated to an object isomorphic to the tensor unit
is inverse to the canonical identification of its tensor factors. -/
theorem unitComponentAt_iso_unit {D : Type u} [Category.{v} D] [MonoidalCategory D]
    (Z : Center D) {A : D} [HasRightDual A] (e : A ≅ 𝟙_ D) :
    unitComponentAt Z A ≫ (unitTensorIso e Z.1).hom = 𝟙 Z.1 := by
  dsimp only [unitComponentAt, unitTensorIso]
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, tensorHom_def,
    whiskerLeft_id, Category.comp_id, Category.assoc]
  rw [← comp_whiskerRight_assoc, ← Z.2.naturality e.hom, comp_whiskerRight_assoc,
    ← associator_inv_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    CentreRigid.halfBraiding_unit Z]
  simp only [comp_whiskerRight, Category.assoc]
  rw [triangle_assoc_comp_right_assoc, ← whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp,
    ← whiskerLeft_comp_assoc, Category.assoc]
  erw [reassoc_of% coevaluation_iso_unit e, whiskerLeft_id]
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The underlying maps proposed for the induction unit and counit satisfy
the first triangle identity. -/
theorem unitCandidate_counit (C : BraidedFusionCategory.{v,u})
    (Z : Center C.Obj) :
    unitCandidate C Z ≫ (underlyingCounit C).app Z.1 = 𝟙 Z.1 :=
  (CategoryTheory.Limits.biproduct.lift_π_assoc (unitComponent C Z) (unitIndex C)
    (unitSummandIso C Z.1).hom).trans
      (unitComponentAt_iso_unit Z (Classical.choice (unitIndex_iso C)))

end PropertyF.Ground.CentreInduction

end
