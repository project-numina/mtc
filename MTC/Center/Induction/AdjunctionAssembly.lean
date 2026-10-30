module
public import MTC.Center.Induction.CrossingBlocks
public import MTC.CategoryTheory.Dimensions.Pivotal
public import MTC.CategoryTheory.Dimensions.DualCoherence
public import MTC.Center.Rigid
public import MTC.Center.Induction.Representatives
public import MTC.Center.Fusion.Fusion

open MTC.Dimensions

/-! The unit summand of the underlying induction object. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
local notation "Sᶜ" => simples C
attribute [local instance] Abelian.hasFiniteBiproducts
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]

/-- Cancel outer tensor factors using maps to the tensor unit. -/
def unitTensorHom {A B : D} (f : A ⟶ 𝟙_ D) (d : B ⟶ 𝟙_ D) (X : D) :
    (A ⊗ X) ⊗ B ⟶ X :=
  ((f ⊗ₘ 𝟙 X) ⊗ₘ d) ≫ ((λ_ X).hom ⊗ₘ 𝟙 (𝟙_ D)) ≫ (ρ_ X).hom

/-- A tensor factor isomorphic to the unit and its dual cancel around any object. -/
def unitTensorIso {A : D} [HasRightDual A] (e : A ≅ 𝟙_ D) (X : D) :
    (A ⊗ X) ⊗ Aᘁ ≅ X :=
  ((e ⊗ᵢ Iso.refl X) ⊗ᵢ rightDualIsoMap e.symm) ≪≫
    ((λ_ X) ⊗ᵢ Iso.refl (𝟙_ D)) ≪≫ ρ_ X

variable {C} in
/-- The unit-labelled summand is isomorphic to the middle object. -/
def unitSummandIso :
    (Sᶜ (unitIndex C) ⊗ X) ⊗ (Sᶜ (unitIndex C))ᘁ ≅ X :=
  unitTensorIso (Classical.choice (unitIndex_iso C)) X

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- Every object is a retract of its underlying induction sum through the
unit-labelled component. -/
def unitSummandRetract :
    Retract X (underlying X) where
  i := (unitSummandIso X).inv ≫ biproduct.ι (inductionSummand X) (unitIndex C)
  r := biproduct.π (inductionSummand X) (unitIndex C) ≫ (unitSummandIso X).hom
  retract := by simp [underlying]

variable {A B U V M N : D}

/-- A fixed map on either outer tensor factor commutes with a map on the
middle factor. -/
theorem tensor_middle_natural (a : A ⟶ B) (d : U ⟶ V) (f : M ⟶ N) :
    CommSq ((A ◁ f) ▷ U) ((a ▷ M) ⊗ₘ d) ((a ▷ N) ⊗ₘ d) ((B ◁ f) ▷ V) :=
  ⟨by simp only [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom,
    Category.id_comp, Category.comp_id]⟩

set_option backward.isDefEq.respectTransparency false in
/-- Cancelling tensor-unit factors is natural in the middle object. -/
theorem unitTensorIso_natural [HasRightDual A] (e : A ≅ 𝟙_ D) (f : M ⟶ N) :
    ((A ◁ f) ▷ Aᘁ) ≫ (unitTensorIso e N).hom = (unitTensorIso e M).hom ≫ f := by
  dsimp [unitTensorIso, hasRightDualUnit]
  rw [Category.assoc, tensorHom_id, (tensor_middle_natural _ _ _).w_assoc]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The unit-summand projection is natural. This is the candidate underlying
counit for the centre-forgetful right adjunction. -/
def underlyingCounit : underlyingFunctor C ⟶ 𝟭 C.Obj where
  app X := (unitSummandRetract X).r
  naturality {X Y} f := by
    simpa [underlyingFunctor, unitSummandRetract, unitSummandIso] using congrArg (fun g =>
      biproduct.π (inductionSummand X)
        (unitIndex C) ≫ g) (unitTensorIso_natural (Classical.choice (unitIndex_iso C)) f)

end MTC.CentreInduction

end

/-! Coevaluation transported along an isomorphism with the unit. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CentreInduction
universe v u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An object isomorphic to the tensor unit has its coevaluation normalized
by the induced identification of its right dual with the unit. -/
theorem coevaluation_iso_unit {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {A : D} [HasRightDual A] (e : A ≅ 𝟙_ D) :
    η_ A Aᘁ ≫ (e.hom ▷ Aᘁ) ≫ (λ_ Aᘁ).hom ≫
      (rightDualIsoMap e.symm).hom = 𝟙 (𝟙_ D) := by
  rw [← leftUnitor_naturality, ← tensorHom_def_assoc, ← Category.assoc,
    show η_ A Aᘁ ≫ (e.hom ⊗ₘ (rightDualIsoMap e.symm).hom) = (ρ_ (𝟙_ D)).inv from
      coevaluation_iso_map e]
  monoidal_coherence

end MTC.CentreInduction

end

/-! Candidate underlying unit of the centre induction adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u})
local notation "Sᶜ" => simples C
local notation "𝒵" => Center C.Obj
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Insert a coevaluation and move its object past the centre half-braiding. -/
def unitComponentAt {D : Type u} [Category.{v} D] [MonoidalCategory D]
    (Z : Center D) (S : D) [HasRightDual S] : Z.1 ⟶ (S ⊗ Z.1) ⊗ Sᘁ :=
  (ρ_ Z.1).inv ≫ (Z.1 ◁ η_ S (Sᘁ)) ≫ (α_ Z.1 S (Sᘁ)).inv ≫ ((Z.2.β S).hom ▷ Sᘁ)

variable {C} in
/-- The unit component indexed by a simple object. -/
def unitComponent (Z : 𝒵) (i : Fin (rank C)) :
    Z.1 ⟶ (Sᶜ i ⊗ Z.1) ⊗ (Sᶜ i)ᘁ :=
  unitComponentAt Z (Sᶜ i)

variable {C} in
/-- The underlying map of the proposed adjunction unit. Centrality depends
on constructing the induction half-braiding and is not asserted. -/
def unitCandidate (Z : 𝒵) :
    Z.1 ⟶ underlying Z.1 :=
  biproduct.lift (unitComponent Z)

set_option backward.isDefEq.respectTransparency false in
/-- The unit component is natural for centre maps. -/
theorem unitComponentAt_natural {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {S : D} [HasRightDual S] {X Y : Center D} (f : X ⟶ Y) :
    f.f ≫ unitComponentAt Y S = unitComponentAt X S ≫ ((S ◁ f.f) ▷ Sᘁ) := by
  simp only [unitComponentAt, Category.assoc, rightUnitor_inv_naturality_assoc,
    ← whisker_exchange_assoc, associator_inv_naturality_left_assoc, ← comp_whiskerRight, f.comm]


end MTC.CentreInduction

end

/-! The first underlying triangle for the proposed centre adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
open CategoryTheory.Limits
namespace MTC.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A unit component cancels against maps satisfying the coevaluation unit equation. -/
theorem unitComponentAt_unit_factor {D : Type u} [Category.{v} D] [MonoidalCategory D]
    (Z : Center D) {A : D} [HasRightDual A] (f : A ⟶ 𝟙_ D) (d : Aᘁ ⟶ 𝟙_ D)
    (h : η_ A Aᘁ ≫ (f ▷ Aᘁ) ≫ (λ_ Aᘁ).hom ≫ d = 𝟙 (𝟙_ D)) :
    unitComponentAt Z A ≫ unitTensorHom f d Z.1 = 𝟙 Z.1 := by
  dsimp only [unitComponentAt, unitTensorHom]
  simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, Category.assoc]
  rw [← comp_whiskerRight_assoc, ← Z.2.naturality f, comp_whiskerRight_assoc,
    ← associator_inv_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    CentreRigid.halfBraiding_unit Z]
  simp only [comp_whiskerRight, Category.assoc]
  rw [triangle_assoc_comp_right_assoc, ← whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp,
    ← whiskerLeft_comp_assoc, Category.assoc]
  simp only [h, whiskerLeft_id, Category.id_comp, Iso.inv_hom_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The underlying maps proposed for the induction unit and counit satisfy
the first triangle identity. -/
theorem unitCandidate_counit {C : BraidedFusionCategory.{v,u}}
    (Z : Center C.Obj) :
    unitCandidate Z ≫ (underlyingCounit C).app Z.1 = 𝟙 Z.1 :=
  let e := Classical.choice (unitIndex_iso C)
  (biproduct.lift_π_assoc (unitComponent Z) (unitIndex C) (unitSummandIso Z.1).hom).trans
    (unitComponentAt_unit_factor Z e.hom (rightDualIsoMap e.symm).hom (coevaluation_iso_unit e))

end MTC.CentreInduction

end
