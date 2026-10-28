module
public import PropertyF.Ground.CentreInduction.CrossingBlocks
public import PropertyF.Ground.Dimensions.Pivotal
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Centre.Rigid
public import PropertyF.Ground.Calculus.PartialTrace
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Fusion.SemisimpleSplit
public import PropertyF.Ground.Centre.Abelian
public import PropertyF.Ground.CentreInduction.Representatives
public import PropertyF.Ground.CentreBundle.Fusion

open PropertyF.Ground.Dimensions

/-! The unit summand of the underlying induction object. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The unit-labelled summand is isomorphic to the middle object. -/
def unitSummandIso :
    (simples C (unitIndex C) ⊗ X) ⊗ (simples C (unitIndex C))ᘁ ≅ X :=
  let e : simples C (unitIndex C) ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  let d : (simples C (unitIndex C))ᘁ ≅ 𝟙_ C.Obj :=
    rightDualIsoMap e.symm ≪≫ rightDualUnitIso
  ((e ⊗ᵢ Iso.refl X) ⊗ᵢ d) ≪≫ ((λ_ X) ⊗ᵢ Iso.refl (𝟙_ C.Obj)) ≪≫ ρ_ X

set_option backward.isDefEq.respectTransparency false in
/-- Every object is a retract of its underlying induction sum through the
unit-labelled component. -/
def unitSummandRetract :
    Retract X (underlying C X) where
  i := (unitSummandIso C X).inv ≫ biproduct.ι (inductionSummand C X) (unitIndex C)
  r := biproduct.π (inductionSummand C X) (unitIndex C) ≫ (unitSummandIso C X).hom
  retract := by simp [underlying, Category.assoc]

/-- A fixed map on either outer tensor factor commutes with a map on the
middle factor. -/
@[reassoc]
theorem tensor_middle_natural {D : Type u} [Category.{v} D] [MonoidalCategory D]
    {A B U V X Y : D} (a : A ⟶ B) (d : U ⟶ V) (f : X ⟶ Y) :
    (((𝟙 A ⊗ₘ f) ⊗ₘ 𝟙 U)) ≫ ((a ⊗ₘ 𝟙 Y) ⊗ₘ d) =
      ((a ⊗ₘ 𝟙 X) ⊗ₘ d) ≫ (((𝟙 B ⊗ₘ f) ⊗ₘ 𝟙 V)) := by
  simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The unit summand isomorphism is natural in the middle factor. -/
theorem unitSummandIso_natural {X Y : C.Obj} (f : X ⟶ Y) :
    ((simples C (unitIndex C) ◁ f) ▷ (simples C (unitIndex C))ᘁ) ≫
        (unitSummandIso C Y).hom = (unitSummandIso C X).hom ≫ f := by
  dsimp [unitSummandIso]
  rw [Category.assoc, ← id_tensorHom, ← tensorHom_id, tensor_middle_natural_assoc]
  simp only [id_tensorHom, tensorHom_id, rightUnitor_naturality, Category.assoc]
  rw [rightUnitor_naturality_assoc, leftUnitor_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- The unit-summand projection is natural. This is the candidate underlying
counit for the centre-forgetful right adjunction. -/
def underlyingCounit : underlyingFunctor C ⟶ 𝟭 C.Obj where
  app X := (unitSummandRetract C X).r
  naturality {X Y} f := by
    dsimp only [underlyingFunctor, unitSummandRetract, Functor.id_map]
    simp only [Category.assoc, biproduct.map_π_assoc]
    simpa only [Category.assoc] using congrArg (fun g =>
      biproduct.π (inductionSummand C X)
        (unitIndex C) ≫ g) (unitSummandIso_natural C f)

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
theorem coevaluation_iso_unit {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
    {A : D} (e : A ≅ 𝟙_ D) :
    η_ A Aᘁ ≫ (e.hom ⊗ₘ (rightDualIsoMap e.symm ≪≫
      rightDualUnitIso).hom) = (ρ_ (𝟙_ D)).inv := by
  let : HasRightDual (𝟙_ D) := RightRigidCategory.rightDual (𝟙_ D)
  dsimp only [Iso.trans_hom, rightDualIsoMap, Iso.symm_hom]
  rw [tensorHom_def, whiskerLeft_comp, ← Category.assoc (e.hom ▷ Aᘁ),
    ← tensorHom_def, ← Category.assoc, coevaluation_iso_map]
  exact coevaluation_rightDualIso HasRightDual.exact exactPairingUnit

end PropertyF.Ground.CentreInduction

end

/-! Candidate underlying unit of the centre induction adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u})
local notation "𝒵" => Center C.Obj
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Insert a coevaluation and move its object past the centre half-braiding. -/
def unitComponentAt {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
    (Z : Center D) (S : D) : Z.1 ⟶ (S ⊗ Z.1) ⊗ Sᘁ :=
  (ρ_ Z.1).inv ≫ (Z.1 ◁ η_ S (Sᘁ)) ≫ (α_ Z.1 S (Sᘁ)).inv ≫ ((Z.2.β S).hom ▷ Sᘁ)

/-- The unit component indexed by a simple object. -/
def unitComponent (Z : 𝒵) (i : Fin (rank C)) :
    Z.1 ⟶ (simples C i ⊗ Z.1) ⊗ (simples C i)ᘁ :=
  unitComponentAt Z (simples C i)

/-- The underlying map of the proposed adjunction unit. Centrality depends
on constructing the induction half-braiding and is not asserted. -/
def unitCandidate (Z : 𝒵) :
    Z.1 ⟶ underlying C Z.1 :=
  biproduct.lift (unitComponent C Z)

set_option backward.isDefEq.respectTransparency false in
/-- The proposed unit component is natural for genuine centre maps. -/
theorem unitComponent_natural {X Y : 𝒵} (f : X ⟶ Y) (i : Fin (rank C)) :
    f.f ≫ unitComponent C Y i = unitComponent C X i ≫
      ((simples C i ◁ f.f) ▷ (simples C i)ᘁ) := by
  dsimp [unitComponent, unitComponentAt]
  rw [Category.assoc, rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc]
  simp only [Category.assoc, ← comp_whiskerRight, f.comm]


end PropertyF.Ground.CentreInduction

end

/-! The first underlying triangle for the proposed centre adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The underlying maps proposed for the induction unit and counit satisfy
the first triangle identity. -/
theorem unitCandidate_counit (C : BraidedFusionCategory.{v,u})
    (Z : Center C.Obj) :
    unitCandidate C Z ≫ (underlyingCounit C).app Z.1 = 𝟙 Z.1 := by
  simp only [unitCandidate, underlyingCounit, unitSummandRetract,
    CategoryTheory.Limits.biproduct.lift_π_assoc]
  let A := simples C (unitIndex C)
  let e : A ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  let d : Aᘁ ≅ 𝟙_ C.Obj := rightDualIsoMap e.symm ≪≫ rightDualUnitIso
  dsimp only [unitComponent, unitComponentAt, unitSummandIso]
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, tensorHom_def,
    whiskerLeft_id, Category.comp_id, Category.assoc]
  rw [← comp_whiskerRight_assoc, ← Z.2.naturality e.hom, comp_whiskerRight_assoc,
    ← associator_inv_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    CentreRigid.halfBraiding_unit Z]
  simp only [comp_whiskerRight, Category.assoc]
  rw [triangle_assoc_comp_right_assoc, ← whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  have hunit : η_ A Aᘁ ≫ (e.hom ▷ Aᘁ) ≫ (λ_ Aᘁ).hom ≫ d.hom = 𝟙 (𝟙_ C.Obj) := by
    rw [← leftUnitor_naturality, ← tensorHom_def_assoc, ← Category.assoc,
      coevaluation_iso_unit e]
    monoidal_coherence
  simp only [← whiskerLeft_comp_assoc]
  dsimp only [A, e, d, Iso.trans_hom] at hunit
  simp only [Category.assoc] at hunit ⊢
  rw [hunit, whiskerLeft_id]
  simp

end PropertyF.Ground.CentreInduction

end
