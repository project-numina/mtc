module
public import PropertyF.Ground.CentreInduction.UnitSummand
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Calculus.PartialTrace
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Fusion.SemisimpleSplit
public import PropertyF.Ground.Centre.Cokernel
public import PropertyF.Ground.CentreRigid.Unit
public import PropertyF.Ground.CentreRigid.Unit
public import PropertyF.Ground.CentreInduction.Representatives
public import PropertyF.Ground.CentreBundle.Fusion

/-! Coevaluation transported along an isomorphism with the unit. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An object isomorphic to the tensor unit has its coevaluation normalized
by the induced identification of its right dual with the unit. -/
theorem coevaluation_iso_unit (C : BraidedFusionCategory.{v,u})
    {A : C.Obj} (e : A ≅ 𝟙_ C.Obj) :
    η_ A Aᘁ ≫ (e.hom ⊗ₘ (Dimensions.rightDualIsoMap e.symm ≪≫
      Dimensions.rightDualUnitIso).hom) = (ρ_ (𝟙_ C.Obj)).inv := by
  let : HasRightDual (𝟙_ C.Obj) := RightRigidCategory.rightDual (𝟙_ C.Obj)
  let p : ExactPairing (𝟙_ C.Obj) ((𝟙_ C.Obj)ᘁ) := HasRightDual.exact
  let q : ExactPairing (𝟙_ C.Obj) (𝟙_ C.Obj) := exactPairingUnit
  have hu := Dimensions.coevaluation_rightDualIso p q
  have he := coevaluation_comp_rightAdjointMate e.inv
  change η_ A Aᘁ ≫ A ◁ (e.invᘁ) = η_ (𝟙_ C.Obj) ((𝟙_ C.Obj)ᘁ) ≫ e.inv ▷ _ at he
  change η_ (𝟙_ C.Obj) ((𝟙_ C.Obj)ᘁ) ≫
    (𝟙_ C.Obj) ◁ Dimensions.rightDualUnitIso.hom = (ρ_ (𝟙_ C.Obj)).inv at hu
  simp only [Iso.trans_hom, Dimensions.rightDualIsoMap, Iso.symm_inv, Iso.symm_hom, Category.assoc,
    tensorHom_def', whiskerLeft_comp]
  rw [← Category.assoc, he]
  simp only [Category.assoc]
  rw [← whisker_exchange_assoc]
  have hh : (e.inv ▷ (𝟙_ C.Obj)) ≫ (e.hom ▷ (𝟙_ C.Obj)) = 𝟙 _ := by
    rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]
  calc
    _ = (η_ (𝟙_ C.Obj) ((𝟙_ C.Obj)ᘁ) ≫
      (𝟙_ C.Obj) ◁ Dimensions.rightDualUnitIso.hom) ≫
      ((e.inv ▷ (𝟙_ C.Obj)) ≫ (e.hom ▷ (𝟙_ C.Obj))) := by simp only [Category.assoc]
    _ = _ := by rw [hh, Category.comp_id]; exact hu

end PropertyF.Ground.CentreInduction

end

/-! Candidate underlying unit of the centre induction adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The component indexed by a simple object inserts its coevaluation and
moves the simple strand past the centre object's half-braiding. -/
def unitComponent (C : BraidedFusionCategory.{v,u})
    (Z : CategoryTheory.Center C.Obj) (i : Fin (rank C)) :
    Z.1 ⟶ (simples C i ⊗ Z.1) ⊗ (simples C i)ᘁ :=
  (ρ_ Z.1).inv ≫ (Z.1 ◁ η_ (simples C i) ((simples C i)ᘁ)) ≫
    (α_ Z.1 (simples C i) ((simples C i)ᘁ)).inv ≫
    ((Z.2.β (simples C i)).hom ▷ (simples C i)ᘁ)

/-- The underlying map of the proposed adjunction unit. Centrality depends
on constructing the induction half-braiding and is not asserted. -/
def unitCandidate (C : BraidedFusionCategory.{v,u}) (Z : CategoryTheory.Center C.Obj) :
    Z.1 ⟶ underlying C Z.1 :=
  biproduct.lift (unitComponent C Z)

set_option backward.isDefEq.respectTransparency false in
/-- The proposed unit component is natural for genuine centre maps. -/
theorem unitComponent_natural (C : BraidedFusionCategory.{v,u})
    {X Y : CategoryTheory.Center C.Obj} (f : X ⟶ Y) (i : Fin (rank C)) :
    f.f ≫ unitComponent C Y i = unitComponent C X i ≫
      ((simples C i ◁ f.f) ▷ (simples C i)ᘁ) := by
  dsimp [unitComponent]
  simp only [Category.assoc]
  rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc]
  have hc := congrArg (fun g => g ▷ (simples C i)ᘁ) (f.comm (simples C i))
  simp only [comp_whiskerRight] at hc
  simpa only [Category.assoc] using congrArg (fun g =>
    (ρ_ X.1).inv ≫ (X.1 ◁ η_ (simples C i) ((simples C i)ᘁ)) ≫
      (α_ X.1 (simples C i) ((simples C i)ᘁ)).inv ≫ g) hc

set_option backward.isDefEq.respectTransparency false in
/-- The proposed underlying unit is natural in centre objects. -/
def unitCandidateNatural (C : BraidedFusionCategory.{v,u}) :
    CategoryTheory.Center.forget C.Obj ⟶
      CategoryTheory.Center.forget C.Obj ⋙ underlyingFunctor C where
  app Z := unitCandidate C Z
  naturality {X Y} f := by
    apply biproduct.hom_ext
    intro i
    simp only [Functor.comp_map, underlyingFunctor,
      unitCandidate, CategoryTheory.Center.forget, Category.assoc, biproduct.lift_π, biproduct.lift_π_assoc, biproduct.map_π]
    simpa only [Category.assoc] using unitComponent_natural C f i

set_option backward.isDefEq.respectTransparency false in
/-- The underlying left triangle reduces to the unit-labelled coevaluation
component; no triangle identity is asserted here. -/
theorem unitCandidate_counit_component (C : BraidedFusionCategory.{v,u})
    (Z : CategoryTheory.Center C.Obj) :
    unitCandidate C Z ≫ (underlyingCounit C).app Z.1 =
      unitComponent C Z (unitIndex C) ≫ (unitSummandIso C Z.1).hom := by
  simp [unitCandidate, underlyingCounit, unitSummandRetract, underlying]

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
    (Z : CategoryTheory.Center C.Obj) :
    unitCandidate C Z ≫ (underlyingCounit C).app Z.1 = 𝟙 Z.1 := by
  rw [unitCandidate_counit_component]
  let A := simples C (unitIndex C)
  let e : A ≅ 𝟙_ C.Obj := Classical.choice (unitIndex_iso C)
  let d : Aᘁ ≅ 𝟙_ C.Obj := Dimensions.rightDualIsoMap e.symm ≪≫ Dimensions.rightDualUnitIso
  have hn := Z.2.naturality e.hom
  have hc := coevaluation_iso_unit C e
  change (η_ A Aᘁ ≫ (e.hom ⊗ₘ d.hom)) = (ρ_ (𝟙_ C.Obj)).inv at hc
  change ((ρ_ Z.1).inv ≫ (Z.1 ◁ η_ A Aᘁ) ≫ (α_ Z.1 A Aᘁ).inv ≫
    ((Z.2.β A).hom ▷ Aᘁ)) ≫
      (((e ⊗ᵢ Iso.refl Z.1) ⊗ᵢ d) ≪≫
        ((λ_ Z.1) ⊗ᵢ Iso.refl (𝟙_ C.Obj)) ≪≫ ρ_ Z.1).hom = 𝟙 Z.1
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, tensorHom_def,
    whiskerLeft_id, Category.comp_id, Category.assoc]
  rw [← comp_whiskerRight_assoc, ← hn]
  rw [comp_whiskerRight_assoc, ← associator_inv_naturality_middle_assoc]
  rw [← whiskerLeft_comp_assoc]
  rw [CentreRigid.halfBraiding_unit Z]
  simp only [comp_whiskerRight, Category.assoc]
  rw [triangle_assoc_comp_right_assoc, ← whisker_exchange_assoc]
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  have hunit : η_ A Aᘁ ≫ (e.hom ▷ Aᘁ) ≫ (λ_ Aᘁ).hom ≫ d.hom = 𝟙 (𝟙_ C.Obj) := by
    rw [← leftUnitor_naturality, ← tensorHom_def_assoc, ← Category.assoc, hc]
    monoidal_coherence
  simp only [← whiskerLeft_comp_assoc]
  simp only [Category.assoc] at hunit ⊢
  rw [hunit, whiskerLeft_id]
  simp

end PropertyF.Ground.CentreInduction

end

/-! Assembly of the induction adjunction from a half-braiding and its two
remaining coherence obligations. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
/-- A half-braiding on each underlying induction sum, natural in the
middle factor, lifts the underlying induction functor to the actual centre. -/
def inductionOfHalfBraiding (C : BraidedFusionCategory.{v,u})
    (b : ∀ X : C.Obj, HalfBraiding (underlying C X))
    (hb : ∀ {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj),
      ((underlyingFunctor C).map f ▷ T) ≫ ((b Y).β T).hom =
        ((b X).β T).hom ≫ (T ◁ (underlyingFunctor C).map f)) :
    C.Obj ⥤ CategoryTheory.Center C.Obj where
  obj X := ⟨underlying C X, b X⟩
  map f := ⟨(underlyingFunctor C).map f, hb f⟩
  map_id X := by
    apply CategoryTheory.Center.ext
    change (underlyingFunctor C).map (𝟙 X) = 𝟙 ((underlyingFunctor C).obj X)
    exact (underlyingFunctor C).map_id X
  map_comp f g := by apply CategoryTheory.Center.ext; simp

set_option backward.isDefEq.respectTransparency false in
/-- If the candidate unit is central for the proposed half-braiding, it lifts
to a natural transformation in the centre. -/
def inductionUnitOfCentrality (C : BraidedFusionCategory.{v,u})
    (b : ∀ X : C.Obj, HalfBraiding (underlying C X))
    (hb : ∀ {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj),
      ((underlyingFunctor C).map f ▷ T) ≫ ((b Y).β T).hom =
        ((b X).β T).hom ≫ (T ◁ (underlyingFunctor C).map f))
    (hunit : ∀ (Z : CategoryTheory.Center C.Obj) (T : C.Obj),
      (unitCandidate C Z ▷ T) ≫ ((b Z.1).β T).hom =
        (Z.2.β T).hom ≫ (T ◁ unitCandidate C Z)) :
    𝟭 (CategoryTheory.Center C.Obj) ⟶
      CategoryTheory.Center.forget C.Obj ⋙ inductionOfHalfBraiding C b hb where
  app Z := ⟨unitCandidate C Z, hunit Z⟩
  naturality {X Y} f := by
    apply CategoryTheory.Center.ext
    exact (unitCandidateNatural C).naturality f

set_option backward.isDefEq.respectTransparency false in
/-- A proposed induction half-braiding and its central unit give the
adjunction once the explicit second triangle is established. The first
triangle has already been proved from the actual half-braidings of centre
objects. Neither the proposed half-braiding, centrality, nor the second
triangle is assumed to exist by the ground target. -/
def adjunctionOfHalfBraiding (C : BraidedFusionCategory.{v,u})
    (b : ∀ X : C.Obj, HalfBraiding (underlying C X))
    (hb : ∀ {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj),
      ((underlyingFunctor C).map f ▷ T) ≫ ((b Y).β T).hom =
        ((b X).β T).hom ≫ (T ◁ (underlyingFunctor C).map f))
    (hunit : ∀ (Z : CategoryTheory.Center C.Obj) (T : C.Obj),
      (unitCandidate C Z ▷ T) ≫ ((b Z.1).β T).hom =
        (Z.2.β T).hom ≫ (T ◁ unitCandidate C Z))
    (htriangle : ∀ X : C.Obj,
      unitCandidate C ((inductionOfHalfBraiding C b hb).obj X) ≫
        (underlyingFunctor C).map ((underlyingCounit C).app X) = 𝟙 (underlying C X)) :
    CategoryTheory.Center.forget C.Obj ⊣ inductionOfHalfBraiding C b hb where
  unit := inductionUnitOfCentrality C b hb hunit
  counit := underlyingCounit C
  left_triangle_components Z := unitCandidate_counit C Z
  right_triangle_components X := by
    apply CategoryTheory.Center.ext
    exact htriangle X


set_option backward.isDefEq.respectTransparency false in
/-- The remaining induction triangle is determined by finitely many matrix
entries against the simple summands of the underlying induction object. -/
theorem secondTriangle_of_matrix_entries (C : BraidedFusionCategory.{v,u})
    (b : ∀ X : C.Obj, HalfBraiding (underlying C X))
    (hb : ∀ {X Y : C.Obj} (f : X ⟶ Y) (T : C.Obj),
      ((underlyingFunctor C).map f ▷ T) ≫ ((b Y).β T).hom =
        ((b X).β T).hom ≫ (T ◁ (underlyingFunctor C).map f))
    (hentries : ∀ (X : C.Obj) (i j : Fin (rank C)),
      let V : Fin (rank C) → C.Obj := fun k => (simples C k ⊗ X) ⊗ (simples C k)ᘁ
      biproduct.ι V i ≫
        (unitCandidate C ((inductionOfHalfBraiding C b hb).obj X) ≫
          (underlyingFunctor C).map ((underlyingCounit C).app X)) ≫ biproduct.π V j =
        biproduct.ι V i ≫ biproduct.π V j) :
    ∀ X : C.Obj,
      unitCandidate C ((inductionOfHalfBraiding C b hb).obj X) ≫
        (underlyingFunctor C).map ((underlyingCounit C).app X) = 𝟙 (underlying C X) := by
  intro X
  apply biproduct.hom_ext'
  intro i
  apply biproduct.hom_ext
  intro j
  simpa [underlying, Category.assoc] using hentries X i j

end PropertyF.Ground.CentreInduction
