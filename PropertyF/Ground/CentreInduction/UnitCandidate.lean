module
public import PropertyF.Ground.CentreInduction.UnitSummand
public import PropertyF.Ground.Centre.Linear

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
  simp [unitCandidate, underlyingCounit, unitSummandRetract, underlying, Category.assoc]

end PropertyF.Ground.CentreInduction
