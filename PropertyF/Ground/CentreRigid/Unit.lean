module
public import PropertyF.Ground.Integrate.CenterDualMate

/-! Unit cases of the tensor law for the normalized dual crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreRigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

omit [RigidCategory C] in
/-- At the tensor unit, every underlying morphism intertwines normalized
crossings; this is the unit case of the evaluation and coevaluation equations. -/
theorem normalized_unit_intertwines {X Y : C} (f : X ⟶ Y) :
    (f ▷ (𝟙_ C)) ≫ (ρ_ Y).hom ≫ (λ_ Y).inv =
      (ρ_ X).hom ≫ (λ_ X).inv ≫ ((𝟙_ C) ◁ f) := by
  monoidal

set_option backward.isDefEq.respectTransparency false in
omit [RigidCategory C] in
/-- The half-braiding of every centre object has its forced unit component. -/
theorem halfBraiding_unit (Z : CategoryTheory.Center C) :
    (Z.2.β (𝟙_ C)).hom = (ρ_ Z.1).hom ≫ (λ_ Z.1).inv := by
  have h := congrArg CategoryTheory.Center.Hom.f
    (CategoryTheory.braiding_tensorUnit_right Z)
  simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.rightUnitor_hom_f,
    CategoryTheory.Center.leftUnitor_inv_f] at h
  exact h

omit [RigidCategory C] in
/-- Any underlying map between centre objects intertwines their
half-braidings at the tensor unit. -/
theorem centrality_at_unit (X Y : CategoryTheory.Center C) (f : X.1 ⟶ Y.1) :
    (f ▷ (𝟙_ C)) ≫ (Y.2.β (𝟙_ C)).hom =
      (X.2.β (𝟙_ C)).hom ≫ ((𝟙_ C) ◁ f) := by
  rw [halfBraiding_unit, halfBraiding_unit]
  simpa only [Category.assoc] using normalized_unit_intertwines f

end PropertyF.Ground.CentreRigid
