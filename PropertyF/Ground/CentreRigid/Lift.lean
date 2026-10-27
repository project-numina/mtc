module
public import PropertyF.Ground.Integrate.CenterDualMate

/-! Lifting the underlying duality to the actual centre. The stated crossing
coherence and intertwining equations are still open. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreRigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- If the normalized mate satisfies the half-braiding law, it defines an
object of the actual centre on the underlying right dual. -/
def dualObject (Z : CategoryTheory.Center C)
    (hTensor : ∀ U V : C, ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
        (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫
          (α_ _ _ _).inv) : CategoryTheory.Center C :=
  ⟨Z.1ᘁ, {
    β := fun U => (Integrate.dualCrossingIso Z).app U
    monoidal := hTensor
    naturality := fun f => Integrate.dualCrossing_natural Z f }⟩

set_option backward.isDefEq.respectTransparency false in
/-- Once the underlying duality maps intertwine the lifted half-braidings,
their triangle identities lift through the faithful forgetful functor. -/
@[instance_reducible] def liftedPairing (Z : CategoryTheory.Center C)
    (hTensor : ∀ U V : C, ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
        (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫
          (α_ _ _ _).inv)
    (hCo : ∀ U, ((η_ Z.1 Z.1ᘁ) ▷ U) ≫
      ((Z ⊗ dualObject Z hTensor).2.β U).hom =
      ((𝟙_ (CategoryTheory.Center C)).2.β U).hom ≫ (U ◁ η_ Z.1 Z.1ᘁ))
    (hEv : ∀ U, ((ε_ Z.1 Z.1ᘁ) ▷ U) ≫
      ((𝟙_ (CategoryTheory.Center C)).2.β U).hom =
      ((dualObject Z hTensor ⊗ Z).2.β U).hom ≫ (U ◁ ε_ Z.1 Z.1ᘁ)) :
    ExactPairing Z (dualObject Z hTensor) where
  coevaluation' := ⟨η_ Z.1 Z.1ᘁ, hCo⟩
  evaluation' := ⟨ε_ Z.1 Z.1ᘁ, hEv⟩
  coevaluation_evaluation' := by
    apply CategoryTheory.Center.ext
    simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.whiskerLeft_f,
      CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_inv_f,
      CategoryTheory.Center.rightUnitor_hom_f, CategoryTheory.Center.leftUnitor_inv_f,
]
    exact ExactPairing.coevaluation_evaluation Z.1 Z.1ᘁ
  evaluation_coevaluation' := by
    apply CategoryTheory.Center.ext
    simp only [CategoryTheory.Center.comp_f, CategoryTheory.Center.whiskerLeft_f,
      CategoryTheory.Center.whiskerRight_f, CategoryTheory.Center.associator_hom_f,
      CategoryTheory.Center.leftUnitor_hom_f, CategoryTheory.Center.rightUnitor_inv_f,
]
    exact ExactPairing.evaluation_coevaluation Z.1 Z.1ᘁ

/-- If the mate satisfies its tensor law and both duality maps are central for
every object, the actual centre is rigid. These coherence equations remain
explicit hypotheses. -/
@[instance_reducible] def rigidOfMateCoherence
    (h : ∀ Z : CategoryTheory.Center C,
      ∃ (hTensor : ∀ U V : C, ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom =
        (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
          (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫
            (α_ _ _ _).inv),
        (∀ U, ((η_ Z.1 Z.1ᘁ) ▷ U) ≫
          ((Z ⊗ dualObject Z hTensor).2.β U).hom =
          ((𝟙_ (CategoryTheory.Center C)).2.β U).hom ≫ (U ◁ η_ Z.1 Z.1ᘁ)) ∧
        (∀ U, ((ε_ Z.1 Z.1ᘁ) ▷ U) ≫
          ((𝟙_ (CategoryTheory.Center C)).2.β U).hom =
          ((dualObject Z hTensor ⊗ Z).2.β U).hom ≫ (U ◁ ε_ Z.1 Z.1ᘁ))) :
    RigidCategory (CategoryTheory.Center C) := by
  letI : RightRigidCategory (CategoryTheory.Center C) := {
    rightDual := fun Z => {
      rightDual := dualObject Z (Classical.choose (h Z))
      exact := liftedPairing Z (Classical.choose (h Z))
        (Classical.choose_spec (h Z)).1 (Classical.choose_spec (h Z)).2 } }
  exact BraidedCategory.rigidCategoryOfRightRigidCategory

end PropertyF.Ground.CentreRigid
