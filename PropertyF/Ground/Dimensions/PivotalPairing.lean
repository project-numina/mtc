module
public import PropertyF.Ground.Dimensions.SphericalPivotalDual

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- A double-dual isomorphism and its inverse dual transport coevaluation. -/
theorem doubleDualIso_coevaluation (X : C) (a : X ≅ (Xᘁ)ᘁ) :
    η_ X (Xᘁ) ≫ (a.hom ⊗ₘ (rightDualIsoMap a).symm.hom) =
      η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) := by
  change η_ X (Xᘁ) ≫ (a.hom ⊗ₘ (a.invᘁ)) = η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)
  simp only [tensorHom_def]
  have h := coevaluation_comp_rightAdjointMate a.inv
  calc
    _ = η_ X (Xᘁ) ≫ X ◁ (a.invᘁ) ≫ a.hom ▷ (((Xᘁ)ᘁ)ᘁ) := by
      simpa only [Category.assoc] using
        (congrArg (fun z => η_ X (Xᘁ) ≫ z) (whisker_exchange a.hom (a.invᘁ))).symm
    _ = η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) ≫ a.inv ▷ (((Xᘁ)ᘁ)ᘁ) ≫ a.hom ▷ (((Xᘁ)ᘁ)ᘁ) := by
      simpa only [Category.assoc] using congrArg (fun z => z ≫ a.hom ▷ (((Xᘁ)ᘁ)ᘁ)) h
    _ = _ := by simp only [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight,
      Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- A double-dual isomorphism and its inverse dual transport evaluation. -/
theorem doubleDualIso_evaluation (X : C) (a : X ≅ (Xᘁ)ᘁ) :
    ((rightDualIsoMap a).symm.hom ⊗ₘ a.hom) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) =
      ε_ X (Xᘁ) := by
  change ((a.invᘁ) ⊗ₘ a.hom) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) = ε_ X (Xᘁ)
  simp only [tensorHom_def]
  have h := rightAdjointMate_comp_evaluation a.inv
  calc
    _ = (Xᘁ) ◁ a.hom ≫ ((a.invᘁ) ▷ ((Xᘁ)ᘁ) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)) := by
      simpa only [Category.assoc] using
        congrArg (fun z => z ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)) (whisker_exchange (a.invᘁ) a.hom).symm
    _ = (Xᘁ) ◁ a.hom ≫ ((Xᘁ) ◁ a.inv ≫ ε_ X (Xᘁ)) := by rw [h]
    _ = _ := by simp only [← Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id,
      whiskerLeft_id, Category.id_comp]

/-- A real spherical pivotal structure preserves coevaluation on every object. -/
theorem real_spherical_pivotal_coevaluation (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank D) → ℝ)
    (hreal : ∀ i, pivotalDimension D p (Ground.simples D i) = (d i : ℂ))
    (X : D.Obj) :
    η_ X (Xᘁ) ≫ ((p.iso X).hom ⊗ₘ (p.iso (Xᘁ)).hom) =
      η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) := by
  rw [real_spherical_pivotal_dual D p hp d hreal X]
  exact doubleDualIso_coevaluation X (p.iso X)

/-- A real spherical pivotal structure preserves evaluation on every object. -/
theorem real_spherical_pivotal_evaluation (D : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := D.Obj)) (hp : p.IsSpherical)
    (d : Fin (Ground.rank D) → ℝ)
    (hreal : ∀ i, pivotalDimension D p (Ground.simples D i) = (d i : ℂ))
    (X : D.Obj) :
    ((p.iso (Xᘁ)).hom ⊗ₘ (p.iso X).hom) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) =
      ε_ X (Xᘁ) := by
  rw [real_spherical_pivotal_dual D p hp d hreal X]
  exact doubleDualIso_evaluation X (p.iso X)
end PropertyF.Ground.Dimensions
