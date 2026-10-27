module
public import PropertyF.Ground.Dimensions.DoubleDualPairing

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Every pivotal structure preserves evaluation. -/
theorem pivotal_evaluation {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (p : PivotalStructure (C := C)) (X : C) :
    ((p.iso (Xᘁ)).hom ⊗ₘ (p.iso X).hom) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) = ε_ X (Xᘁ) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let W := (Xᘁ) ⊗ X
  let : HasRightDual W := RightRigidCategory.rightDual W
  have h := p.naturality (ε_ X (Xᘁ))
  change ε_ X (Xᘁ) ≫ (p.iso I).hom = (p.iso W).hom ≫ (((ε_ X (Xᘁ))ᘁ)ᘁ) at h
  rw [p.tensor, p.unit] at h
  have he := doubleDual_evaluation X
  calc
    _ = ((p.iso (Xᘁ)).hom ⊗ₘ (p.iso X).hom) ≫
      ((doubleDualTensorIso (Xᘁ) X).hom ≫ (((ε_ X (Xᘁ))ᘁ)ᘁ) ≫
        (doubleDualUnitIso (C := C)).inv) := by rw [he]
    _ = ε_ X (Xᘁ) := by
      rw [← Category.assoc, ← Category.assoc, ← h]
      simp
set_option backward.isDefEq.respectTransparency false in
/-- A pivotal component on a dual is the inverse dual of the original component. -/
theorem pivotal_dual {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (p : PivotalStructure (C := C)) (X : C) :
    p.iso (Xᘁ) = (rightDualIsoMap (p.iso X)).symm := by
  apply Iso.ext
  change (p.iso (Xᘁ)).hom = ((p.iso X).inv)ᘁ
  have h := pivotal_evaluation p X
  simp only [tensorHom_def, Category.assoc] at h
  have hm := rightAdjointMate_comp_evaluation (p.iso X).hom
  rw [← hm] at h
  rw [← comp_whiskerRight_assoc] at h
  have hh := congrArg (tensorRightHomEquiv (Xᘁ) X (Xᘁ) (𝟙_ C)) h
  simp only [tensorRightHomEquiv_whiskerRight_comp_evaluation] at hh
  have hi := tensorRightHomEquiv_whiskerRight_comp_evaluation (X := X) (Y := (Xᘁ)) (𝟙 (Xᘁ))
  simp only [id_whiskerRight, Category.id_comp] at hi
  rw [hi] at hh
  have hk : (p.iso (Xᘁ)).hom ≫ ((p.iso X).hom)ᘁ = 𝟙 (Xᘁ) := by
    apply (cancel_mono (λ_ (Xᘁ)).inv).1
    simpa only [id_whiskerRight, Category.id_comp] using hh
  calc
    _ = (p.iso (Xᘁ)).hom ≫ (((p.iso X).hom)ᘁ ≫ ((p.iso X).inv)ᘁ) := by
      rw [← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id, Category.comp_id]
    _ = _ := by rw [← Category.assoc, hk, Category.id_comp]
/-- Every pivotal structure also preserves coevaluation. -/
theorem pivotal_coevaluation {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RightRigidCategory C] (p : PivotalStructure (C := C)) (X : C) :
    η_ X (Xᘁ) ≫ ((p.iso X).hom ⊗ₘ (p.iso (Xᘁ)).hom) =
      η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) := by
  rw [pivotal_dual p X]
  exact doubleDualIso_coevaluation X (p.iso X)

set_option backward.isDefEq.respectTransparency false in
/-- In a spherical category, taking the right dual preserves pivotal traces. -/
theorem spherical_rightTrace_dual {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RigidCategory C] (p : PivotalStructure (C := C))
    (hp : p.IsSpherical) {X : C} (f : X ⟶ X) : p.rightTrace (fᘁ) = p.rightTrace f := by
  have h := leftTrace_eq_rightTraceWith_dual p f
  rw [← pivotal_dual p X] at h
  change p.leftTrace f = p.rightTrace (fᘁ) at h
  exact h.symm.trans (hp X f)
end PropertyF.Ground.Dimensions
