module
public import PropertyF.Ground.Dimensions.DoubleDualPairing
public import PropertyF.Ground.Dimensions.FourthDualUnit
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.ComplexSaturation

/-! # Pivotal structures and pseudo-unitarity

Duality and reality properties of pivotal dimensions characterize spherical structures.

## Main results

* `pivotal_dual`: relates pivotal components on dual objects.
* `pivotal_spherical_iff_simple_dimensions_real`: characterizes spherical structures.
-/

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
  rw [← (rightAdjointMate_comp_evaluation (p.iso X).hom)] at h
  rw [← comp_whiskerRight_assoc] at h
  have hk : (p.iso (Xᘁ)).hom ≫ ((p.iso X).hom)ᘁ = 𝟙 (Xᘁ) := by
    apply evaluation_ext (X := X)
    simpa only [id_whiskerRight, Category.id_comp] using h
  calc
    _ = (p.iso (Xᘁ)).hom ≫ (((p.iso X).hom)ᘁ ≫ ((p.iso X).inv)ᘁ) := by
      rw [← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id, Category.comp_id]
    _ = _ := by rw [← Category.assoc, hk, Category.id_comp]
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The left dimension is the right dimension of the dual object. -/
theorem pivotal_leftTrace_id_eq_rightTrace_dual {C : Type u} [Category.{v} C]
    [MonoidalCategory C] [RigidCategory C] (p : PivotalStructure (C := C)) (X : C) :
    p.leftTrace (𝟙 X) = p.rightTrace (𝟙 (Xᘁ)) :=
  by rw [leftTrace_id, rightTrace_id, pivotal_dual, leftQuantumTrace_eq_rightDual]

/-- A pivotal fusion category is spherical exactly when all simple dimensions are real. -/
theorem pivotal_spherical_iff_simple_dimensions_real
    (p : PivotalStructure (C := C.Obj)) :
    p.IsSpherical ↔ ∀ i, star (pivotalDimension C p (simples C i)) =
      pivotalDimension C p (simples C i) := by
  have hdual (i : Fin (rank C)) :
      unitScalar C (p.leftTrace (𝟙 (simples C i))) =
        star (pivotalDimension C p (simples C i)) := by
    rw [pivotal_leftTrace_id_eq_rightTrace_dual]
    change pivotalDimension C p ((simples C i)ᘁ) = _
    rw [pivotalDimension_iso C p (rightDualLabelIso C i), pivotalDimension_dual_eq_conj]
  rw [isSpherical_iff_simple_dimensions]
  constructor
  · intro h i
    rw [← hdual, h i]
    rfl
  · intro h i
    apply (unitScalarEquiv C).injective
    simpa only [← unitScalar_eq_equiv, pivotalDimension] using
      (hdual i).trans (h i)
end PropertyF.Ground.Dimensions

end
