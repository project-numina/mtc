module
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Dimensions.SphericalCriterion
public import PropertyF.Ground.Dimensions.IntrinsicNonzero

/-! # Pivotal scalar twists

Scalar natural transformations twist pivotal structures and their simple dimensions.

## Main results

* `pivotalScalarTwist`: twists a pivotal structure by scalar natural data.
* `pivotalDimension_scalarTwist_simple`: computes the resulting dimensions of simples.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- Twist a pivotal structure by a fusion-compatible family of nonzero simple scalars. -/
def pivotalScalarTwist (C : BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (c : Fin (rank C) → ℂ)
    (hc : ∀ i, c i ≠ 0) (hunit : c (unitIndex C) = 1)
    (hmul : ∀ i j k, fusionCoeff C i j k ≠ 0 → c k = c i * c j) :
    PivotalStructure (C := C.Obj) where
  iso X := (simpleScalarNaturalIso C c hc).app X ≪≫ p.iso X
  naturality {X Y} f := by
    simp only [Iso.trans_hom, ← Category.assoc]
    have hn := (simpleScalarNaturalIso C c hc).hom.naturality f
    simp only [Functor.id_map] at hn
    change f ≫ ((simpleScalarNaturalIso C c hc).app Y).hom =
      ((simpleScalarNaturalIso C c hc).app X).hom ≫ f at hn
    rw [hn]
    simpa only [Category.assoc] using congrArg
      (fun h => ((simpleScalarNaturalIso C c hc).app X).hom ≫ h) (p.naturality f)
  tensor X Y := by
    simp only [Iso.trans_hom, p.tensor]
    change (simpleScalarNatural C c).app (X ⊗ Y) ≫
      ((p.iso X).hom ⊗ₘ (p.iso Y).hom) ≫ (doubleDualTensorIso X Y).hom = _
    rw [simpleScalarNatural_tensor C c hmul, ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rfl
  unit := by
    simp only [Iso.trans_hom, p.unit]
    change (simpleScalarNatural C c).app (𝟙_ C.Obj) ≫ _ = _
    simp only [simpleScalarNatural_unit C c hunit, Category.id_comp]

/-- Twisting rescales each simple pivotal dimension by the chosen scalar. -/
theorem pivotalDimension_scalarTwist_simple
    (p : PivotalStructure (C := C.Obj)) (c : Fin (rank C) → ℂ)
    (hc : ∀ i, c i ≠ 0) (hunit : c (unitIndex C) = 1)
    (hmul : ∀ i j k, fusionCoeff C i j k ≠ 0 → c k = c i * c j)
    (i : Fin (rank C)) :
    pivotalDimension C (pivotalScalarTwist C p c hc hunit hmul) (simples C i) =
      c i * pivotalDimension C p (simples C i) := by
  unfold pivotalDimension
  have ht : (pivotalScalarTwist C p c hc hunit hmul).rightTrace
      (𝟙 (simples C i)) = c i • p.rightTrace (𝟙 (simples C i)) := by
    rw [rightTrace_id, rightTrace_id]
    apply rightQuantumTrace_smul_hom
    change ((simpleScalarNaturalIso C c hc).app (simples C i)).hom ≫ _ = _
    rw [simpleScalarNaturalIso_app_simple]
    simp
  rw [ht]
  simp only [← groundUnitScalarEquiv_apply, map_smul, smul_eq_mul]

end PropertyF.Ground.Dimensions
