module
public import PropertyF.Ground.Dimensions.DoubleDualMonoidal
public import PropertyF.Ground.Dimensions.FourthDualUnit
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Dimensions.SimpleScalars
public import PropertyF.Ground.Fusion.Agreement
public import PropertyF.Ground.Dimensions.ENOMatrices

/-! # Double-dual pairings and pivotal duality

Tensor pairings satisfy the triangle identities and give the double-dual evaluation and coevaluation laws.
Pivotal duality characterizes spherical structures by real simple dimensions.

## Main results

* `tensorPairing_coevaluation_evaluation`: closes the middle pair of a tensor-product coevaluation.
* `tensorPairing_evaluation_coevaluation`: gives the dual evaluation identity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]
variable (X : C)
omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Closing the middle dual pair in the tensor-product coevaluation recovers
the coevaluation of the right dual. -/
theorem tensorPairing_coevaluation_evaluation [HasRightDual X] [HasRightDual (Xᘁ)] :
    let W := (Xᘁ) ⊗ X
    let V := (Xᘁ) ⊗ ((Xᘁ)ᘁ)
    letI : ExactPairing W V := ExactPairing.tensor
    η_ W V ≫ (ε_ X (Xᘁ) ▷ V) ≫ (λ_ V).hom = η_ (Xᘁ) ((Xᘁ)ᘁ) := by
  dsimp only
  rw [ExactPairing.tensor_coevaluation]
  calc
    _ = η_ (Xᘁ) ((Xᘁ)ᘁ) ⊗≫
      (((Xᘁ) ◁ η_ X (Xᘁ) ≫ (α_ (Xᘁ) X (Xᘁ)).inv ≫ ε_ X (Xᘁ) ▷ (Xᘁ)) ▷ ((Xᘁ)ᘁ)) ⊗≫ 𝟙 _ := by
        simp only [comp_whiskerRight]
        monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation]
      monoidal
set_option backward.isDefEq.respectTransparency false in
/-- Dualizing evaluation and transporting the dual of a tensor product gives
the coevaluation of the dual object. -/
theorem rightDualEvaluation_coevaluation :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    (rightDualUnitIso (C := C)).inv ≫ ((ε_ X (Xᘁ))ᘁ) ≫
      (rightDualTensorIso (Xᘁ) X).hom = η_ (Xᘁ) ((Xᘁ)ᘁ) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let W := (Xᘁ) ⊗ X
  let V := (Xᘁ) ⊗ ((Xᘁ)ᘁ)
  let : HasRightDual W := RightRigidCategory.rightDual W
  let r : Iᘁ ≅ I := rightDualUnitIso
  let t : Wᘁ ≅ V := rightDualTensorIso (Xᘁ) X
  let q : ExactPairing W V := ExactPairing.tensor
  have hu := coevaluation_rightDualIso_inv
    (@HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
    (exactPairingUnit (C := C))
  change (ρ_ I).inv ≫ I ◁ r.inv = η_ I (Iᘁ) at hu
  have ht := coevaluation_rightDualIso
    (@HasRightDual.exact C _ _ W (RightRigidCategory.rightDual W)) q
  change η_ W (Wᘁ) ≫ W ◁ t.hom = @ExactPairing.coevaluation C _ _ W V q at ht
  have hm := coevaluation_comp_rightAdjointMate (ε_ X (Xᘁ))
  change η_ I (Iᘁ) ≫ I ◁ ((ε_ X (Xᘁ))ᘁ) =
    η_ W (Wᘁ) ≫ (ε_ X (Xᘁ)) ▷ (Wᘁ) at hm
  calc
    _ = ((ρ_ I).inv ≫ I ◁ r.inv ≫ I ◁ ((ε_ X (Xᘁ))ᘁ) ≫ I ◁ t.hom) ≫ (λ_ V).hom := by monoidal
    _ = (η_ W (Wᘁ) ≫ (ε_ X (Xᘁ)) ▷ (Wᘁ)) ≫ I ◁ t.hom ≫ (λ_ V).hom := by
      simpa only [← Category.assoc, hu] using
        congrArg (fun f ↦ f ≫ I ◁ t.hom ≫ (λ_ V).hom) hm
    _ = @ExactPairing.coevaluation C _ _ W V q ≫ (ε_ X (Xᘁ) ▷ V) ≫ (λ_ V).hom := by
      rw [← ht]
      simp only [Category.assoc]
      rw [← whisker_exchange_assoc]
    _ = _ := tensorPairing_coevaluation_evaluation X
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C]
variable (X : C)
omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Closing the middle pair in a tensor-product evaluation leaves the outer evaluation. -/
theorem tensorPairing_evaluation_coevaluation [HasRightDual X] [HasRightDual (Xᘁ)] :
    let W := X ⊗ (Xᘁ)
    let V := ((Xᘁ)ᘁ) ⊗ (Xᘁ)
    letI : ExactPairing W V := ExactPairing.tensor
    (ρ_ V).inv ≫ V ◁ η_ X (Xᘁ) ≫ ε_ W V = ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
  dsimp only
  rw [ExactPairing.tensor_evaluation]
  calc
    _ = 𝟙 (((Xᘁ)ᘁ) ⊗ (Xᘁ)) ⊗≫
      (((Xᘁ)ᘁ) ◁ ((Xᘁ) ◁ η_ X (Xᘁ) ≫ (α_ (Xᘁ) X (Xᘁ)).inv ≫ ε_ X (Xᘁ) ▷ (Xᘁ))) ⊗≫
        ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
      simp only [whiskerLeft_comp]
      monoidal
    _ = _ := by
      rw [ExactPairing.coevaluation_evaluation]
      monoidal
set_option backward.isDefEq.respectTransparency false in
/-- Dualizing coevaluation gives the evaluation of the right dual. -/
theorem rightDualCoevaluation_evaluation :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    (rightDualTensorIso X (Xᘁ)).inv ≫ ((η_ X (Xᘁ))ᘁ) ≫
      (rightDualUnitIso (C := C)).hom = ε_ (Xᘁ) ((Xᘁ)ᘁ) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let W := X ⊗ (Xᘁ)
  let V := ((Xᘁ)ᘁ) ⊗ (Xᘁ)
  let : HasRightDual W := RightRigidCategory.rightDual W
  let r : Iᘁ ≅ I := rightDualUnitIso
  let t : Wᘁ ≅ V := rightDualTensorIso X (Xᘁ)
  let q : ExactPairing W V := ExactPairing.tensor
  have hu := rightDualIso_evaluation
    (@HasRightDual.exact C _ _ I (RightRigidCategory.rightDual I))
    (exactPairingUnit (C := C))
  change r.hom ▷ I ≫ (ρ_ I).hom = ε_ I (Iᘁ) at hu
  have ht := rightDualIso_inv_evaluation
    (@HasRightDual.exact C _ _ W (RightRigidCategory.rightDual W)) q
  change t.inv ▷ W ≫ ε_ W (Wᘁ) = @ExactPairing.evaluation C _ _ W V q at ht
  have hm := rightAdjointMate_comp_evaluation (η_ X (Xᘁ))
  change ((η_ X (Xᘁ))ᘁ) ▷ I ≫ ε_ I (Iᘁ) = Wᘁ ◁ η_ X (Xᘁ) ≫ ε_ W (Wᘁ) at hm
  change t.inv ≫ ((η_ X (Xᘁ))ᘁ) ≫ r.hom = _
  calc
    _ = (ρ_ V).inv ≫ t.inv ▷ I ≫ (((η_ X (Xᘁ))ᘁ) ▷ I ≫ ε_ I (Iᘁ)) := by
      rw [← hu]
      simp only [← Category.assoc, ← comp_whiskerRight]
      monoidal
    _ = (ρ_ V).inv ≫ t.inv ▷ I ≫ (Wᘁ ◁ η_ X (Xᘁ) ≫ ε_ W (Wᘁ)) :=
      congrArg (fun f ↦ (ρ_ V).inv ≫ t.inv ▷ I ≫ f) hm
    _ = (ρ_ V).inv ≫ V ◁ η_ X (Xᘁ) ≫ @ExactPairing.evaluation C _ _ W V q := by
      rw [← ht, whisker_exchange_assoc]
    _ = _ := tensorPairing_evaluation_coevaluation X
set_option backward.isDefEq.respectTransparency false in
/-- The canonical strong monoidal double-dual functor preserves evaluation. -/
theorem doubleDual_evaluation :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    (doubleDualTensorIso (Xᘁ) X).hom ≫ (((ε_ X (Xᘁ))ᘁ)ᘁ) ≫
      (doubleDualUnitIso (C := C)).inv = ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let W := (Xᘁ) ⊗ X
  let V := (Xᘁ) ⊗ ((Xᘁ)ᘁ)
  let : HasRightDual W := RightRigidCategory.rightDual W
  let : HasRightDual V := RightRigidCategory.rightDual V
  let r : Iᘁ ≅ I := rightDualUnitIso
  let t : Wᘁ ≅ V := rightDualTensorIso (Xᘁ) X
  let s : Vᘁ ≅ (((Xᘁ)ᘁ)ᘁ) ⊗ ((Xᘁ)ᘁ) := rightDualTensorIso (Xᘁ) ((Xᘁ)ᘁ)
  have hd := congrArg (fun f : I ⟶ V ↦ fᘁ) (rightDualEvaluation_coevaluation X)
  simp only [comp_rightAdjointMate] at hd
  change (s.inv ≫ t.homᘁ) ≫ (((ε_ X (Xᘁ))ᘁ)ᘁ) ≫ (r.invᘁ ≫ r.hom) = _
  simpa only [Category.assoc] using
    (congrArg (fun f ↦ s.inv ≫ f ≫ r.hom) hd).trans (rightDualCoevaluation_evaluation (Xᘁ))
set_option backward.isDefEq.respectTransparency false in
/-- The canonical strong monoidal double-dual functor preserves coevaluation. -/
theorem doubleDual_coevaluation :
    letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual (𝟙_ C)
    (doubleDualUnitIso (C := C)).hom ≫ (((η_ X (Xᘁ))ᘁ)ᘁ) ≫
      (doubleDualTensorIso X (Xᘁ)).inv = η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let W := X ⊗ (Xᘁ)
  let V := ((Xᘁ)ᘁ) ⊗ (Xᘁ)
  let : HasRightDual W := RightRigidCategory.rightDual W
  let : HasRightDual V := RightRigidCategory.rightDual V
  let r : Iᘁ ≅ I := rightDualUnitIso
  let t : Wᘁ ≅ V := rightDualTensorIso X (Xᘁ)
  let s : Vᘁ ≅ ((Xᘁ)ᘁ) ⊗ (((Xᘁ)ᘁ)ᘁ) := rightDualTensorIso ((Xᘁ)ᘁ) (Xᘁ)
  have hd := congrArg (fun f : V ⟶ I ↦ fᘁ) (rightDualCoevaluation_evaluation X)
  simp only [comp_rightAdjointMate] at hd
  change (r.inv ≫ r.homᘁ) ≫ (((η_ X (Xᘁ))ᘁ)ᘁ) ≫ (t.invᘁ ≫ s.hom) = _
  simpa only [Category.assoc] using
    (congrArg (fun f ↦ r.inv ≫ f ≫ s.hom) hd).trans (rightDualEvaluation_coevaluation (Xᘁ))
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
variable (p : PivotalStructure (C := C)) (X : C)
set_option backward.isDefEq.respectTransparency false in
/-- Every pivotal structure preserves evaluation. -/
theorem pivotal_evaluation :
    ((p.iso (Xᘁ)).hom ⊗ₘ (p.iso X).hom) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) = ε_ X (Xᘁ) := by
  let I := 𝟙_ C
  let : HasRightDual I := RightRigidCategory.rightDual I
  let W := (Xᘁ) ⊗ X
  let : HasRightDual W := RightRigidCategory.rightDual W
  have h := p.naturality (ε_ X (Xᘁ))
  change ε_ X (Xᘁ) ≫ (p.iso I).hom = (p.iso W).hom ≫ (((ε_ X (Xᘁ))ᘁ)ᘁ) at h
  rw [p.tensor, p.unit] at h
  rw [← doubleDual_evaluation X, ← Category.assoc, ← Category.assoc, ← h]
  simp
set_option backward.isDefEq.respectTransparency false in
/-- A pivotal component on a dual is the inverse dual of the original component. -/
theorem pivotal_dual :
    p.iso (Xᘁ) = (rightDualIsoMap (p.iso X)).symm :=
  Iso.ext <| show (p.iso (Xᘁ)).hom = ((p.iso X).inv)ᘁ from
    evaluation_ext (X := (Xᘁ)ᘁ) <| (cancel_epi ((Xᘁ) ◁ (p.iso X).hom)).1 <| by
      simpa only [tensorHom_def', Category.assoc] using
        (pivotal_evaluation p X).trans (evaluation_iso_map (p.iso X)).symm
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- A pivotal fusion category is spherical exactly when all simple dimensions are real. -/
theorem pivotal_spherical_iff_simple_dimensions_real
    (p : PivotalStructure (C := C.Obj)) :
    p.IsSpherical ↔ ∀ i, star (pivotalDimension C p (simples C i)) =
      pivotalDimension C p (simples C i) := by
  have hdual (i : Fin (rank C)) :
      unitScalar C (p.leftTrace (𝟙 (simples C i))) =
        star (pivotalDimension C p (simples C i)) := by
    rw [leftTrace_id, leftQuantumTrace_eq_rightDual, ← pivotal_dual, ← rightTrace_id]
    change pivotalDimension C p ((simples C i)ᘁ) = _
    rw [pivotalDimension_iso C p (rightDualLabelIso C i), pivotalDimension_dual_eq_conj]
  rw [isSpherical_iff_simple_dimensions]
  refine forall_congr' fun i ↦ ?_
  rw [← hdual i]
  simp only [pivotalDimension, unitScalar_eq_equiv, (unitScalarEquiv C).injective.eq_iff]
end PropertyF.Ground.Dimensions

end
