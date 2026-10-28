module
public import PropertyF.Ground.CentreInduction.PositivePivotal
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Dimensions.DoubleDualMonoidal
public import PropertyF.Ground.Dimensions.DefectExtension
public import PropertyF.Ground.CentreIntegrate.TwistBalancing
public import PropertyF.Ground.Dimensions.MonodromyTensorCap

open PropertyF.Ground.Dimensions

/-! The Drinfeld map satisfies its tensor coherence law. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u

/-- The Drinfeld map satisfies tensor coherence in a braided rigid category. -/
theorem drinfeld_tensor {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] [RightRigidCategory D] (X Y : D) :
    Modular.doubleBraiding X Y ≫ (drinfeldIso (X ⊗ Y)).hom =
      ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom) ≫ (doubleDualTensorIso X Y).hom :=
  CentreIntegrate.drinfeld_tensor_of_pairing_cap (fun Z ↦ drinfeldIso Z)
    (drinfeld_eval (X ⊗ Y)) (drinfeld_tensor_pairing_cap X Y)

end PropertyF.Ground
end

section
/-! The dual functors transport monodromy through their tensorators. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
-- Monodromy is the double braiding.
local notation "M" => Modular.doubleBraiding
variable {X Y : D} [HasRightDual X] [HasRightDual Y] [HasRightDual (X ⊗ Y)]

/-- Right duality reverses the tensor factors of mixed monodromy. -/
theorem rightDualTensorIso_monodromy :
    (M X Y)ᘁ ≫ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso X Y).hom ≫ M (Yᘁ) (Xᘁ) :=
  let : HasRightDual (Y ⊗ X) := hasRightDualTensor
  by simp [Modular.doubleBraiding, comp_rightAdjointMate, Category.assoc,
    rightDualTensorIso_braiding]

/-- Inverse dual tensor comparison also transports monodromy. -/
theorem rightDualTensorIso_inv_monodromy :
    (rightDualTensorIso X Y).inv ≫ (M X Y)ᘁ =
      M (Yᘁ) (Xᘁ) ≫ (rightDualTensorIso X Y).inv :=
  (CommSq.vert_inv ⟨rightDualTensorIso_monodromy⟩).w.symm

end PropertyF.Ground.CentreInduction

end
end

/-! Monoidality of the fourth dual from the Drinfeld tensor law. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] (X Y : D)
-- The Drinfeld isomorphism and the double-dual tensor comparison.
local notation "d" => drinfeldIso
local notation "μ₂" => doubleDualTensorIso
local notation "d₄" => fourthDualIso
-- Monodromy is the double braiding.
local notation "M" => Modular.doubleBraiding

/-- The inverse Drinfeld map satisfies the reversed tensor identity. -/
theorem drinfeld_tensor_inverse :
    (d (X ⊗ Y)).inv = (μ₂ X Y).inv ≫
      ((d X).inv ⊗ₘ (d Y).inv) ≫ M X Y := by
  rw [← tensorIso_inv, Iso.eq_inv_comp, Iso.eq_inv_comp, ← Category.assoc,
    Iso.comp_inv_eq, drinfeld_tensor, tensorIso_hom]

omit [RightRigidCategory D] in
/-- Formula for transporting the inverse Drinfeld map through an isomorphism. -/
theorem drinfeld_inv_natural {A B : D} [HasRightDual A] [HasRightDual (Aᘁ)]
    [HasRightDual B] [HasRightDual (Bᘁ)] (t : A ≅ B) :
    (d A).inv = (((t.homᘁ)ᘁ) ≫ (d B).inv) ≫ t.inv := by
  rw [Iso.eq_comp_inv, Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
    drinfeldIso_natural]

/-- The inverse dual Drinfeld map after the tensorator, in terms of the
reversed dual factors and monodromy. -/
theorem drinfeld_inv_dual_tensor :
    (μ₂ X Y).hom ≫ ((d ((X ⊗ Y)ᘁ)).invᘁ) =
      M ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) ≫ (((d (Xᘁ)).invᘁ) ⊗ₘ ((d (Yᘁ)).invᘁ)) ≫
        (μ₂ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫ (((μ₂ X Y).homᘁ)ᘁ) := by
  let t := rightDualTensorIso X Y
  let f := (d (Yᘁ)).inv
  let g := (d (Xᘁ)).inv
  have hn' := congrArg (fun z => rightAdjointMate z) (drinfeld_inv_natural t)
  have hi' := congrArg (fun z => rightAdjointMate z) (drinfeld_tensor_inverse (Yᘁ : D) (Xᘁ : D))
  simp only [comp_rightAdjointMate] at hn' hi'
  simp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    rightDualIsoMap, Category.assoc]
  change (rightDualTensorIso (Yᘁ) (Xᘁ)).inv ≫ t.homᘁ ≫
    (d ((X ⊗ Y)ᘁ)).invᘁ = _
  simp only [hn', hi', comp_rightAdjointMate, Category.assoc]
  rw [← Category.assoc (t.homᘁ), ← comp_rightAdjointMate, Iso.inv_hom_id,
    rightAdjointMate_id, Category.id_comp]
  rw [reassoc_of% rightDualTensorIso_inv_monodromy,
    ← reassoc_of% rightDualTensorIso_inv_natural f g]
  simp only [doubleDualTensorIso, rightDualIsoMap, Iso.trans_inv, Iso.symm_inv,
    comp_rightAdjointMate, Category.assoc, f, g, t]

/-- The Drinfeld tensor law forces monoidality of the canonical fourth-dual map. -/
theorem fourthDualIso_tensor :
    (d₄ (X ⊗ Y)).hom =
      ((d₄ X).hom ⊗ₘ (d₄ Y).hom) ≫
        (μ₂ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫ (((μ₂ X Y).homᘁ)ᘁ) := by
  let m : X ⊗ Y ≅ X ⊗ Y := (β_ X Y) ≪≫ (β_ Y X)
  simp only [fourthDualIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap]
  rw [(Iso.eq_inv_comp m).2 (drinfeld_tensor X Y)]
  rw [Category.assoc, Category.assoc, drinfeld_inv_dual_tensor X Y]
  simp only [← tensorHom_comp_tensorHom_assoc, ← Category.assoc]
  rw [Category.assoc m.inv,
    ← Modular.doubleBraiding_natural (d X).hom (d Y).hom]
  simp only [Category.assoc, show M X Y = m.hom from rfl,
    Iso.inv_hom_id_assoc]

end PropertyF.Ground.CentreInduction

end

/-! The Drinfeld tensor law and its pseudo-unitary consequences. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u

/-- Every pseudo-unitary braided fusion category has a positive spherical
structure with its actual FP dimensions, without any pivotal premise. -/
theorem positive_spherical_of_pseudoUnitary {C : BraidedFusionCategory.{v,u}}
    (hpu : PseudoUnitary C) :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ PivotalHasFPDimensions C p :=
  let h (i j : Fin (rank C)) := fourthDualIso_tensor (simples C i) (simples C j)
  positive_spherical_of_simple_fourth_and_reciprocity h (trace_reciprocity_of_fourth_dual h) hpu

end PropertyF.Ground.CentreInduction
