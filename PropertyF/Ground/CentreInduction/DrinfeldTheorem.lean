module
public import PropertyF.Ground.CentreInduction.PositivePivotal
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Dimensions.DoubleDualMonoidal
public import PropertyF.Ground.CentreCabling.CentralityClosure
public import PropertyF.Ground.Dimensions.DefectExtension
public import PropertyF.Ground.CentreIntegrate.TwistBalancing
public import PropertyF.Ground.Dimensions.MonodromyTensorCap

open PropertyF.Ground.Dimensions

/-! The Drinfeld map satisfies its tensor coherence law. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u

/-- The actual Drinfeld map has the tensor coherence law in any braided
fusion category. -/
theorem drinfeld_tensor (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    Modular.doubleBraiding X Y ≫ (doubleDualIso C (X ⊗ Y)).hom =
      ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ≫
        (doubleDualTensorIso X Y).hom :=
  CentreIntegrate.drinfeld_tensor_of_pairing_cap (doubleDualIso C)
    (drinfeld_eval C (X ⊗ Y)) (drinfeld_tensor_pairing_cap C X Y)

end PropertyF.Ground
end

section
/-! The dual functors transport monodromy through their tensorators. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D] [RightRigidCategory D]

/-- Right duality reverses the tensor factors of mixed monodromy. -/
theorem rightDualTensorIso_monodromy {X Y : D} :
    (Modular.doubleBraiding X Y)ᘁ ≫ (rightDualTensorIso X Y).hom =
      (rightDualTensorIso X Y).hom ≫ Modular.doubleBraiding (Yᘁ) (Xᘁ) := by
  simp [Modular.doubleBraiding, comp_rightAdjointMate, Category.assoc,
    rightDualTensorIso_braiding]

end PropertyF.Ground.CentreInduction

end
end

/-! Monoidality of the fourth dual from the Drinfeld tensor law. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj)

/-- The inverse Drinfeld map satisfies the reversed tensor identity. -/
theorem drinfeld_tensor_inverse :
    (doubleDualIso C (X ⊗ Y)).inv = (doubleDualTensorIso X Y).inv ≫
      ((doubleDualIso C X).inv ⊗ₘ (doubleDualIso C Y).inv) ≫ Modular.doubleBraiding X Y := by
  change (doubleDualIso C (X ⊗ Y)).inv =
    (doubleDualTensorIso X Y).inv ≫
      (doubleDualIso C X ⊗ᵢ doubleDualIso C Y).inv ≫ Modular.doubleBraiding X Y
  rw [Iso.eq_inv_comp, Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (drinfeld_tensor C X Y).symm

/-- Formula for transporting the inverse Drinfeld map through an isomorphism. -/
theorem drinfeld_inv_natural {A B : C.Obj} (t : A ≅ B) :
    (doubleDualIso C A).inv = (((t.homᘁ)ᘁ) ≫ (doubleDualIso C B).inv) ≫ t.inv := by
  rw [Iso.eq_comp_inv, Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact doubleDualIso_natural C t.hom

/-- The inverse dual Drinfeld map after the tensorator, in terms of the
reversed dual factors and monodromy. -/
theorem drinfeld_inv_dual_tensor :
    (doubleDualTensorIso X Y).hom ≫
      ((doubleDualIso C ((X ⊗ Y)ᘁ)).invᘁ) =
    Modular.doubleBraiding ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) ≫
      (((doubleDualIso C (Xᘁ)).invᘁ) ⊗ₘ ((doubleDualIso C (Yᘁ)).invᘁ)) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫ (((doubleDualTensorIso X Y).homᘁ)ᘁ) := by
  let t := rightDualTensorIso X Y
  let f := (doubleDualIso C (Yᘁ)).inv
  let g := (doubleDualIso C (Xᘁ)).inv
  have hn' := congrArg (fun z => rightAdjointMate z) (drinfeld_inv_natural C t)
  have hi' := congrArg (fun z => rightAdjointMate z) (drinfeld_tensor_inverse C (Yᘁ) (Xᘁ))
  simp only [comp_rightAdjointMate] at hn' hi'
  have hm' : (rightDualTensorIso (Yᘁ) (Xᘁ)).inv ≫
      ((Modular.doubleBraiding (Yᘁ) (Xᘁ))ᘁ) =
      Modular.doubleBraiding ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) ≫
        (rightDualTensorIso (Yᘁ) (Xᘁ)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact rightDualTensorIso_monodromy
  simp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    rightDualIsoMap, Category.assoc]
  change (rightDualTensorIso (Yᘁ) (Xᘁ)).inv ≫ t.homᘁ ≫
    (doubleDualIso C ((X ⊗ Y)ᘁ)).invᘁ = _
  rw [hn', hi']
  simp only [comp_rightAdjointMate, Category.assoc]
  rw [← Category.assoc (t.homᘁ), ← comp_rightAdjointMate, Iso.inv_hom_id,
    rightAdjointMate_id, Category.id_comp]
  rw [← Category.assoc (rightDualTensorIso (Yᘁ) (Xᘁ)).inv, hm']
  simp only [Category.assoc]
  rw [← Category.assoc (rightDualTensorIso (Yᘁ) (Xᘁ)).inv,
    ← rightDualTensorIso_inv_natural f g]
  simp only [Category.assoc]
  dsimp only [doubleDualTensorIso, rightDualIsoMap,
    Iso.trans_inv, Iso.symm_inv]
  simp only [comp_rightAdjointMate, Category.assoc, f, g, t]

/-- The Drinfeld tensor law forces monoidality of the canonical fourth-dual map. -/
theorem fourthDualIso_tensor :
    (fourthDualIso C (X ⊗ Y)).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ) := by
  let m : X ⊗ Y ≅ X ⊗ Y := (β_ X Y) ≪≫ (β_ Y X)
  simp only [fourthDualIso, Iso.trans_hom, Iso.symm_hom,
    rightDualIsoMap]
  rw [(Iso.eq_inv_comp m).2 (drinfeld_tensor C X Y)]
  simp only [Category.assoc, drinfeld_inv_dual_tensor C X Y]
  simp only [← tensorHom_comp_tensorHom_assoc, ← Category.assoc]
  rw [Category.assoc m.inv,
    ← CentreCabling.doubleBraiding_natural (doubleDualIso C X).hom (doubleDualIso C Y).hom]
  simp only [Category.assoc, show Modular.doubleBraiding X Y = m.hom from rfl,
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
theorem positive_spherical_of_pseudoUnitary (C : BraidedFusionCategory.{v,u})
    (hpu : PseudoUnitary C) :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ PivotalHasFPDimensions C p :=
  positive_spherical_of_nonunit_fourth_dual C
    (fun i j _ _ ↦ fourthDualIso_tensor C (simples C i) (simples C j)) hpu

end PropertyF.Ground.CentreInduction
