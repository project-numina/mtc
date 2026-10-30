module
public import MTC.Center.Induction.PositivePivotal
public import MTC.CategoryTheory.Dimensions.DualTensorNaturality
public import MTC.CategoryTheory.Dimensions.DualBraiding
public import MTC.CategoryTheory.Dimensions.DoubleDualMonoidal
public import MTC.CategoryTheory.Dimensions.DefectExtension
public import MTC.Center.Balancing.TwistBalancing
public import MTC.CategoryTheory.Dimensions.MonodromyTensorCap

open PropertyF.Ground.Dimensions

/-! The Drinfeld map satisfies its tensor coherence law. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u

/-- The Drinfeld map satisfies tensor coherence in a braided rigid category. -/
theorem drinfeld_tensor {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] [RightRigidCategory D] (X Y : D) :
    CommSq (Modular.doubleBraiding X Y) ((drinfeldIso X).hom ⊗ₘ (drinfeldIso Y).hom)
      (drinfeldIso (X ⊗ Y)).hom (doubleDualTensorIso X Y).hom :=
  ⟨CentreIntegrate.drinfeld_tensor_of_pairing_cap (fun Z ↦ drinfeldIso Z)
    (drinfeld_eval (X ⊗ Y))
    ((monodromy_tensor_cap_evaluated X Y).trans (drinfeld_tensor_cap_factor X Y).symm)⟩

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
    CommSq ((M X Y)ᘁ) (rightDualTensorIso X Y).hom (rightDualTensorIso X Y).hom
      (M (Yᘁ) (Xᘁ)) :=
  let : HasRightDual (Y ⊗ X) := hasRightDualTensor
  ⟨by simp [Modular.doubleBraiding, comp_rightAdjointMate, rightDualTensorIso_braiding]⟩

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
-- Monodromy is the double braiding.
local notation "M" => Modular.doubleBraiding

/-- The tensorator and inverse Drinfeld maps form the reversed tensor square. -/
theorem drinfeld_tensor_inverse :
    CommSq (μ₂ X Y).hom ((d X).inv ⊗ₘ (d Y).inv) (d (X ⊗ Y)).inv (M X Y) := by
  simpa only [tensorIso_inv] using
    CommSq.vert_inv (g := d X ⊗ᵢ d Y) (h := d (X ⊗ Y)) (drinfeld_tensor X Y)

omit [RightRigidCategory D] in
/-- The inverse Drinfeld map is natural in the object. -/
theorem drinfeld_inv_natural {A B : D} [HasRightDual A] [HasRightDual (Aᘁ)]
    [HasRightDual B] [HasRightDual (Bᘁ)] (f : A ⟶ B) :
    CommSq (d A).inv ((fᘁ)ᘁ) f (d B).inv :=
  (CommSq.vert_inv ⟨drinfeldIso_natural f⟩).flip

/-- The inverse dual Drinfeld map after the tensorator, in terms of the
reversed dual factors and monodromy. -/
theorem drinfeld_inv_dual_tensor :
    (μ₂ X Y).hom ≫ ((d ((X ⊗ Y)ᘁ)).invᘁ) =
      M ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) ≫ (((d (Xᘁ)).invᘁ) ⊗ₘ ((d (Yᘁ)).invᘁ)) ≫
        (μ₂ ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫ (((μ₂ X Y).homᘁ)ᘁ) := by
  let t := rightDualTensorIso X Y
  let f := (d (Yᘁ)).inv
  let g := (d (Xᘁ)).inv
  have hn' := congrArg rightAdjointMate ((Iso.eq_comp_inv t).2 (drinfeld_inv_natural t.hom).w)
  have hi' := congrArg rightAdjointMate <|
    (Iso.eq_inv_comp (μ₂ (Yᘁ : D) (Xᘁ : D))).2 (drinfeld_tensor_inverse (Yᘁ : D) (Xᘁ : D)).w
  simp only [comp_rightAdjointMate] at hn' hi'
  simp only [doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    rightDualIsoMap, Category.assoc]
  change (rightDualTensorIso (Yᘁ) (Xᘁ)).inv ≫ t.homᘁ ≫
    (d ((X ⊗ Y)ᘁ)).invᘁ = _
  simp only [hn', hi', comp_rightAdjointMate, Category.assoc]
  rw [← Category.assoc (t.homᘁ), ← comp_rightAdjointMate, Iso.inv_hom_id,
    rightAdjointMate_id, Category.id_comp]
  rw [reassoc_of% (CommSq.vert_inv rightDualTensorIso_monodromy).w.symm,
    ← reassoc_of% rightDualTensorIso_inv_natural f g]
  simp only [doubleDualTensorIso, rightDualIsoMap, Iso.trans_inv, Iso.symm_inv,
    comp_rightAdjointMate, Category.assoc, f, g, t]

/-- The Drinfeld tensor law forces monoidality of the canonical fourth-dual map. -/
theorem fourthDualIso_tensor :
    fourthDualTensorLaw X Y := by
  let m : X ⊗ Y ≅ X ⊗ Y := (β_ X Y) ≪≫ (β_ Y X)
  simp only [fourthDualTensorLaw, fourthDualIso, Iso.trans_hom, Iso.symm_hom, rightDualIsoMap]
  rw [(Iso.eq_inv_comp m).2 (drinfeld_tensor X Y).w]
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
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ PivotalHasFPDimensions p :=
  let h (i j : Fin (rank C)) := fourthDualIso_tensor (simples C i) (simples C j)
  positive_spherical_of_simple_fourth_and_reciprocity h (trace_reciprocity_of_fourth_dual h) hpu

end PropertyF.Ground.CentreInduction
