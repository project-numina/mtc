module
public import PropertyF.Ground.CentreInduction.PositivePivotal
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Dimensions.DualBraiding
public import PropertyF.Ground.Dimensions.DoubleDualBraiding
public import PropertyF.Ground.CentreCabling.CentralityClosure
public import PropertyF.Ground.Dimensions.DefectExtension
public import PropertyF.Ground.CentreIntegrate.TwistBalancing
public import PropertyF.Ground.Dimensions.MonodromyTensorCap

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
    Dimensions.rightDualTensorIso_braiding]

end PropertyF.Ground.CentreInduction

end
end

/-! Monoidality of the fourth dual from the Drinfeld tensor law. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u})

/-- The standard tensor equation for the Drinfeld isomorphism. -/
def DrinfeldTensorLaw : Prop := ∀ X Y : C.Obj,
    Modular.doubleBraiding X Y ≫ (doubleDualIso C (X ⊗ Y)).hom =
      ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ≫
        (Dimensions.doubleDualTensorIso X Y).hom

theorem drinfeld_tensor_inverse (h : DrinfeldTensorLaw C) (X Y : C.Obj) :
    (doubleDualIso C (X ⊗ Y)).inv =
      (Dimensions.doubleDualTensorIso X Y).inv ≫
        ((doubleDualIso C X).inv ⊗ₘ (doubleDualIso C Y).inv) ≫
          Modular.doubleBraiding X Y := by
  let m : X ⊗ Y ≅ X ⊗ Y := (β_ X Y) ≪≫ (β_ Y X)
  have hi : m ≪≫ doubleDualIso C (X ⊗ Y) =
      (doubleDualIso C X ⊗ᵢ doubleDualIso C Y) ≪≫ Dimensions.doubleDualTensorIso X Y := by
    apply Iso.ext
    exact h X Y
  have hinv := congrArg Iso.inv hi
  simp only [Iso.trans_inv, tensorIso_inv] at hinv
  change (doubleDualIso C (X ⊗ Y)).inv ≫ m.inv = _ at hinv
  apply (cancel_mono m.inv).1
  rw [hinv]
  change _ = (_ ≫ _ ≫ m.hom) ≫ m.inv
  simp [Category.assoc]

/-- Formula for transporting the inverse Drinfeld map through an isomorphism. -/
theorem drinfeld_inv_natural {A B : C.Obj} (t : A ≅ B) :
    (doubleDualIso C A).inv = (((t.homᘁ)ᘁ) ≫ (doubleDualIso C B).inv) ≫ t.inv := by
  apply (cancel_epi (doubleDualIso C A).hom).1
  simp only [Iso.hom_inv_id]
  rw [Category.assoc, ← Dimensions.doubleDualIso_natural_assoc]
  simp

/-- The inverse dual Drinfeld map after the tensorator, in terms of the
reversed dual factors and monodromy. -/
theorem drinfeld_inv_dual_tensor (h : DrinfeldTensorLaw C) (X Y : C.Obj) :
    (Dimensions.doubleDualTensorIso X Y).hom ≫
      ((doubleDualIso C ((X ⊗ Y)ᘁ)).invᘁ) =
    Modular.doubleBraiding ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) ≫
      (((doubleDualIso C (Xᘁ)).invᘁ) ⊗ₘ ((doubleDualIso C (Yᘁ)).invᘁ)) ≫
        (Dimensions.doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((Dimensions.doubleDualTensorIso X Y).homᘁ)ᘁ) := by
  let t := rightDualTensorIso X Y
  let d := Dimensions.doubleDualTensorIso (Yᘁ) (Xᘁ)
  let f := (doubleDualIso C (Yᘁ)).inv
  let g := (doubleDualIso C (Xᘁ)).inv
  have hn := drinfeld_inv_natural C t
  have hn' := congrArg (fun z => rightAdjointMate z) hn
  simp only [comp_rightAdjointMate] at hn'
  have hi := drinfeld_tensor_inverse C h (Yᘁ) (Xᘁ)
  change (doubleDualIso C ((Yᘁ) ⊗ (Xᘁ))).inv = d.inv ≫ (f ⊗ₘ g) ≫
    Modular.doubleBraiding (Yᘁ) (Xᘁ) at hi
  have hi' := congrArg (fun z => rightAdjointMate z) hi
  simp only [comp_rightAdjointMate] at hi'
  have hm' : (rightDualTensorIso (Yᘁ) (Xᘁ)).inv ≫
      ((Modular.doubleBraiding (Yᘁ) (Xᘁ))ᘁ) =
      Modular.doubleBraiding ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) ≫
        (rightDualTensorIso (Yᘁ) (Xᘁ)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact rightDualTensorIso_monodromy
  have ht' := rightDualTensorIso_inv_natural f g
  simp only [Dimensions.doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap, Category.assoc]
  change (rightDualTensorIso (Yᘁ) (Xᘁ)).inv ≫ t.homᘁ ≫
    (doubleDualIso C ((X ⊗ Y)ᘁ)).invᘁ = _
  rw [hn', hi']
  have hc : t.homᘁ ≫ t.invᘁ = 𝟙 _ := by
    rw [← comp_rightAdjointMate, Iso.inv_hom_id, rightAdjointMate_id]
  simp only [comp_rightAdjointMate, Category.assoc]
  rw [← Category.assoc (t.homᘁ), hc, Category.id_comp]
  rw [← Category.assoc (rightDualTensorIso (Yᘁ) (Xᘁ)).inv, hm']
  simp only [Category.assoc]
  rw [← Category.assoc (rightDualTensorIso (Yᘁ) (Xᘁ)).inv, ht']
  simp only [Category.assoc]
  dsimp only [d, Dimensions.doubleDualTensorIso, Dimensions.rightDualIsoMap,
    Iso.trans_inv, Iso.symm_inv]
  simp only [comp_rightAdjointMate, Category.assoc, f, g, t]



/-- The Drinfeld tensor law forces monoidality of the canonical fourth-dual map. -/
theorem fourthDualIso_tensor_of_drinfeld (h : DrinfeldTensorLaw C) (X Y : C.Obj) :
    (Dimensions.fourthDualIso C (X ⊗ Y)).hom =
      ((Dimensions.fourthDualIso C X).hom ⊗ₘ (Dimensions.fourthDualIso C Y).hom) ≫
        (Dimensions.doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((Dimensions.doubleDualTensorIso X Y).homᘁ)ᘁ) := by
  let m : X ⊗ Y ≅ X ⊗ Y := (β_ X Y) ≪≫ (β_ Y X)
  have hm : m.hom = Modular.doubleBraiding X Y := rfl
  have hu : (doubleDualIso C (X ⊗ Y)).hom = m.inv ≫
      ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ≫
        (Dimensions.doubleDualTensorIso X Y).hom := by
    exact (Iso.eq_inv_comp m).2 (h X Y)
  have hv := drinfeld_inv_dual_tensor C h X Y
  have hn : Modular.doubleBraiding X Y ≫
      ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) =
      ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ≫
        Modular.doubleBraiding ((Xᘁ)ᘁ) ((Yᘁ)ᘁ) := by
    exact CentreCabling.doubleBraiding_natural (doubleDualIso C X).hom (doubleDualIso C Y).hom
  simp only [Dimensions.fourthDualIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap]
  rw [hu]
  simp only [Category.assoc]
  rw [hv]
  simp only [← tensorHom_comp_tensorHom_assoc]
  have hn' : m.inv ≫ (((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ≫
      Modular.doubleBraiding ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)) =
      ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) := by
    rw [← hn]
    change m.inv ≫ (m.hom ≫ _) = _
    simp
  simp only [← Category.assoc]
  rw [Category.assoc m.inv, hn']


/-- The Drinfeld tensor law constructs the canonical positive sphere in a
pseudo-unitary base, without assuming an initial pivotal structure. -/
theorem positive_spherical_of_drinfeld_tensor (h : DrinfeldTensorLaw C)
    (hpu : PseudoUnitary C) :
    ∃ p : Dimensions.PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ) :=
  Dimensions.positive_spherical_of_nonunit_fourth_dual C
    (fun i j _ _ ↦ fourthDualIso_tensor_of_drinfeld C h (simples C i) (simples C j)) hpu

end PropertyF.Ground.CentreInduction

end

/-! The Drinfeld tensor law and its pseudo-unitary consequences. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreInduction
universe v u

/-- The canonical Drinfeld isomorphism satisfies its tensor law. -/
theorem drinfeldTensorLaw (C : BraidedFusionCategory.{v,u}) : DrinfeldTensorLaw C :=
  fun X Y ↦ CentreIntegrate.drinfeld_tensor_of_pairing_cap C X Y
    (Dimensions.drinfeld_tensor_pairing_cap C X Y)


/-- Every pseudo-unitary braided fusion category has a positive spherical
structure with its actual FP dimensions, without any pivotal premise. -/
theorem positive_spherical_of_pseudoUnitary (C : BraidedFusionCategory.{v,u})
    (hpu : PseudoUnitary C) :
    ∃ p : Dimensions.PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      Dimensions.pivotalDimension C p (simples C i) = (fpSimple C i : ℂ) :=
  positive_spherical_of_drinfeld_tensor C (drinfeldTensorLaw C) hpu

end PropertyF.Ground.CentreInduction
