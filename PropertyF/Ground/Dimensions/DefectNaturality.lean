module
public import PropertyF.Ground.Dimensions.RootDualLabel

/-! # Naturality of tensor defects

Naturality of the root tensor isomorphism and defect yields trace reciprocity identities.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The tensor of natural-root components is natural. -/
theorem rootTensorIso_natural
    {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ (rootTensorIso C X' Y').hom =
      (rootTensorIso C X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ) := by
  have hf : f ≫ ((fourthDualRootNaturalIso C).app X').hom =
      ((fourthDualRootNaturalIso C).app X).hom ≫ ((fᘁ)ᘁ) :=
    (fourthDualRootNaturalIso C).hom.naturality f
  have hg : g ≫ ((fourthDualRootNaturalIso C).app Y').hom =
      ((fourthDualRootNaturalIso C).app Y).hom ≫ ((gᘁ)ᘁ) :=
    (fourthDualRootNaturalIso C).hom.naturality g
  change (f ⊗ₘ g) ≫
      ((((fourthDualRootNaturalIso C).app X').hom ⊗ₘ ((fourthDualRootNaturalIso C).app Y').hom) ≫
        (doubleDualTensorIso X' Y').hom) =
    ((((fourthDualRootNaturalIso C).app X).hom ⊗ₘ ((fourthDualRootNaturalIso C).app Y).hom) ≫
        (doubleDualTensorIso X Y).hom) ≫ (((f ⊗ₘ g)ᘁ)ᘁ)
  rw [Category.assoc, ← doubleDualTensorIso_natural, ← Category.assoc,
    ← Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, hf, hg]

/-- The multiplicativity defect is natural in both variables. -/
theorem rootTensorDefect_natural
    {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ (rootTensorDefect C X' Y').hom =
      (rootTensorDefect C X Y).hom ≫ (f ⊗ₘ g) := by
  have hni : (((f ⊗ₘ g)ᘁ)ᘁ) ≫ (rootTensorIso C X' Y').inv =
      (rootTensorIso C X Y).inv ≫ (f ⊗ₘ g) := by
    apply (cancel_epi (rootTensorIso C X Y).hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← (rootTensorIso_natural C f g)]
    simp
  have ha : (f ⊗ₘ g) ≫ ((fourthDualRootNaturalIso C).app (X' ⊗ Y')).hom =
      ((fourthDualRootNaturalIso C).app (X ⊗ Y)).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ) :=
    (fourthDualRootNaturalIso C).hom.naturality (f ⊗ₘ g)
  change (f ⊗ₘ g) ≫ (((fourthDualRootNaturalIso C).app (X' ⊗ Y')).hom ≫
        (rootTensorIso C X' Y').inv) =
      (((fourthDualRootNaturalIso C).app (X ⊗ Y)).hom ≫ (rootTensorIso C X Y).inv) ≫ (f ⊗ₘ g)
  calc
    _ = ((f ⊗ₘ g) ≫ ((fourthDualRootNaturalIso C).app (X' ⊗ Y')).hom) ≫
        (rootTensorIso C X' Y').inv := by simp only [doubleDualFunctor, Category.assoc]
    _ = (((fourthDualRootNaturalIso C).app (X ⊗ Y)).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ)) ≫
        (rootTensorIso C X' Y').inv := by simpa only [doubleDualFunctor] using congrArg (fun t => t ≫ (rootTensorIso C X' Y').inv) ha
    _ = _ := by simpa only [doubleDualFunctor, Category.assoc] using congrArg (fun t => ((fourthDualRootNaturalIso C).app (X ⊗ Y)).hom ≫ t) hni

/-- The dual-label choice can be removed from the Frobenius defect equation. -/
theorem enoTraceMatrix_reciprocity_of_rightDual_frobenius_defect
    (hraw : ∀ i j k (g : Ground.simples C i ⊗ Ground.simples C k ⟶ Ground.simples C j),
      letI : ExactPairing ((Ground.simples C i)ᘁ) (Ground.simples C i) :=
        BraidedCategory.exactPairing_swap _ _
      Ground.tensorLeftHomLinearEquiv (Ground.simples C k) ((Ground.simples C i)ᘁ)
          (Ground.simples C i) (Ground.simples C j)
          ((rootTensorDefect C (Ground.simples C i) (Ground.simples C k)).hom ≫ g) =
        rootDualSign C i • (Ground.tensorLeftHomLinearEquiv (Ground.simples C k)
            ((Ground.simples C i)ᘁ) (Ground.simples C i) (Ground.simples C j) g ≫
          (rootTensorDefect C ((Ground.simples C i)ᘁ) (Ground.simples C j)).hom)) :
    ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j := by
  apply enoTraceMatrix_reciprocity_of_frobenius_defect C
  intro i j k g
  let : ExactPairing ((Ground.simples C i)ᘁ) (Ground.simples C i) :=
    BraidedCategory.exactPairing_swap _ _
  have hn := rootTensorDefect_natural C (rightDualLabelIso C i).hom (𝟙 (Ground.simples C j))
  simp only [enoFrobeniusEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Iso.refl_inv, Iso.refl_hom, Category.id_comp, tensorIso_hom] 
  rw [(hraw i j k g)]
  simp only [Linear.smul_comp, Category.assoc, ← hn]

end PropertyF.Ground.Dimensions
