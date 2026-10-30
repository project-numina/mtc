module
public import MTC.CategoryTheory.Dimensions.RootDualLabel

open MTC.Braided

/-! # Tensor-defect naturality and coevaluation sliding

Naturality of the root tensor isomorphism and sliding through coevaluation yield trace reciprocity.

## Main results

* `rootTensorIso_natural`: proves naturality of the tensor comparison for fourth-dual roots.
* `rootTensorDefect_natural`: derives naturality of its defect.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
variable {X X' Y Y' : C.Obj}
set_option backward.isDefEq.respectTransparency false in
/-- The tensor of natural-root components is natural. -/
theorem rootTensorIso_natural (f : X ⟶ X') (g : Y ⟶ Y') :
    CommSq (f ⊗ₘ g) (rootTensorIso C X Y).hom (rootTensorIso C X' Y').hom
      (((f ⊗ₘ g)ᘁ)ᘁ) := by
  refine ⟨?_⟩
  simp only [rootTensorIso, Iso.trans_hom, tensorIso_hom]
  rw [Category.assoc, ← doubleDualTensorIso_natural, ← Category.assoc,
    ← Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  erw [(fourthDualRootNaturalIso C).hom.naturality f, (fourthDualRootNaturalIso C).hom.naturality g]
  rfl

/-- The multiplicativity defect is natural in both variables. -/
theorem rootTensorDefect_natural (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ (rootTensorDefect C X' Y').hom =
      (rootTensorDefect C X Y).hom ≫ (f ⊗ₘ g) := by
  have ha : (f ⊗ₘ g) ≫ ((fourthDualRootNaturalIso C).app (X' ⊗ Y')).hom =
      ((fourthDualRootNaturalIso C).app (X ⊗ Y)).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ) :=
    (fourthDualRootNaturalIso C).hom.naturality (f ⊗ₘ g)
  change (f ⊗ₘ g) ≫ (((fourthDualRootNaturalIso C).app (X' ⊗ Y')).hom ≫
        (rootTensorIso C X' Y').inv) =
      (((fourthDualRootNaturalIso C).app (X ⊗ Y)).hom ≫ (rootTensorIso C X Y).inv) ≫ (f ⊗ₘ g)
  dsimp only [doubleDualFunctor] at ha ⊢
  rw [reassoc_of% ha, (CommSq.vert_inv (rootTensorIso_natural C f g)).w,
    Category.assoc]


end MTC.CategoryTheory.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The Frobenius defect equation reduces to its value on the identity map. -/
theorem trace_reciprocity_of_coeval_defect
    (hunit : ∀ i k,
      let X := simples C i
      let K := simples C k
      letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
      tensorLeftHomLinearEquiv (k := ℂ) K (Xᘁ) X (X ⊗ K) (rootTensorDefect C X K).hom =
        (rootDualSign C i).1 • (tensorLeftHomLinearEquiv (k := ℂ) K (Xᘁ) X (X ⊗ K) (𝟙 (X ⊗ K)) ≫
          (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom)) :
    ENOTraceMatrixReciprocity C :=
  trace_reciprocity_of_frobenius_defect fun i j k g ↦ by
    let X := simples C i
    let K := simples C k
    let J := simples C j
    let : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
    have hpost := tensorLeftHomEquiv_naturality (Y := Xᘁ) (rootTensorDefect C X K).hom g
    have hpost' := tensorLeftHomEquiv_naturality (Y := Xᘁ) (𝟙 (X ⊗ K)) g
    change tensorLeftHomLinearEquiv (k := ℂ) K (Xᘁ) X J ((rootTensorDefect C X K).hom ≫ g) =
      tensorLeftHomLinearEquiv (k := ℂ) K (Xᘁ) X (X ⊗ K) (rootTensorDefect C X K).hom ≫ (Xᘁ) ◁ g at hpost
    change tensorLeftHomLinearEquiv (k := ℂ) K (Xᘁ) X J ((𝟙 (X ⊗ K)) ≫ g) =
      tensorLeftHomLinearEquiv (k := ℂ) K (Xᘁ) X (X ⊗ K) (𝟙 (X ⊗ K)) ≫ (Xᘁ) ◁ g at hpost'
    have hn := rootTensorDefect_natural C (𝟙 (Xᘁ)) g
    simp only [id_tensorHom] at hn
    simp only [Category.id_comp] at hpost'
    have hnlabel := rootTensorDefect_natural C (rightDualLabelIso C i).hom (𝟙 J)
    simp only [enoFrobeniusEquiv, LinearEquiv.trans_apply, Linear.homCongr_apply,
      Iso.refl_inv, Iso.refl_hom, Category.id_comp, tensorIso_hom]
    rw [hpost, hunit i k, Linear.smul_comp, Category.assoc, ← hn, ← Category.assoc, ← hpost']
    dsimp only [X, K, J] at hnlabel ⊢
    simp only [Linear.smul_comp, Category.assoc, ← hnlabel]
end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- The signed tensor defect slides across the coevaluation of a simple object. -/
abbrev RootTensorDefectSlide (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) (K : C.Obj) : Prop :=
  let X := simples C i
  letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  let η : K ⟶ (Xᘁ) ⊗ (X ⊗ K) :=
    (λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom
  η ≫ (Xᘁ) ◁ (rootTensorDefect C X K).hom =
    (rootDualSign C i).1 • (η ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom)

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The ENO reciprocity identity only needs the defect to slide through the
coevaluation of the swapped dual pairing. -/
theorem trace_reciprocity_of_coevaluation
    (hslide : ∀ i k, RootTensorDefectSlide C i (simples C k)) :
    ENOTraceMatrixReciprocity C :=
  trace_reciprocity_of_coeval_defect fun i k ↦ by
    let X := simples C i
    let K := simples C k
    let : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
    change ((λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom ≫
        (Xᘁ) ◁ (rootTensorDefect C X K).hom) =
      (rootDualSign C i).1 • (((λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom ≫
        (Xᘁ) ◁ 𝟙 (X ⊗ K)) ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom)
    simpa only [RootTensorDefectSlide, whiskerLeft_id, Category.comp_id, Category.assoc] using hslide i k
end MTC.CategoryTheory.Dimensions

end
