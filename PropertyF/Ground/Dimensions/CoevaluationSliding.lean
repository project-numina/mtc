module
public import PropertyF.Ground.Dimensions.CoevaluationReciprocity

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The ENO reciprocity identity only needs the defect to slide through the
coevaluation of the swapped dual pairing. -/
theorem enoTraceMatrix_reciprocity_of_coevaluation_sliding
    (C : Ground.BraidedFusionCategory.{v,u})
    (hslide : ∀ i k,
      let X := Ground.simples C i
      let K := Ground.simples C k
      letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
      let η : K ⟶ (Xᘁ) ⊗ (X ⊗ K) :=
        (λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom
      η ≫ (Xᘁ) ◁ (rootTensorDefect C X K).hom =
        rootDualSign C i • (η ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom)) :
    ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j := by
  apply enoTraceMatrix_reciprocity_of_coevaluation_defect C
  intro i k
  let X := Ground.simples C i
  let K := Ground.simples C k
  let : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  change ((λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom ≫
      (Xᘁ) ◁ (rootTensorDefect C X K).hom) =
    rootDualSign C i • (((λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom ≫
      (Xᘁ) ◁ 𝟙 (X ⊗ K)) ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom)
  simpa only [whiskerLeft_id, Category.comp_id, Category.assoc] using hslide i k
end PropertyF.Ground.Dimensions
