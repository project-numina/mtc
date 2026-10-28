module
public import PropertyF.Ground.Dimensions.DefectAssociativity
public import PropertyF.Ground.Dimensions.FourthTensorUnit
public import PropertyF.Ground.Dimensions.CoevaluationSliding

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The signed three-object cup slide follows from involutivity of its outer tensor defect. -/
theorem rootTensorDefect_slide_of_involution (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) (K : C.Obj)
    (hinv : let X := Ground.simples C i
      (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom =
        𝟙 ((Xᘁ) ⊗ (X ⊗ K))) :
    let X := Ground.simples C i
    letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
    let η : K ⟶ (Xᘁ) ⊗ (X ⊗ K) :=
      (λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom
    η ≫ (Xᘁ) ◁ (rootTensorDefect C X K).hom =
      rootDualSign C i • (η ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom) := by
  let X := Ground.simples C i
  let A := Xᘁ
  let I := 𝟙_ C.Obj
  let p : ExactPairing A X := BraidedCategory.exactPairing_swap X A
  let : ExactPairing A X := p
  let cup : I ⟶ A ⊗ X := η_ A X
  let η : K ⟶ A ⊗ (X ⊗ K) := (λ_ K).inv ≫ cup ▷ K ≫ (α_ A X K).hom
  let D := (rootTensorDefect C A (X ⊗ K)).hom
  let E := A ◁ (rootTensorDefect C X K).hom
  let u := rootDimension C (Ground.unitIndex C)
  let e := rootDualSign C i
  have hs : u * u = 1 := rootDimension_unit_sq C
  have hc : cup ≫ (rootTensorDefect C A X).hom = (u * e) • cup :=
    rootTensorDefect_swapped_coevaluation C i
  have hn := rootTensorDefect_natural C cup (𝟙 K)
  simp only [tensorHom_id] at hn
  have hu : (rootTensorDefect C I K).hom = u • 𝟙 (I ⊗ K) := rootTensorDefect_unit_left C K
  have hcomm := rootTensorDefect_natural C (𝟙 A) (rootTensorDefect C X K).hom
  simp only [id_tensorHom] at hcomm
  change E ≫ D = D ≫ E at hcomm
  have hloop : η ≫ D ≫ E = e • η := by
    change ((λ_ K).inv ≫ cup ▷ K ≫ (α_ A X K).hom) ≫ D ≫ E = _
    rw [Category.assoc, rootTensorDefect_associativity]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (cup ▷ K), hn]
    simp only [hu, Linear.smul_comp, Linear.comp_smul, Category.id_comp]
    rw [← comp_whiskerRight_assoc, hc]
    simp only [MonoidalLinear.smul_whiskerRight, Linear.comp_smul, Linear.smul_comp,
      smul_smul, ← mul_assoc, hs, one_mul]
    rfl
  change η ≫ E = e • (η ≫ D)
  have hloop' : η ≫ E ≫ D = e • η := by rw [hcomm]; exact hloop
  change D ≫ D = 𝟙 _ at hinv
  have hh := congrArg (fun f => f ≫ D) hloop'
  simpa only [Category.assoc, hinv, Category.comp_id, Linear.smul_comp] using hh
end PropertyF.Ground.Dimensions
