module
public import PropertyF.Ground.Dimensions.ENOMatrices
public import PropertyF.Ground.Dimensions.QuantumTensor

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

set_option backward.isDefEq.respectTransparency false in
/-- Closing the inverse tensor defect with the natural root gives the product
of the two simple root dimensions. -/
theorem rootTrace_inverseDefect (C : Ground.BraidedFusionCategory.{v,u})
    (i j : Fin (Ground.rank C)) :
    Ground.unitScalar C (rootTrace C (rootTensorDefect C (Ground.simples C i) (Ground.simples C j)).inv) =
      rootDimension C i * rootDimension C j := by
  let X := Ground.simples C i
  let Y := Ground.simples C j
  let a := fourthDualRootNaturalIso C
  let b := rootTensorIso C X Y
  let d := rootTensorDefect C X Y
  have hd : d.inv ≫ (a.app (X ⊗ Y)).hom = b.hom := by
    simp [d, rootTensorDefect, b, a, Category.assoc]
  have ht : rootTrace C d.inv = rightQuantumTrace b := by
    apply End.homEquiv.injective
    change η_ (X ⊗ Y) ((X ⊗ Y)ᘁ) ≫
      ((d.inv ≫ (a.app (X ⊗ Y)).hom) ⊗ₘ 𝟙 ((X ⊗ Y)ᘁ)) ≫
        ε_ ((X ⊗ Y)ᘁ) (((X ⊗ Y)ᘁ)ᘁ) =
      η_ (X ⊗ Y) ((X ⊗ Y)ᘁ) ≫ (b.hom ⊗ₘ 𝟙 ((X ⊗ Y)ᘁ)) ≫
        ε_ ((X ⊗ Y)ᘁ) (((X ⊗ Y)ᘁ)ᘁ)
    rw [hd]
  rw [ht]
  change Ground.unitScalar C (rightQuantumTrace
    (((a.app X) ⊗ᵢ (a.app Y)) ≪≫ doubleDualTensorIso X Y)) = _
  rw [← groundUnitScalarEquiv_apply]
  let ax : X ≅ (Xᘁ)ᘁ := (a.app X)
  let ay : Y ≅ (Yᘁ)ᘁ := (a.app Y)
  have hp := rightQuantumTrace_tensor_scalar (groundUnitScalarEquiv C) ax ay
  change (groundUnitScalarEquiv C) (rightQuantumTrace ((ax ⊗ᵢ ay) ≪≫ doubleDualTensorIso X Y)) =
    rootDimension C i * rootDimension C j
  rw [hp]
  have hx : groundUnitScalarEquiv C (rightQuantumTrace ax) = rootDimension C i := by
    simp [rootDimension, rootTrace, rightTraceWith, rightQuantumTrace, groundUnitScalarEquiv_apply, X, a, ax]
  have hy : groundUnitScalarEquiv C (rightQuantumTrace ay) = rootDimension C j := by
    simp [rootDimension, rootTrace, rightTraceWith, rightQuantumTrace, groundUnitScalarEquiv_apply, Y, a, ay]
  rw [hx, hy]

end PropertyF.Ground.Dimensions
