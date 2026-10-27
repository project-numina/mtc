module
public import PropertyF.Ground.Dimensions.ENOGalois
public import PropertyF.Ground.Dimensions.DualTensorNaturality

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

/-- Tensor compatibility of the fourth-dual map makes every actual ENO
multiplicity defect involutive. -/
theorem multiplicityDefect_involutive_of_fourthDual_tensor
    (C : Ground.BraidedFusionCategory.{v,u})
    (hfourth : ∀ X Y : C.Obj, (fourthDualIso C (X ⊗ Y)).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ))
    (i j k : Fin (Ground.rank C)) :
    (multiplicityDefect C i j k).toLinearMap * (multiplicityDefect C i j k).toLinearMap = 1 := by
  apply multiplicityDefect_involution_of_tensor_square C i j k
  apply rootTensor_square_of_fourthDual_tensor C
  · exact (doubleDualTensorIso_natural ((fourthDualRootNaturalIso C).app (Ground.simples C i)).hom
      ((fourthDualRootNaturalIso C).app (Ground.simples C j)).hom).symm
  · exact hfourth _ _

/-- Pseudo-unitarity yields a positive spherical structure from the fourth-dual
tensor law and ENO's trace reciprocity. -/
theorem eno_pseudoUnitary_yields_positive_spherical_of_fourth_tensor_and_reciprocity
    (C : Ground.BraidedFusionCategory.{v,u})
    (hfourth : ∀ X Y : C.Obj, (fourthDualIso C (X ⊗ Y)).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ))
    (htranspose : ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j)
    (hpu : Ground.PseudoUnitary C) :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  apply eno_pseudoUnitary_yields_positive_spherical_of_reciprocity C _ hfourth htranspose hpu
  intro X X' Y Y' f g
  exact doubleDualTensorIso_natural f g

/-- The fourth-dual tensor law alone implies intrinsic simple algebraic
integrality, without sphericality or pseudo-unitarity. -/
theorem squaredNorm_isIntegral_of_fourthDual_tensor
    (C : Ground.BraidedFusionCategory.{v,u})
    (hfourth : ∀ X Y : C.Obj, (fourthDualIso C (X ⊗ Y)).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ)) (i : Fin (Ground.rank C)) :
    IsIntegral ℤ (Ground.squaredNorm C (Ground.simples C i)) :=
  squaredNorm_isIntegral_of_involutions C (multiplicityDefect_involutive_of_fourthDual_tensor C hfourth) i

/-- The fourth-dual tensor law and trace reciprocity imply the full Galois
bounds on the intrinsic global dimension. -/
theorem globalDimension_galois_bounds_of_fourth_tensor_and_reciprocity
    (C : Ground.BraidedFusionCategory.{v,u})
    (hfourth : ∀ X Y : C.Obj, (fourthDualIso C (X ⊗ Y)).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ))
    (htranspose : ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j) (σ : ℂ ≃+* ℂ) :
    ∃ D : ℝ, 1 ≤ D ∧ D ≤ Ground.globalFPDimension C ∧ σ (Ground.globalDimension C) = (D : ℂ) :=
  globalDimension_galois_bounds_of_trace_reciprocity C
    (multiplicityDefect_involutive_of_fourthDual_tensor C hfourth) htranspose σ

end PropertyF.Ground.Dimensions
