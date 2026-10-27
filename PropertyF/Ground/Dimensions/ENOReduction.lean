module
public import PropertyF.Ground.Dimensions.ENOPhase
public import PropertyF.Ground.Dimensions.SimpleHomBasis

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

/-- The ENO construction needs only the two dual coherence laws and the
intrinsic root-norm identity; the trace-matrix eigenvector identity follows. -/
theorem eno_pseudoUnitary_yields_positive_spherical_of_coherence_and_norm
    (C : Ground.BraidedFusionCategory.{v,u})
    (hnat : ∀ {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y'),
      (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
        (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ))
    (hfourth : ∀ X Y : C.Obj, (fourthDualIso C (X ⊗ Y)).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ))
    (hnorm : ∀ i, Ground.squaredNorm C (Ground.simples C i) =
      ((‖rootDimension C i‖ ^ 2 : ℝ) : ℂ)) (hpu : Ground.PseudoUnitary C) :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  have hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1 := by
    intro i j k
    apply multiplicityDefect_involution_of_tensor_square C i j k
    apply rootTensor_square_of_fourthDual_tensor C
    · exact (hnat ((fourthDualRootNaturalIso C).app (Ground.simples C i)).hom
        ((fourthDualRootNaturalIso C).app (Ground.simples C j)).hom).symm
    · exact hfourth _ _
  apply eno_pseudoUnitary_yields_positive_spherical_of_matrix_identities C hinv _ hnat hnorm hpu
  intro i j
  exact enoTraceMatrix_eigenvector_of_involutions C i j (hinv i j)

end PropertyF.Ground.Dimensions
