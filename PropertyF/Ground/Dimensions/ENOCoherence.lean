module
public import PropertyF.Ground.Dimensions.ENOReciprocity
public import PropertyF.Ground.Dimensions.DualTensorNaturality

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

/-- It suffices to prove the fourth-dual tensor law on simple pairs; the
construction uses no assumption about that law on arbitrary objects. -/
theorem eno_pseudoUnitary_yields_positive_spherical_of_simple_fourth_and_reciprocity
    (C : Ground.BraidedFusionCategory.{v,u})
    (hfourth : ∀ i j : Fin (Ground.rank C),
      (fourthDualIso C (Ground.simples C i ⊗ Ground.simples C j)).hom =
      ((fourthDualIso C (Ground.simples C i)).hom ⊗ₘ (fourthDualIso C (Ground.simples C j)).hom) ≫
        (doubleDualTensorIso (((Ground.simples C i)ᘁ)ᘁ) (((Ground.simples C j)ᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso (Ground.simples C i) (Ground.simples C j)).homᘁ)ᘁ))
    (htranspose : ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j)
    (hpu : Ground.PseudoUnitary C) :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  have hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1 := by
    intro i j k
    apply multiplicityDefect_involution_of_tensor_square C i j k
    apply rootTensor_square_of_fourthDual_tensor C
    · exact (doubleDualTensorIso_natural ((fourthDualRootNaturalIso C).app (Ground.simples C i)).hom
        ((fourthDualRootNaturalIso C).app (Ground.simples C j)).hom).symm
    · exact hfourth i j
  have heig : ∀ i j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j := by
    intro i j
    exact enoTraceMatrix_eigenvector_of_involutions C i j (hinv i j)
  have hnorm : ∀ i, Ground.squaredNorm C (Ground.simples C i) =
      ((‖rootDimension C i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    exact squaredNorm_eq_rootDimension_norm_sq_of_trace_reciprocity C hinv htranspose i
  apply eno_pseudoUnitary_yields_positive_spherical_of_matrix_identities C hinv heig _ hnorm hpu
  intro X X' Y Y' f g
  exact doubleDualTensorIso_natural f g


end PropertyF.Ground.Dimensions
