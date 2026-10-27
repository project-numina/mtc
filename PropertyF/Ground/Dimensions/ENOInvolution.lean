module
public import PropertyF.Ground.Dimensions.DefectExtension

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false in
/-- Involutivity on all multiplicity spaces makes the underlying categorical tensor defect involutive. -/
theorem rootTensorDefect_involution_of_multiplicity_involutions
    (C : Ground.BraidedFusionCategory.{v,u}) (i j : Fin (Ground.rank C))
    (h : ∀ k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) :
    (rootTensorDefect C (Ground.simples C i) (Ground.simples C j)).hom ≫
      (rootTensorDefect C (Ground.simples C i) (Ground.simples C j)).hom =
        𝟙 (Ground.simples C i ⊗ Ground.simples C j) := by
  classical
  let X := Ground.simples C i ⊗ Ground.simples C j
  let ex := simpleDecomposition C X
  let V := simplePiecesObject C X
  apply (cancel_epi ex.inv).1
  apply biproduct.hom_ext'
  intro a
  let f : Ground.simples C a.1 ⟶ X := biproduct.ι V a ≫ ex.inv
  have hh := congrArg (fun L => L f) (h a.1)
  change multiplicityDefect C i j a.1 (multiplicityDefect C i j a.1 f) = f at hh
  rw [multiplicityDefect_apply, multiplicityDefect_apply] at hh
  simpa [f, X, ex, V, Category.assoc] using hh

/-- Multiplicity involutivity alone implies ENO trace reciprocity. -/
theorem enoTraceMatrix_reciprocity_of_multiplicity_involutions
    (C : Ground.BraidedFusionCategory.{v,u})
    (h : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) :
    ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k = rootDualSign C i * enoTraceMatrix C i k j := by
  have hinv : ∀ X Y : C.Obj, (rootTensorDefect C X Y).hom ≫ (rootTensorDefect C X Y).hom = 𝟙 (X ⊗ Y) := by
    apply rootTensorDefect_involution_extension C
    intro i j
    exact rootTensorDefect_involution_of_multiplicity_involutions C i j (h i j)
  apply enoTraceMatrix_reciprocity_of_coevaluation_sliding C
  intro i k
  exact rootTensorDefect_slide_of_involution C i (Ground.simples C k) (hinv _ _)

/-- Multiplicity involutivity and pseudo-unitarity construct the canonical positive spherical structure. -/
theorem eno_pseudoUnitary_yields_positive_spherical_of_involutions
    (C : Ground.BraidedFusionCategory.{v,u})
    (h : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) (hpu : Ground.PseudoUnitary C) :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  have heig : ∀ i j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j := by
    intro i j
    exact enoTraceMatrix_eigenvector_of_involutions C i j (h i j)
  have htranspose := enoTraceMatrix_reciprocity_of_multiplicity_involutions C h
  have hnorm : ∀ i, Ground.squaredNorm C (Ground.simples C i) =
      ((‖rootDimension C i‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    exact squaredNorm_eq_rootDimension_norm_sq_of_trace_reciprocity C h htranspose i
  apply eno_pseudoUnitary_yields_positive_spherical_of_matrix_identities C h heig _ hnorm hpu
  intro X X' Y Y' f g
  exact doubleDualTensorIso_natural f g
/-- Multiplicity involutivity implies total positivity and the FP-square norm bound. -/
theorem squaredNorm_galois_bounds_of_multiplicity_involutions
    (C : Ground.BraidedFusionCategory.{v,u})
    (h : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ Ground.fpSimple C i ^ 2 ∧
      σ (Ground.squaredNorm C (Ground.simples C i)) = (r : ℂ) :=
  squaredNorm_galois_bounds_of_trace_reciprocity C h
    (enoTraceMatrix_reciprocity_of_multiplicity_involutions C h) σ i

/-- Multiplicity involutivity implies the global Galois dimension bounds. -/
theorem globalDimension_galois_bounds_of_multiplicity_involutions
    (C : Ground.BraidedFusionCategory.{v,u})
    (h : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1) (σ : ℂ ≃+* ℂ) :
    ∃ D : ℝ, 1 ≤ D ∧ D ≤ Ground.globalFPDimension C ∧ σ (Ground.globalDimension C) = (D : ℂ) :=
  globalDimension_galois_bounds_of_trace_reciprocity C h
    (enoTraceMatrix_reciprocity_of_multiplicity_involutions C h) σ
end PropertyF.Ground.Dimensions
