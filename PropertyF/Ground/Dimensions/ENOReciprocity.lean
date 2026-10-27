module
public import PropertyF.Ground.Dimensions.RootNorm
public import PropertyF.Ground.Dimensions.ENOReduction

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix ComplexOrder
namespace PropertyF.Ground.Dimensions
universe v u

/-- ENO's trace reciprocity identifies the dual root dimension with the
signed complex conjugate of the original one. -/
theorem rootDimension_dual_conjugate_of_trace_reciprocity
    (C : Ground.BraidedFusionCategory.{v,u})
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (htranspose : ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j)
    (i : Fin (Ground.rank C)) :
    rootDimension C (Ground.dualIndex C i) = rootDualSign C i * star (rootDimension C i) := by
  classical
  let A : Matrix (Fin (Ground.rank C)) (Fin (Ground.rank C)) ℂ := enoTraceMatrix C i
  let d := rootDimension C
  let ε := rootDualSign C i
  have hε : ε * ε = 1 := rootDualSign_sq C i
  have hεstar : star ε = ε := by
    rcases mul_self_eq_one_iff.mp hε with h | h <;> simp [h]
  have hA : ∀ j k, star (A j k) = A j k := by
    intro j k
    obtain ⟨n, hn, _⟩ := multiplicityDefect_trace_integer_bound C i j k (hinv i j k)
    change star (LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap) =
      LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap
    rw [hn]
    simp
  have hv : d ≠ 0 := by
    intro hz
    apply rootDimension_ne_zero C (Ground.unitIndex C)
    exact congrFun hz (Ground.unitIndex C)
  have h : A *ᵥ d = d i • d := by
    ext j
    change (∑ k, enoTraceMatrix C i j k * rootDimension C k) = rootDimension C i * rootDimension C j
    exact enoTraceMatrix_eigenvector_of_involutions C i j (hinv i j)
  have ht : Aᵀ *ᵥ d = (ε * d (Ground.dualIndex C i)) • d := by
    ext j
    change (∑ k, enoTraceMatrix C i k j * rootDimension C k) =
      (ε * rootDimension C (Ground.dualIndex C i)) * rootDimension C j
    have he := enoTraceMatrix_eigenvector_of_involutions C (Ground.dualIndex C i) j
      (hinv (Ground.dualIndex C i) j)
    simp_rw [htranspose] at he
    calc
      _ = ε * ∑ k, ((ε * enoTraceMatrix C i k j) * rootDimension C k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        calc
          _ = (ε * ε) * (enoTraceMatrix C i k j * rootDimension C k) := by rw [hε, one_mul]
          _ = _ := by ring
      _ = ε * (rootDimension C (Ground.dualIndex C i) * rootDimension C j) := by rw [he]
      _ = _ := by ring
  have hc := conjugate_of_transpose_eigenvector A hA d hv (d i) (ε * d (Ground.dualIndex C i)) h ht
  have hc' := congrArg star hc
  simp only [star_mul, star_star, hεstar] at hc'
  calc
    d (Ground.dualIndex C i) = (ε * ε) * d (Ground.dualIndex C i) := by rw [hε, one_mul]
    _ = ε * (ε * d (Ground.dualIndex C i)) := by ring
    _ = ε * star (d i) := by rw [hc']

/-- ENO's trace reciprocity proves the intrinsic root-norm identity. -/
theorem squaredNorm_eq_rootDimension_norm_sq_of_trace_reciprocity
    (C : Ground.BraidedFusionCategory.{v,u})
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (htranspose : ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j) (i : Fin (Ground.rank C)) :
    Ground.squaredNorm C (Ground.simples C i) = ((‖rootDimension C i‖ ^ 2 : ℝ) : ℂ) := by
  rw [squaredNorm_eq_rootDualSign_mul C i,
    rootDimension_dual_conjugate_of_trace_reciprocity C hinv htranspose i]
  calc
    _ = rootDimension C i * star (rootDimension C i) := by
      calc
        _ = (rootDualSign C i * rootDualSign C i) *
          (rootDimension C i * star (rootDimension C i)) := by ring
        _ = _ := by rw [rootDualSign_sq, one_mul]
    _ = _ := by simpa using Complex.mul_conj' (rootDimension C i)

/-- Pseudo-unitarity yields the positive spherical structure once the two
pure dual coherence identities and ENO's trace reciprocity are established. -/
theorem eno_pseudoUnitary_yields_positive_spherical_of_reciprocity
    (C : Ground.BraidedFusionCategory.{v,u})
    (hnat : ∀ {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y'),
      (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
        (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ))
    (hfourth : ∀ X Y : C.Obj, (fourthDualIso C (X ⊗ Y)).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ))
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
    · exact (hnat ((fourthDualRootNaturalIso C).app (Ground.simples C i)).hom
        ((fourthDualRootNaturalIso C).app (Ground.simples C j)).hom).symm
    · exact hfourth _ _
  apply eno_pseudoUnitary_yields_positive_spherical_of_coherence_and_norm C hnat hfourth _ hpu
  intro i
  exact squaredNorm_eq_rootDimension_norm_sq_of_trace_reciprocity C hinv htranspose i

end PropertyF.Ground.Dimensions
