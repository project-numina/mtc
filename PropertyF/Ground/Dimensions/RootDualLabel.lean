module
public import PropertyF.Ground.Dimensions.ENOReciprocity
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Dimensions.SimplePairing

/-! # Dual labels and reciprocity

Frobenius reciprocity and the fourth-dual tensor law imply trace reciprocity on simple labels.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
/-- It suffices to prove the fourth-dual tensor law on simple pairs; the
construction uses no assumption about that law on arbitrary objects. -/
theorem eno_pseudoUnitary_yields_positive_spherical_of_simple_fourth_and_reciprocity
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

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
/-- Braiding identifies the right dual with the chosen left-dual representative. -/
def rightDualLabelIso (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    (Ground.simples C i)ᘁ ≅ Ground.simples C (Ground.dualIndex C i) :=
  leftDualIso (BraidedCategory.exactPairing_swap (Ground.simples C i) ((Ground.simples C i)ᘁ))
    HasLeftDual.exact ≪≫ Classical.choice (Ground.dualIndex_iso C i)

/-- The actual ENO Frobenius/semisimple reciprocity isomorphism: the dual of
one fusion multiplicity space is the dual-label multiplicity space. -/
def enoReciprocityEquiv (C : Ground.BraidedFusionCategory.{v,u})
    (i j k : Fin (Ground.rank C)) :
    Module.Dual ℂ (Ground.simples C k ⟶ Ground.simples C i ⊗ Ground.simples C j) ≃ₗ[ℂ]
      (Ground.simples C j ⟶ Ground.simples C (Ground.dualIndex C i) ⊗ Ground.simples C k) := by
  let Xi := Ground.simples C i
  let Xj := Ground.simples C j
  let Xk := Ground.simples C k
  letI : ExactPairing (Xiᘁ) Xi := BraidedCategory.exactPairing_swap Xi (Xiᘁ)
  let eq1 := (simpleHomPairingEquiv C k (Xi ⊗ Xj)).symm
  let eq2 := Ground.tensorLeftHomLinearEquiv Xj (Xiᘁ) Xi Xk
  let eq3 := Linear.homCongr ℂ (Iso.refl Xj) (rightDualLabelIso C i ⊗ᵢ Iso.refl Xk)
  exact eq1.trans (eq2.trans eq3)

/-- The categorical operator intertwining under the actual reciprocity
isomorphism implies ENO's trace-transpose relation. -/
theorem enoTraceMatrix_reciprocity_of_operator_intertwining
    (hintertwine : ∀ i j k
      (v : Module.Dual ℂ (Ground.simples C j ⟶ Ground.simples C i ⊗ Ground.simples C k)),
      enoReciprocityEquiv C i k j
        (Module.Dual.transpose (multiplicityDefect C i k j).toLinearMap v) =
      rootDualSign C i • (multiplicityDefect C (Ground.dualIndex C i) j k)
        (enoReciprocityEquiv C i k j v)) :
    ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k =
      rootDualSign C i * enoTraceMatrix C i k j := by
  intro i j k
  let E := enoReciprocityEquiv C i k j
  let A := (multiplicityDefect C i k j).toLinearMap
  let B := (multiplicityDefect C (Ground.dualIndex C i) j k).toLinearMap
  have hconj : E.conj (Module.Dual.transpose A) = rootDualSign C i • B := by
    ext w
    obtain ⟨v, rfl⟩ := E.surjective w
    simpa [E, A, B, LinearEquiv.conj_apply] using hintertwine i j k v
  let : FiniteDimensional ℂ (Ground.simples C j ⟶ Ground.simples C i ⊗ Ground.simples C k) :=
    Ground.IsFusionCategory.hom_finite _ _
  let : FiniteDimensional ℂ (Ground.simples C k ⟶ Ground.simples C (Ground.dualIndex C i) ⊗ Ground.simples C j) :=
    Ground.IsFusionCategory.hom_finite _ _
  have ht := congrArg (LinearMap.trace ℂ _) hconj
  simp only [LinearMap.trace_conj', LinearMap.trace_transpose', map_smul, smul_eq_mul] at ht
  have hs := rootDualSign_sq C i
  change LinearMap.trace ℂ _ A = rootDualSign C i * LinearMap.trace ℂ _ B at ht
  change LinearMap.trace ℂ _ B = rootDualSign C i * LinearMap.trace ℂ _ A
  calc
    _ = (rootDualSign C i * rootDualSign C i) * LinearMap.trace ℂ _ B := by rw [hs, one_mul]
    _ = rootDualSign C i * (rootDualSign C i * LinearMap.trace ℂ _ B) := by ring
    _ = _ := by rw [← ht]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
/-- Actual Frobenius reciprocity using the chosen dual-label identification. -/
def enoFrobeniusEquiv (C : Ground.BraidedFusionCategory.{v,u})
    (i j k : Fin (Ground.rank C)) :
    (Ground.simples C i ⊗ Ground.simples C j ⟶ Ground.simples C k) ≃ₗ[ℂ]
      (Ground.simples C j ⟶ Ground.simples C (Ground.dualIndex C i) ⊗ Ground.simples C k) := by
  let Xi := Ground.simples C i
  let Xj := Ground.simples C j
  let Xk := Ground.simples C k
  letI : ExactPairing (Xiᘁ) Xi := BraidedCategory.exactPairing_swap Xi (Xiᘁ)
  exact (Ground.tensorLeftHomLinearEquiv Xj (Xiᘁ) Xi Xk).trans
    (Linear.homCongr ℂ (Iso.refl Xj) (rightDualLabelIso C i ⊗ᵢ Iso.refl Xk))

/-- The ENO reciprocity equivalence is the composition pairing followed by
the actual Frobenius reciprocity map. -/
theorem enoReciprocityEquiv_pairing
    (i j k : Fin (Ground.rank C))
    (g : Ground.simples C i ⊗ Ground.simples C j ⟶ Ground.simples C k) :
    enoReciprocityEquiv C i j k (simpleHomPairingEquiv C k (Ground.simples C i ⊗ Ground.simples C j) g) =
      enoFrobeniusEquiv C i j k g := by simp [enoReciprocityEquiv, enoFrobeniusEquiv]

/-- It is enough to prove the defect compatibility on ordinary categorical
morphisms before applying the perfect-pairing duality. -/
theorem enoTraceMatrix_reciprocity_of_frobenius_defect
    (hcompat : ∀ i j k (g : Ground.simples C i ⊗ Ground.simples C k ⟶ Ground.simples C j),
      enoFrobeniusEquiv C i k j ((rootTensorDefect C (Ground.simples C i) (Ground.simples C k)).hom ≫ g) =
      rootDualSign C i • (enoFrobeniusEquiv C i k j g ≫
        (rootTensorDefect C (Ground.simples C (Ground.dualIndex C i)) (Ground.simples C j)).hom)) :
    ∀ i j k, enoTraceMatrix C (Ground.dualIndex C i) j k = rootDualSign C i * enoTraceMatrix C i k j := by
  apply enoTraceMatrix_reciprocity_of_operator_intertwining C
  intro i j k v
  let : Simple (Ground.simples C j) := Ground.simples_simple C j
  let P := simpleHomPairingEquiv C j (Ground.simples C i ⊗ Ground.simples C k)
  let g := P.symm v
  have hv : P g = v := P.apply_symm_apply v
  rw [← hv]
  have hn := simpleHomPairing_natural C (Ground.simples C j)
    (Ground.simples C i ⊗ Ground.simples C k) g
    (rootTensorDefect C (Ground.simples C i) (Ground.simples C k)).hom
  have hm : (multiplicityDefect C i k j).toLinearMap =
      Linear.rightComp ℂ (Ground.simples C j) (rootTensorDefect C (Ground.simples C i) (Ground.simples C k)).hom := by
    ext f
    exact multiplicityDefect_apply C i k j f
  rw [hm]
  change P ((rootTensorDefect C (Ground.simples C i) (Ground.simples C k)).hom ≫ g) =
    Module.Dual.transpose (Linear.rightComp ℂ (Ground.simples C j)
      (rootTensorDefect C (Ground.simples C i) (Ground.simples C k)).hom) (P g) at hn
  rw [← hn, enoReciprocityEquiv_pairing, enoReciprocityEquiv_pairing, hcompat]
  simp [multiplicityDefect_apply]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The ENO signs agree on the chosen dual label. -/
theorem rootDualSign_dual (i : Fin (Ground.rank C)) :
    rootDualSign C (Ground.dualIndex C i) = rootDualSign C i := by
  let X := Ground.simples C i
  let Y := Ground.simples C (Ground.dualIndex C i)
  let : Simple X := Ground.simples_simple C i
  let : Simple Y := Ground.simples_simple C _
  let : Simple (Xᘁ) := Ground.simple_rightDual C X
  have he : Ground.squaredNorm C Y = Ground.squaredNorm C X := by
    rw [← target_squaredNorm_iso C (rightDualLabelIso C i)]
    exact target_squaredNorm_rightDual C X
  rw [squaredNorm_eq_rootDualSign_mul, squaredNorm_eq_rootDualSign_mul] at he
  rw [Ground.dualIndex_involutive] at he
  have he' := rootDimension_ne_zero C (Ground.dualIndex C i)
  have hc : rootDualSign C (Ground.dualIndex C i) *
      (rootDimension C i * rootDimension C (Ground.dualIndex C i)) =
      rootDualSign C i * (rootDimension C i * rootDimension C (Ground.dualIndex C i)) := by
    calc
      _ = rootDualSign C (Ground.dualIndex C i) * rootDimension C (Ground.dualIndex C i) * rootDimension C i := by ring
      _ = rootDualSign C i * rootDimension C i * rootDimension C (Ground.dualIndex C i) := he
      _ = _ := by ring
  exact mul_right_cancel₀ (mul_ne_zero (rootDimension_ne_zero C i) he') hc
end PropertyF.Ground.Dimensions

end
