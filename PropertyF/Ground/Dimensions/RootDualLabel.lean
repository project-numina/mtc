module
public import PropertyF.Ground.Dimensions.ENOReciprocity
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Dimensions.SimpleHomBasis

/-! # Dual labels and reciprocity

Frobenius reciprocity and the fourth-dual tensor law imply trace reciprocity on simple labels.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- It suffices to prove the fourth-dual tensor law on simple pairs; the
construction uses no assumption about that law on arbitrary objects. -/
theorem positive_spherical_of_simple_fourth_and_reciprocity
    (hfourth : ∀ i j : Fin (rank C),
      fourthDualTensorLaw (simples C i) (simples C j))
    (htranspose : ENOTraceMatrixReciprocity C)
    (hpu : PseudoUnitary C) :
    HasFPSphericalStructure C :=
  let hinv : MultiplicityDefectsInvolutive C := fun i j k ↦
    multiplicityDefect_involution_of_tensor_square C k
      ((rootTensor_square_eq_fourthDual_tensor C _ _).trans (hfourth i j).symm)
  positive_spherical_of_matrix_identities C hinv
    (fun i j ↦ enoTraceMatrix_eigenvector_of_involutions C (hinv i j))
    (fun i ↦ squaredNorm_eq_root_norm_sq_of_reciprocity C hinv htranspose i) hpu


end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
local instance (i : Fin (rank C)) : Simple (simples C i) := simples_simple C i
variable (i j k : Fin (rank C))

/-- Braiding identifies the right dual with the chosen left-dual representative. -/
def rightDualLabelIso :
    (simples C i)ᘁ ≅ simples C (dualIndex C i) :=
  leftDualIso (BraidedCategory.exactPairing_swap (simples C i) ((simples C i)ᘁ))
    HasLeftDual.exact ≪≫ Classical.choice (dualIndex_iso C i)

/-- Actual Frobenius reciprocity using the chosen dual-label identification. -/
def enoFrobeniusEquiv :
    (simples C i ⊗ simples C j ⟶ simples C k) ≃ₗ[ℂ]
      (simples C j ⟶ simples C (dualIndex C i) ⊗ simples C k) := by
  let Xi := simples C i
  let Xj := simples C j
  let Xk := simples C k
  letI : ExactPairing (Xiᘁ) Xi := BraidedCategory.exactPairing_swap Xi (Xiᘁ)
  exact (tensorLeftHomLinearEquiv (k := ℂ) Xj (Xiᘁ) Xi Xk).trans
    (Linear.homCongr ℂ (Iso.refl Xj) (rightDualLabelIso C i ⊗ᵢ Iso.refl Xk))

/-- The actual ENO Frobenius/semisimple reciprocity isomorphism: the dual of
one fusion multiplicity space is the dual-label multiplicity space. -/
def enoReciprocityEquiv :
    Module.Dual ℂ (simples C k ⟶ simples C i ⊗ simples C j) ≃ₗ[ℂ]
      (simples C j ⟶ simples C (dualIndex C i) ⊗ simples C k) :=
  (simpleHomPairingEquiv (simples C k) (simples C i ⊗ simples C j)).symm.trans
    (enoFrobeniusEquiv C i j k)

/-- The categorical operator intertwining under the actual reciprocity
isomorphism implies ENO's trace-transpose relation. -/
theorem trace_reciprocity_of_intertwining
    (hintertwine : ∀ i j k
      (v : Module.Dual ℂ (simples C j ⟶ simples C i ⊗ simples C k)),
      enoReciprocityEquiv C i k j
        (Module.Dual.transpose (multiplicityDefect C i k j).toLinearMap v) =
      rootDualSign C i • (multiplicityDefect C (dualIndex C i) j k)
        (enoReciprocityEquiv C i k j v)) :
    ENOTraceMatrixReciprocity C := by
  intro i j k
  let E := enoReciprocityEquiv C i k j
  let A := (multiplicityDefect C i k j).toLinearMap
  let B := (multiplicityDefect C (dualIndex C i) j k).toLinearMap
  let : FiniteDimensional ℂ (simples C j ⟶ simples C i ⊗ simples C k) :=
    IsFusionCategory.hom_finite _ _
  let : FiniteDimensional ℂ (simples C k ⟶ simples C (dualIndex C i) ⊗ simples C j) :=
    IsFusionCategory.hom_finite _ _
  have ht : LinearMap.trace ℂ _ A = rootDualSign C i * LinearMap.trace ℂ _ B := by
    simpa only [LinearMap.trace_conj', LinearMap.trace_transpose', map_smul, smul_eq_mul] using
      congrArg (LinearMap.trace ℂ _) (show E.conj (Module.Dual.transpose A) =
        rootDualSign C i • B from by
          ext w
          obtain ⟨v, rfl⟩ := E.surjective w
          simpa [E, A, B, LinearEquiv.conj_apply] using hintertwine i j k v)
  change LinearMap.trace ℂ _ B = rootDualSign C i * LinearMap.trace ℂ _ A
  rw [ht, ← mul_assoc, rootDualSign_sq, one_mul]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
local instance (i : Fin (rank C)) : Simple (simples C i) := simples_simple C i
/-- The ENO reciprocity equivalence is the composition pairing followed by
the actual Frobenius reciprocity map. -/
theorem enoReciprocityEquiv_pairing
    {i j k : Fin (rank C)}
    (g : simples C i ⊗ simples C j ⟶ simples C k) :
    enoReciprocityEquiv C i j k (simpleHomPairingEquiv (simples C k) (simples C i ⊗ simples C j) g) =
      enoFrobeniusEquiv C i j k g := by simp [enoReciprocityEquiv]

/-- It is enough to prove the defect compatibility on ordinary categorical
morphisms before applying the perfect-pairing duality. -/
theorem trace_reciprocity_of_frobenius_defect
    (hcompat : ∀ i j k (g : simples C i ⊗ simples C k ⟶ simples C j),
      enoFrobeniusEquiv C i k j ((rootTensorDefect C (simples C i) (simples C k)).hom ≫ g) =
      rootDualSign C i • (enoFrobeniusEquiv C i k j g ≫
        (rootTensorDefect C (simples C (dualIndex C i)) (simples C j)).hom)) :
    ENOTraceMatrixReciprocity C := by
  apply trace_reciprocity_of_intertwining C
  intro i j k v
  let : Simple (simples C j) := simples_simple C j
  let P := simpleHomPairingEquiv (simples C j) (simples C i ⊗ simples C k)
  obtain ⟨g, rfl⟩ := P.surjective v
  let : FiniteDimensional ℂ (simples C j ⟶ simples C j) := IsFusionCategory.hom_finite _ _
  have hn : Module.Dual.transpose (Linear.rightComp ℂ (simples C j)
      (rootTensorDefect C (simples C i) (simples C k)).hom) (P g) =
      P ((rootTensorDefect C (simples C i) (simples C k)).hom ≫ g) :=
    (simpleHomPairing_natural (k := ℂ) g _).symm
  have hm : (multiplicityDefect C i k j).toLinearMap =
      Linear.rightComp ℂ (simples C j) (rootTensorDefect C (simples C i) (simples C k)).hom := by
    ext f
    exact multiplicityDefect_apply C f
  rw [hm, hn, enoReciprocityEquiv_pairing, enoReciprocityEquiv_pairing, hcompat]
  simp [multiplicityDefect_apply]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The ENO signs agree on the chosen dual label. -/
theorem rootDualSign_dual (i : Fin (rank C)) :
    rootDualSign C (dualIndex C i) = rootDualSign C i := by
  let X := simples C i
  let Y := simples C (dualIndex C i)
  let : Simple X := simples_simple C i
  let : Simple Y := simples_simple C _
  let : Simple (Xᘁ) := simple_rightDual X
  have he : squaredNorm C Y = squaredNorm C X :=
    (target_squaredNorm_iso C (rightDualLabelIso C i)).symm.trans (target_squaredNorm_rightDual C X)
  rw [squaredNorm_eq_rootDualSign_mul, squaredNorm_eq_rootDualSign_mul] at he
  rw [Ground.dualIndex_involutive] at he
  apply mul_right_cancel₀ (mul_ne_zero (rootDimension_ne_zero C i)
    (rootDimension_ne_zero C (dualIndex C i)))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using he
end PropertyF.Ground.Dimensions

end
