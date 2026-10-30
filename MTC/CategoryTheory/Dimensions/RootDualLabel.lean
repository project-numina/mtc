module
public import MTC.CategoryTheory.Dimensions.ENOReciprocity
public import MTC.CategoryTheory.Dimensions.DualTensorNaturality
public import MTC.CategoryTheory.Dimensions.SimpleHomBasis

open MTC.Fusion

open MTC.Braided

/-! # Dual labels and reciprocity

`enoFrobeniusEquiv` and `enoReciprocityEquiv` realize Frobenius reciprocity on
the chosen simple objects. Compatibility of the tensor defect with these
equivalences yields trace reciprocity, while `rootDualSign_dual` compares the
signs on a label and its dual.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})

/-- The fourth-dual tensor law on pairs of chosen simple objects. -/
abbrev SimpleFourthDualTensorLaw : Prop :=
  ∀ i j : Fin (rank C), fourthDualTensorLaw (simples C i) (simples C j)

variable {C} in
/-- It suffices to prove the fourth-dual tensor law on simple pairs; the
construction uses no assumption about that law on arbitrary objects. -/
theorem positive_spherical_of_simple_fourth_and_reciprocity
    (hfourth : SimpleFourthDualTensorLaw C) (htranspose : ENOTraceMatrixReciprocity C)
    (hpu : PseudoUnitary C) : HasFPSphericalStructure C :=
  let hinv : MultiplicityDefectsInvolutive C := fun i j k ↦
    multiplicityDefect_involution_of_tensor_square C k
      ((rootTensor_square_eq_fourthDual_tensor C _ _).trans (hfourth i j).symm)
  positive_spherical_of_matrix_identities hinv
    (fun i j ↦ enoTraceMatrix_eigenvector_of_involutions (hinv i j))
    (fun i ↦ squaredNorm_eq_root_norm_sq_of_reciprocity hinv htranspose i) hpu


end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] IsFusionCategory.hom_finite
local instance (i : Fin (rank C)) : Simple (simples C i) := simples_simple C i
variable (i j k : Fin (rank C))

/-- Actual Frobenius reciprocity using the chosen dual-label identification. -/
def enoFrobeniusEquiv :
    (simples C i ⊗ simples C j ⟶ simples C k) ≃ₗ[ℂ]
      (simples C j ⟶ simples C (dualIndex C i) ⊗ simples C k) := by
  letI : ExactPairing ((simples C i)ᘁ) (simples C i) :=
    BraidedCategory.exactPairing_swap _ _
  exact (tensorLeftHomLinearEquiv (k := ℂ) _ _ _ _).trans
    (Linear.homCongr ℂ (Iso.refl _) (rightDualLabelIso C i ⊗ᵢ Iso.refl _))

/-- The actual ENO Frobenius/semisimple reciprocity isomorphism: the dual of
one fusion multiplicity space is the dual-label multiplicity space. -/
def enoReciprocityEquiv :
    Module.Dual ℂ (simples C k ⟶ simples C i ⊗ simples C j) ≃ₗ[ℂ]
      (simples C j ⟶ simples C (dualIndex C i) ⊗ simples C k) :=
  (simpleHomPairingEquiv (simples C k) (simples C i ⊗ simples C j)).symm.trans
    (enoFrobeniusEquiv C i j k)

variable {C} in
/-- The categorical operator intertwining under the actual reciprocity
isomorphism implies ENO's trace-transpose relation. -/
theorem trace_reciprocity_of_intertwining
    (hintertwine : ∀ i j k
      (v : Module.Dual ℂ (simples C j ⟶ simples C i ⊗ simples C k)),
      enoReciprocityEquiv C i k j
        (Module.Dual.transpose (multiplicityDefect C i k j).toLinearMap v) =
      (rootDualSign C i).1 • (multiplicityDefect C (dualIndex C i) j k)
        (enoReciprocityEquiv C i k j v)) :
    ENOTraceMatrixReciprocity C := by
  intro i j k
  let E := enoReciprocityEquiv C i k j
  let A := (multiplicityDefect C i k j).toLinearMap
  let B := (multiplicityDefect C (dualIndex C i) j k).toLinearMap
  have ht : LinearMap.trace ℂ _ A = (rootDualSign C i).1 * LinearMap.trace ℂ _ B := by
    simpa only [LinearMap.trace_conj', LinearMap.trace_transpose', map_smul, smul_eq_mul] using
      congrArg (LinearMap.trace ℂ _) (show E.conj (Module.Dual.transpose A) =
        (rootDualSign C i).1 • B from LinearMap.ext fun w ↦ by
          simpa [E, A, B, LinearEquiv.conj_apply] using hintertwine i j k (E.symm w))
  change LinearMap.trace ℂ _ B = (rootDualSign C i).1 * LinearMap.trace ℂ _ A
  rw [ht, ← mul_assoc, (rootDualSign C i).2.1, one_mul]

end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
local instance (i : Fin (rank C)) : Simple (simples C i) := simples_simple C i
variable {C} in
/-- It is enough to prove the defect compatibility on ordinary categorical
morphisms before applying the perfect-pairing duality. -/
theorem trace_reciprocity_of_frobenius_defect
    (hcompat : ∀ i j k (g : simples C i ⊗ simples C k ⟶ simples C j),
      enoFrobeniusEquiv C i k j ((rootTensorDefect C (simples C i) (simples C k)).hom ≫ g) =
      (rootDualSign C i).1 • (enoFrobeniusEquiv C i k j g ≫
        (rootTensorDefect C (simples C (dualIndex C i)) (simples C j)).hom)) :
    ENOTraceMatrixReciprocity C :=
  trace_reciprocity_of_intertwining fun i j k v ↦ by
    obtain ⟨g, rfl⟩ := (simpleHomPairingEquiv (simples C j) (simples C i ⊗ simples C k)).surjective v
    have hm : (multiplicityDefect C i k j).toLinearMap =
        Linear.rightComp ℂ (simples C j) (rootTensorDefect C (simples C i) (simples C k)).hom :=
      LinearMap.ext fun f ↦ multiplicityDefect_apply C f
    rw [hm]
    erw [← simpleHomPairingEquiv_natural]
    simp [enoReciprocityEquiv, hcompat, multiplicityDefect_apply]

end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The ENO signs agree on the chosen dual label. -/
theorem rootDualSign_dual (i : Fin (rank C)) :
    (rootDualSign C (dualIndex C i)).1 = (rootDualSign C i).1 := by
  let : Simple (simples C i) := simples_simple C i
  have he := (target_squaredNorm_iso C (rightDualLabelIso C i)).symm.trans
    (target_squaredNorm_rightDual (simples C i))
  rw [squaredNorm_eq_rootDualSign_mul, squaredNorm_eq_rootDualSign_mul,
    MTC.Fusion.dualIndex_involutive] at he
  apply mul_right_cancel₀ (mul_ne_zero (rootDimension_ne_zero i)
    (rootDimension_ne_zero (dualIndex C i)))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using he
end MTC.CategoryTheory.Dimensions

end
