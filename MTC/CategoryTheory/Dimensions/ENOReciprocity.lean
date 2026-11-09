module
public import MTC.CategoryTheory.Dimensions.DimensionCharacter
public import MTC.PropertyF.Reduction.CharacterReality
public import MTC.Modular.SMatrix
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import MTC.CategoryTheory.Dimensions.MultiplicityDefect
public import MTC.CategoryTheory.Dimensions.ENOMatrices
public import MTC.CategoryTheory.Dimensions.SimpleHomBasis
public import MTC.CategoryTheory.Dimensions.TensorExtension

open MTC.PropertyF.Reduction

open MTC.Fusion

open MTC.Braided


/-! # Reciprocity and spherical dimensions

Character duality, phase normalization and trace reciprocity control the dimensions of simple objects.

## Main results

* `positive_spherical_of_matrix_identities`: uses trace matrix identities to construct a positive spherical structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CategoryTheory.Dimensions
universe v u
variable {k : Type*} [Field k] {D : Type u} [Category.{v} D]
  [MonoidalCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]

omit [RightRigidCategory D] in
/-- Scalar multiples with the same double-dual square differ by a sign. -/
theorem scalar_sq_eq_one_of_same_square {X : D} [HasRightDual X] [HasRightDual (Xᘁ)]
    [HasRightDual ((Xᘁ)ᘁ)] [HasRightDual (((Xᘁ)ᘁ)ᘁ)] [Simple X]
    (a b : X ≅ (Xᘁ)ᘁ) (z : k) (hz : b.hom = z • a.hom)
    (hsq : b.hom ≫ ((b.homᘁ)ᘁ) = a.hom ≫ ((a.homᘁ)ᘁ)) : z * z = 1 :=
  smul_left_injective k (mono_ne_zero_of_id_ne_zero
    (a ≪≫ rightDualIsoMap (rightDualIsoMap a)).hom (id_nonzero X)) (by
      simpa [rightDualIsoMap, hz, rightAdjointMate_smul, smul_smul] using hsq)

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] IsFusionCategory.hom_finite
set_option backward.isDefEq.respectTransparency false in
/-- The inverse dual of a natural fourth-dual square root is also a root at
the dual object. -/
theorem inverseDualRoot_square (X : C.Obj) :
    (rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm.hom ≫
      (((((rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm.hom)ᘁ)ᘁ)) =
      (fourthDualIso (Xᘁ)).hom := by
  let j : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  have h : j ≪≫ rightDualIsoMap (rightDualIsoMap j) = fourthDualIso X :=
    Iso.ext (congrArg (fun n ↦ (n.app X).hom) (fourthDualRootNaturalSquare_eq C))
  simpa only [fourthDualIso_rightDual, Iso.trans_inv, rightDualIsoMap, Iso.symm_hom, Iso.symm_inv,
    comp_rightAdjointMate] using congrArg (fun (e : X ≅ _) ↦ e.invᘁ) h

set_option backward.isDefEq.respectTransparency false in
/-- On a simple object, the natural root on the dual differs from the inverse
dual root by a sign. -/
theorem rootDual_differs_by_sign (X : C.Obj)
    [Simple X] : ∃ ε : ℂ, ε * ε = 1 ∧
      ((fourthDualRootNaturalIso C).app (Xᘁ)).hom =
        ε • (rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm.hom :=
  letI : Simple (Xᘁ) := simple_rightDual X
  let l : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm
  let k : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (fourthDualRootNaturalIso C).app (Xᘁ)
  (isomorphisms_scalar (k := ℂ) l k).elim fun ε ⟨_, he⟩ ↦
    ⟨ε, scalar_sq_eq_one_of_same_square l k ε he
      ((congrArg (fun n ↦ (n.app (Xᘁ)).hom) (fourthDualRootNaturalSquare_eq C)).trans
        (inverseDualRoot_square C X).symm), he⟩

end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
local instance (i : Fin (rank C)) : Simple (simples C i) := simples_simple C i
/-- The sign comparing the root on a simple's dual to the inverse dual root. -/
noncomputable def rootDualSign (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) : {ε : ℂ // ε * ε = 1 ∧
      ((fourthDualRootNaturalIso C).app ((simples C i)ᘁ)).hom =
        ε • (rightDualIsoMap ((fourthDualRootNaturalIso C).app (simples C i))).symm.hom} :=
  Classical.indefiniteDescription _ (rootDual_differs_by_sign C (simples C i))

/-- The trace matrices of dual simples are transposes up to the dual-root sign. -/
abbrev ENOTraceMatrixReciprocity (C : BraidedFusionCategory.{v,u}) : Prop :=
  ∀ i j k, enoTraceMatrix C (dualIndex C i) j k =
    (rootDualSign C i).1 * enoTraceMatrix C i k j

/-- Braiding identifies the right dual with the chosen left-dual representative. -/
def rightDualLabelIso (C : BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    (simples C i)ᘁ ≅ simples C (dualIndex C i) :=
  leftDualIso (BraidedCategory.exactPairing_swap (simples C i) ((simples C i)ᘁ))
    HasLeftDual.exact ≪≫ Classical.choice (dualIndex_iso i)

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- Intrinsic simple norms are signed products of the root dimensions of a
simple and its dual, using the same sign as the dual-root component. -/
theorem squaredNorm_eq_rootDualSign_mul
    (i : Fin (rank C)) :
    squaredNorm C (simples C i) = (rootDualSign C i).1 * rootDimension C i *
      rootDimension C (dualIndex C i) := by
  let X := simples C i
  let j : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  let k : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (fourthDualRootNaturalIso C).app (Xᘁ)
  have hq : unitScalar C (rightQuantumTrace k) = rootDimension C (dualIndex C i) := congrArg _
    ((rootTrace_id C (Xᘁ)).symm.trans (rootTrace_id_iso C (rightDualLabelIso C i)))
  rw [target_squaredNorm_choice_independent j, leftQuantumTrace_eq_rightDual j,
    ← (show unitScalar C (rightQuantumTrace j) = rootDimension C i from
      congrArg (unitScalar C) (rootTrace_id C X).symm), ← hq,
    rightQuantumTrace_smul_hom ((rootDualSign C i).2.2)]
  simp only [MTC.Fusion.unitScalar_eq_equiv, map_smul, smul_eq_mul]
  rw [mul_mul_mul_comm, (rootDualSign C i).2.1, one_mul]

end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
variable {C} in
/-- A pivotal structure whose simple dimensions and intrinsic norms are the
FP values is spherical. -/
theorem spherical_of_fp_dimensions_and_squaredNorms {p : PivotalStructure (C := C.Obj)}
    (hdim : ∀ i, pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (hnorm : ∀ i, squaredNorm C (simples C i) =
      ((fpSimple C i ^ 2 : ℝ) : ℂ)) : p.IsSpherical :=
  (isSpherical_iff_simple_dimensions C p).2 fun i ↦ by
    let X := simples C i
    let : Simple X := simples_simple C i
    have hh := target_squaredNorm_choice_independent (p.iso X)
    rw [← rightTrace_id, ← leftTrace_id, ← pivotalDimension, hdim i, hnorm i, Complex.ofReal_pow] at hh
    apply (MTC.Fusion.unitScalarEquiv C).injective
    rw [← MTC.Fusion.unitScalar_eq_equiv, ← MTC.Fusion.unitScalar_eq_equiv, ← pivotalDimension, hdim i]
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (fpSimple_pos C i)))
      (by simpa [pow_two] using hh.symm)

variable {C} in
/-- ENO's trace-matrix bound and the root-norm identity turn global
pseudo-unitarity into pointwise FP saturation. -/
theorem eno_root_norm_saturation_of_pseudoUnitary
    (hinv : MultiplicityDefectsInvolutive C) (heig : ENOTraceMatrixEigenvector C)
    (hnorm : RootNormIdentity C) (hpu : PseudoUnitary C) :
    ∀ i, ‖rootDimension C i‖ = fpSimple C i :=
  norm_saturation_of_pseudoUnitary
    (fun i => rootDimension_norm_le_fp_of_trace_matrix (hinv i) (heig i)) hnorm hpu

end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] IsFusionCategory.hom_finite
/-- A phase-twisted natural root becomes pivotal when its scaled multiplicity
operators are identities. -/
def rootPhasePivotal (C : BraidedFusionCategory.{v,u})
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hdef : ScaledMultiplicityDefectsTrivial C c)
    (hunit : RootSignUnitLaw C c hc) : PivotalStructure (C := C.Obj) where
  iso X := (rootSignTwist C c hc).app X
  naturality {_X _Y} f := (rootSignTwist C c hc).hom.naturality f
  tensor X Y := doubleDualTensor_extension C (rootSignTwist C c hc)
    (fun i j ↦ congrArg Iso.hom (rootPhaseTensor_compatible_of_scaled_defects hc (hdef i j))) X Y
  unit := hunit

set_option backward.isDefEq.respectTransparency false in
variable {C} in
theorem rootPhasePivotal_dimension {c : Fin (rank C) → ℂ} (hc : ∀ i, c i ≠ 0)
    (hdef : ScaledMultiplicityDefectsTrivial C c) (hunit : RootSignUnitLaw C c hc)
    (i : Fin (rank C)) : pivotalDimension C (rootPhasePivotal C c hc hdef hunit) (simples C i) =
      c i * rootDimension C i := by
  simpa only [pivotalDimension, rightTrace_id, rootPhasePivotal] using
    rootSignQuantumTrace_simple hc i

/-- The root dimension normalized by the Frobenius–Perron dimension. -/
abbrev normalizedRootDimension (C : BraidedFusionCategory.{v,u}) (i : Fin (rank C)) : ℂ :=
  rootDimension C i / (fpSimple C i : ℂ)

variable (hinv : MultiplicityDefectsInvolutive C) (heig : ENOTraceMatrixEigenvector C)
include hinv heig

variable {C} in
/-- Saturated root dimensions normalize every involutive multiplicity defect. -/
theorem normalized_defects_trivial
    (hsat : ∀ i, ‖rootDimension C i‖ = fpSimple C i) :
    ScaledMultiplicityDefectsTrivial C
      (fun i ↦ (normalizedRootDimension C i)⁻¹) := by
  let q := normalizedRootDimension C
  intro i j k
  let r := q k / (q i * q j)
  have hrnorm : ‖r‖ = 1 := by
    simp [r, q, normalizedRootDimension, Complex.norm_real, abs_of_pos (fpSimple_pos C _),
      hsat, ne_of_gt (fpSimple_pos C _)]
  simpa [q, r, normalizedRootDimension, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_assoc] using
    (involution_phase_inv_eq_one_of_trace (hinv i j k) hrnorm (by
      simpa [enoTraceMatrix, fusionCoeff, q, r, normalizedRootDimension, div_eq_mul_inv, mul_assoc] using
        (weighted_eigenvalue_saturation (fpSimple_pos C) (fpSimple_mul C) hsat
          (fun i j k ↦ enoTraceMatrix_norm_le_fusionCoeff (hinv i j k)) heig i j k)))

variable {C} in
/-- The ENO phase construction removes any need to assume the chosen natural
root has real dimensions. The remaining categorical identities are explicit. -/
theorem positive_spherical_of_matrix_identities
    (hnorm : RootNormIdentity C) (hpu : PseudoUnitary C) :
    HasFPSphericalStructure C :=
  let hsat := eno_root_norm_saturation_of_pseudoUnitary hinv heig hnorm hpu
  let c : Fin (rank C) → ℂ := fun i ↦ (normalizedRootDimension C i)⁻¹
  have hc : ∀ i, c i ≠ 0 := fun i ↦ inv_ne_zero (div_ne_zero (rootDimension_ne_zero i)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (fpSimple_pos C i))))
  have hvalue (i) : c i * rootDimension C i = (fpSimple C i : ℂ) := by
    simp [c, normalizedRootDimension, rootDimension_ne_zero]
  let p := rootPhasePivotal C c hc (normalized_defects_trivial hinv heig hsat)
    (rootSignTwist_unit_of_simple_dimension hc (by simp [hvalue, fpSimple_unit]))
  have hp (i) : pivotalDimension C p (simples C i) = (fpSimple C i : ℂ) := by
    rw [rootPhasePivotal_dimension, hvalue]
  ⟨p, spherical_of_fp_dimensions_and_squaredNorms hp (by simp [hnorm, hsat]), hp⟩

end MTC.CategoryTheory.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix ComplexOrder
namespace MTC.CategoryTheory.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] IsFusionCategory.hom_finite
/-- An involution in a domain is fixed by the star operation. -/
theorem star_eq_self_of_mul_self_eq_one {R : Type*} [NonAssocRing R] [NoZeroDivisors R]
    [StarRing R] {x : R} (h : x * x = 1) : star x = x := by
  rcases mul_self_eq_one_iff.mp h with h | h
  · rw [h, star_one]
  · rw [h, star_neg, star_one]

variable {C} in
/-- ENO's trace reciprocity identifies the dual root dimension with the
signed complex conjugate of the original one. -/
theorem rootDimension_dual_conjugate_of_trace_reciprocity
    (hinv : MultiplicityDefectsInvolutive C) (htranspose : ENOTraceMatrixReciprocity C)
    (i : Fin (rank C)) :
    rootDimension C (dualIndex C i) = (rootDualSign C i).1 * star (rootDimension C i) := by
  let A : Matrix (Fin (rank C)) (Fin (rank C)) ℂ := enoTraceMatrix C i
  let d := rootDimension C
  let ε := (rootDualSign C i).1
  have hε : ε * ε = 1 := (rootDualSign C i).2.1
  have hεstar : star ε = ε := star_eq_self_of_mul_self_eq_one hε
  have hA : ∀ j k, star (A j k) = A j k := fun j k ↦ star_involution_trace (hinv i j k)
  have ht : Aᵀ *ᵥ d = (ε * d (dualIndex C i)) • d := by
    ext j
    change (∑ k, enoTraceMatrix C i k j * rootDimension C k) =
      (ε * rootDimension C (dualIndex C i)) * rootDimension C j
    simpa only [ε, htranspose, Finset.mul_sum, ← mul_assoc, (rootDualSign C i).2.1, one_mul] using
      congrArg (fun z : ℂ ↦ ε * z)
        (enoTraceMatrix_eigenvector_of_involutions (hinv (dualIndex C i) j))
  have hc := congrArg star (conjugate_of_transpose_eigenvector A hA
    (fun hz ↦ rootDimension_ne_zero (unitIndex C) (congrFun hz _))
    (fusion_character_eigenvector (fun j k ↦
      (enoTraceMatrix_eigenvector_of_involutions (hinv j k)).symm) i) ht)
  simp only [star_mul, star_star, hεstar] at hc
  rw [← hc, ← mul_assoc, hε, one_mul]

variable {C} in
/-- ENO's trace reciprocity proves the intrinsic root-norm identity. -/
theorem squaredNorm_eq_root_norm_sq_of_reciprocity
    (hinv : MultiplicityDefectsInvolutive C)
    (htranspose : ENOTraceMatrixReciprocity C) (i : Fin (rank C)) :
    squaredNorm C (simples C i) = ((‖rootDimension C i‖ ^ 2 : ℝ) : ℂ) := by
  rw [squaredNorm_eq_rootDualSign_mul i, rootDimension_dual_conjugate_of_trace_reciprocity hinv htranspose i,
    mul_mul_mul_comm, (rootDualSign C i).2.1, one_mul]; simpa using Complex.mul_conj' (rootDimension C i)

end MTC.CategoryTheory.Dimensions

end
