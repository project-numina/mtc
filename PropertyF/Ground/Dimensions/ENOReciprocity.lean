module
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Modular.SMatrix
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import PropertyF.Ground.Dimensions.MultiplicityDefect
public import PropertyF.Ground.Dimensions.ENOMatrices
public import PropertyF.Ground.Dimensions.SimpleHomBasis
public import PropertyF.Ground.Dimensions.TensorExtension


/-! # Reciprocity and spherical dimensions

Character duality, phase normalization and trace reciprocity control the dimensions of simple objects.

## Main results

* `pivotalDimension_dual_eq_conj`: identifies simple dimensions on duals with their complex conjugates.
* `positive_spherical_of_matrix_identities`: uses trace matrix identities to construct a positive spherical structure.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix ComplexOrder
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- Simple pivotal dimensions on duals are conjugate, for any pivotal
structure on a genuine braided fusion category. -/
theorem pivotalDimension_dual_eq_conj
    (p : PivotalStructure (C := C.Obj)) (i : Fin (rank C)) :
    pivotalDimension C p (simples C (dualIndex C i)) =
      star (pivotalDimension C p (simples C i)) := by
  apply fusion_character_dual_eq_conj (N := fusionCoeff C) (d := dualIndex C)
    (χ := fun j => pivotalDimension C p (simples C j)) (i₀ := unitIndex C)
  · exact fun i j k ↦ (fusionCoeff_dual_symmetry C i j k).symm
  · simpa only [pivotalDimension_unitIndex] using (one_ne_zero : (1 : ℂ) ≠ 0)
  · exact pivotalDimension_character C p


end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

/-- Scalar multiples with the same double-dual square differ by a sign. -/
theorem scalar_sq_eq_one_of_same_square {X : D} [Simple X]
    (a b : X ≅ (Xᘁ)ᘁ) (z : ℂ) (hz : b.hom = z • a.hom)
    (hsq : b.hom ≫ ((b.homᘁ)ᘁ) = a.hom ≫ ((a.homᘁ)ᘁ)) : z * z = 1 := by
  have hn : (a ≪≫ rightDualIsoMap (rightDualIsoMap a)).hom ≠ 0 :=
    mono_ne_zero_of_id_ne_zero _ (id_nonzero X)
  apply smul_left_injective ℂ hn
  change (z * z) • (a.hom ≫ ((a.homᘁ)ᘁ)) = (1 : ℂ) • (a.hom ≫ ((a.homᘁ)ᘁ))
  calc
    _ = b.hom ≫ ((b.homᘁ)ᘁ) := by
      rw [hz]
      simp only [rightAdjointMate_smul, Linear.smul_comp, Linear.comp_smul, smul_smul]
    _ = _ := by simpa using hsq

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The inverse dual of a natural fourth-dual square root is also a root at
the dual object. -/
theorem inverseDualRoot_square (X : C.Obj) :
    (rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm.hom ≫
      (((((rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm.hom)ᘁ)ᘁ)) =
      (fourthDualIso C (Xᘁ)).hom := by
  let j : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  have hroot : j.hom ≫ ((j.homᘁ)ᘁ) = (fourthDualIso C X).hom :=
    (congrArg (fun n => (n.app X).hom) (fourthDualRootNaturalSquare_eq C))
  have hiso : j ≪≫ rightDualIsoMap (rightDualIsoMap j) = fourthDualIso C X := Iso.ext hroot
  have hinv := congrArg Iso.inv hiso
  have hm := congrArg (fun f => rightAdjointMate f) hinv
  rw [fourthDualIso_rightDual]
  simpa only [Iso.trans_inv, rightDualIsoMap, Iso.symm_hom, Iso.symm_inv,
    comp_rightAdjointMate] using hm

set_option backward.isDefEq.respectTransparency false in
/-- On a simple object, the natural root on the dual differs from the inverse
dual root by a sign. -/
theorem rootDual_differs_by_sign (X : C.Obj)
    [Simple X] : ∃ ε : ℂ, ε * ε = 1 ∧
      ((fourthDualRootNaturalIso C).app (Xᘁ)).hom =
        ε • (rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm.hom := by
  let : Simple (Xᘁ) := simple_rightDual C X
  let : FiniteDimensional ℂ ((Xᘁ) ⟶ (Xᘁ)) := IsFusionCategory.hom_finite _ _
  let l : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm
  let k : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (fourthDualRootNaturalIso C).app (Xᘁ)
  obtain ⟨ε, _, he, _⟩ := isomorphisms_scalar l k
  refine ⟨ε, ?_, he⟩
  exact scalar_sq_eq_one_of_same_square l k ε he
    ((congrArg (fun n => (n.app (Xᘁ)).hom) (fourthDualRootNaturalSquare_eq C)).trans
      (inverseDualRoot_square C X).symm)

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- The sign comparing the root on a simple's dual to the inverse dual root. -/
noncomputable def rootDualSign (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) : ℂ := by
  letI : Simple (simples C i) := simples_simple C i
  exact Classical.choose (rootDual_differs_by_sign C (simples C i))

/-- The trace matrices of dual simples are transposes up to the dual-root sign. -/
abbrev ENOTraceMatrixReciprocity (C : BraidedFusionCategory.{v,u}) : Prop :=
  ∀ i j k, enoTraceMatrix C (dualIndex C i) j k =
    rootDualSign C i * enoTraceMatrix C i k j

theorem rootDualSign_sq (i : Fin (rank C)) :
    rootDualSign C i * rootDualSign C i = 1 :=
  letI : Simple (simples C i) := simples_simple C i
  (Classical.choose_spec (rootDual_differs_by_sign C (simples C i))).1

theorem rootDualSign_component (i : Fin (rank C)) :
    ((fourthDualRootNaturalIso C).app ((simples C i)ᘁ)).hom =
      rootDualSign C i • (rightDualIsoMap ((fourthDualRootNaturalIso C).app (simples C i))).symm.hom :=
  letI : Simple (simples C i) := simples_simple C i
  (Classical.choose_spec (rootDual_differs_by_sign C (simples C i))).2

set_option backward.isDefEq.respectTransparency false in
/-- Intrinsic simple norms are signed products of the root dimensions of a
simple and its dual, using the same sign as the dual-root component. -/
theorem squaredNorm_eq_rootDualSign_mul
    (i : Fin (rank C)) :
    squaredNorm C (simples C i) = rootDualSign C i * rootDimension C i *
      rootDimension C (dualIndex C i) := by
  let X := simples C i
  let : Simple X := simples_simple C i
  let j : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  let l : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (rightDualIsoMap j).symm
  let k : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (fourthDualRootNaturalIso C).app (Xᘁ)
  let e : Xᘁ ≅ ᘁX := leftDualIso
    (BraidedCategory.exactPairing_swap X (Xᘁ)) HasLeftDual.exact
  obtain ⟨u⟩ := dualIndex_iso C i
  have hq : unitScalar C (rightQuantumTrace k) = rootDimension C (dualIndex C i) :=
    congrArg (unitScalar C) ((rootTrace_id C (Xᘁ)).symm.trans (rootTrace_id_iso C (e ≪≫ u)))
  have hx : unitScalar C (rightQuantumTrace j) = rootDimension C i :=
    congrArg (unitScalar C) (rootTrace_id C X).symm
  have ht : rightQuantumTrace k = rootDualSign C i • rightQuantumTrace l :=
    rightQuantumTrace_smul_hom (rootDualSign_component C i)
  rw [target_squaredNorm_choice_independent C j, leftQuantumTrace_eq_rightDual j]
  change unitScalar C (rightQuantumTrace j) * unitScalar C (rightQuantumTrace l) =
    rootDualSign C i * rootDimension C i * rootDimension C (dualIndex C i)
  rw [← hx, ← hq, ht]
  simp only [Ground.unitScalar_eq_equiv, map_smul, smul_eq_mul]
  have hs := rootDualSign_sq C i
  calc
    _ = (rootDualSign C i * rootDualSign C i) * (Ground.unitScalarEquiv C (rightQuantumTrace j) *
      Ground.unitScalarEquiv C (rightQuantumTrace l)) := by rw [hs, one_mul]
    _ = _ := by ring

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- A pivotal structure whose simple dimensions and intrinsic norms are the
FP values is spherical. -/
theorem spherical_of_fp_dimensions_and_squaredNorms
    (p : PivotalStructure (C := C.Obj))
    (hdim : ∀ i, pivotalDimension C p (simples C i) = (fpSimple C i : ℂ))
    (hnorm : ∀ i, squaredNorm C (simples C i) =
      ((fpSimple C i ^ 2 : ℝ) : ℂ)) : p.IsSpherical := by
  apply (isSpherical_iff_simple_dimensions C p).2
  intro i
  let X := simples C i
  let : Simple X := simples_simple C i
  have hh := target_squaredNorm_choice_independent C (p.iso X)
  rw [← rightTrace_id, ← leftTrace_id] at hh
  have hr : unitScalar C (p.rightTrace (𝟙 X)) = (fpSimple C i : ℂ) := hdim i
  rw [hr, hnorm i, Complex.ofReal_pow] at hh
  have hf : (fpSimple C i : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (fpSimple_pos C i)
  have hl : unitScalar C (p.leftTrace (𝟙 X)) = (fpSimple C i : ℂ) :=
    mul_left_cancel₀ hf (by simpa [pow_two] using hh.symm)
  apply (Ground.unitScalarEquiv C).injective
  simpa only [← Ground.unitScalar_eq_equiv] using hl.trans hr.symm

/-- ENO's trace-matrix bound and the root-norm identity turn global
pseudo-unitarity into pointwise FP saturation. -/
theorem eno_root_norm_saturation_of_pseudoUnitary
    (hinv : MultiplicityDefectsInvolutive C)
    (heig : ENOTraceMatrixEigenvector C)
    (hnorm : RootNormIdentity C) (hpu : PseudoUnitary C) :
    ∀ i, ‖rootDimension C i‖ = fpSimple C i :=
  norm_saturation_of_pseudoUnitary C
    (fun i => rootDimension_norm_le_fp_of_trace_matrix C (hinv i) (heig i)) hnorm hpu

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- A phase-twisted natural root becomes pivotal when its scaled multiplicity
operators are identities. -/
def rootPhasePivotal (C : BraidedFusionCategory.{v,u})
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hdef : ScaledMultiplicityDefectsTrivial C c)
    (hunit : RootSignUnitLaw C c hc) : PivotalStructure (C := C.Obj) where
  iso X := (rootSignTwist C c hc).app X
  naturality {_X _Y} f := (rootSignTwist C c hc).hom.naturality f
  tensor X Y := doubleDualTensor_extension C (rootSignTwist C c hc)
    (fun i j ↦ congrArg Iso.hom (rootPhaseTensor_compatible_of_scaled_defects C hc (hdef i j))) X Y
  unit := hunit

set_option backward.isDefEq.respectTransparency false in
theorem rootPhasePivotal_dimension
    {c : Fin (rank C) → ℂ} (hc : ∀ i, c i ≠ 0)
    (hdef : ScaledMultiplicityDefectsTrivial C c)
    (hunit : RootSignUnitLaw C c hc) (i : Fin (rank C)) :
    pivotalDimension C (rootPhasePivotal C c hc hdef hunit) (simples C i) =
      c i * rootDimension C i := by
  simpa only [pivotalDimension, rightTrace_id, rootPhasePivotal] using
    rootSignQuantumTrace_simple C hc i

/-- Saturated root dimensions normalize every involutive multiplicity defect. -/
theorem normalized_defects_trivial
    (hinv : MultiplicityDefectsInvolutive C) (heig : ENOTraceMatrixEigenvector C)
    (hsat : ∀ i, ‖rootDimension C i‖ = fpSimple C i) :
    ScaledMultiplicityDefectsTrivial C
      (fun i => (rootDimension C i / (fpSimple C i : ℂ))⁻¹) := by
  classical
  let q : Fin (rank C) → ℂ := fun i => rootDimension C i / (fpSimple C i : ℂ)
  have hq : ∀ i, ‖q i‖ = 1 :=
    fun i ↦ norm_div_ofReal_eq_one (fpSimple_pos C i) (hsat i)
  let c : Fin (rank C) → ℂ := fun i => (q i)⁻¹
  have hdom : ∀ i j k, ‖enoTraceMatrix C i j k‖ ≤ (fusionCoeff C i j k : ℝ) :=
    fun i j k ↦ enoTraceMatrix_norm_le_fusionCoeff C (hinv i j k)
  have hphase (i j k) : enoTraceMatrix C i j k * (q k / (q i * q j)) =
      (fusionCoeff C i j k : ℂ) := by
    simpa [q, div_eq_mul_inv, mul_assoc] using
      (fusion_complex_eigenvalue_saturation C hsat hdom heig i j k)
  change ScaledMultiplicityDefectsTrivial C c
  intro i j k
  let r := q k / (q i * q j)
  have hrnorm : ‖r‖ = 1 := by simp [r, hq]
  have hrtrace : LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap * r =
      (Module.finrank ℂ (simples C k ⟶ simples C i ⊗ simples C j) : ℂ) := hphase i j k
  let : FiniteDimensional ℂ
    (simples C k ⟶ simples C i ⊗ simples C j) :=
    IsFusionCategory.hom_finite _ _
  have hfactor : c k / (c i * c j) = r⁻¹ := by
    simp [c, r, div_eq_mul_inv, mul_inv_rev, mul_comm, mul_assoc]
  rw [hfactor]
  exact involution_phase_inv_eq_one_of_trace (hinv i j k) hrnorm hrtrace

/-- The ENO phase construction removes any need to assume the chosen natural
root has real dimensions. The remaining categorical identities are explicit. -/
theorem positive_spherical_of_matrix_identities
    (hinv : MultiplicityDefectsInvolutive C)
    (heig : ENOTraceMatrixEigenvector C)
    (hnorm : RootNormIdentity C) (hpu : PseudoUnitary C) :
    HasFPSphericalStructure C := by
  classical
  have hsat := eno_root_norm_saturation_of_pseudoUnitary C hinv heig hnorm hpu
  let q : Fin (rank C) → ℂ := fun i => rootDimension C i / (fpSimple C i : ℂ)
  let c : Fin (rank C) → ℂ := fun i => (q i)⁻¹
  have hc : ∀ i, c i ≠ 0 := fun i ↦ inv_ne_zero (div_ne_zero (rootDimension_ne_zero C i)
    (by exact_mod_cast ne_of_gt (fpSimple_pos C i)))
  have hdef : ScaledMultiplicityDefectsTrivial C c := normalized_defects_trivial C hinv heig hsat
  have hvalue (i) : c i * rootDimension C i = (fpSimple C i : ℂ) := by
    dsimp [c, q]
    rw [inv_div, div_mul_cancel₀ _ (rootDimension_ne_zero C i)]
  have hu : c (unitIndex C) * rootDimension C (unitIndex C) = 1 := by
    rw [hvalue, fpSimple_unit]
    norm_num
  let unitProof := rootSignTwist_unit_of_simple_dimension C hc hu
  let p := rootPhasePivotal C c hc hdef unitProof
  have hp (i) : pivotalDimension C p (simples C i) = (fpSimple C i : ℂ) := by
    rw [rootPhasePivotal_dimension, hvalue]
  exact ⟨p, spherical_of_fp_dimensions_and_squaredNorms C p hp
    (fun i ↦ by rw [hnorm i, hsat i]), hp⟩

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix ComplexOrder
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
/-- ENO's trace reciprocity identifies the dual root dimension with the
signed complex conjugate of the original one. -/
theorem rootDimension_dual_conjugate_of_trace_reciprocity
    (hinv : MultiplicityDefectsInvolutive C)
    (htranspose : ENOTraceMatrixReciprocity C)
    (i : Fin (rank C)) :
    rootDimension C (dualIndex C i) = rootDualSign C i * star (rootDimension C i) := by
  classical
  let A : Matrix (Fin (rank C)) (Fin (rank C)) ℂ := enoTraceMatrix C i
  let d := rootDimension C
  let ε := rootDualSign C i
  have hε : ε * ε = 1 := rootDualSign_sq C i
  have hεstar : star ε = ε := by
    rcases mul_self_eq_one_iff.mp hε with h | h <;> simp [h]
  have hA : ∀ j k, star (A j k) = A j k := fun j k ↦
    letI : FiniteDimensional ℂ (simples C k ⟶ simples C i ⊗ simples C j) :=
      IsFusionCategory.hom_finite _ _
    star_involution_trace (hinv i j k)
  have hv : d ≠ 0 := fun hz ↦ rootDimension_ne_zero C (unitIndex C) (congrFun hz _)
  have h : A *ᵥ d = d i • d :=
    fusion_character_eigenvector (fun j k ↦ (enoTraceMatrix_eigenvector_of_involutions C
      (hinv j k)).symm) i
  have ht : Aᵀ *ᵥ d = (ε * d (dualIndex C i)) • d := by
    ext j
    change (∑ k, enoTraceMatrix C i k j * rootDimension C k) =
      (ε * rootDimension C (dualIndex C i)) * rootDimension C j
    have he := enoTraceMatrix_eigenvector_of_involutions C
      (hinv (dualIndex C i) j)
    simp_rw [htranspose] at he
    calc
      _ = ε * ∑ k, ((ε * enoTraceMatrix C i k j) * rootDimension C k) := by
        simp only [Finset.mul_sum, ← mul_assoc, hε, one_mul]
      _ = _ := by rw [he]; ring
  have hc := congrArg star (conjugate_of_transpose_eigenvector A hA hv h ht)
  simp only [star_mul, star_star, hεstar] at hc
  rw [← hc, ← mul_assoc, hε, one_mul]

/-- ENO's trace reciprocity proves the intrinsic root-norm identity. -/
theorem squaredNorm_eq_root_norm_sq_of_reciprocity
    (hinv : MultiplicityDefectsInvolutive C)
    (htranspose : ENOTraceMatrixReciprocity C) (i : Fin (rank C)) :
    squaredNorm C (simples C i) = ((‖rootDimension C i‖ ^ 2 : ℝ) : ℂ) := by
  rw [squaredNorm_eq_rootDualSign_mul C i,
    rootDimension_dual_conjugate_of_trace_reciprocity C hinv htranspose i]
  calc
    _ = (rootDualSign C i * rootDualSign C i) *
        (rootDimension C i * star (rootDimension C i)) := by ring
    _ = _ := by
      rw [rootDualSign_sq, one_mul]
      simpa using Complex.mul_conj' (rootDimension C i)

end PropertyF.Ground.Dimensions

end
