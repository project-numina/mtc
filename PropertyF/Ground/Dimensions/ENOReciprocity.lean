module
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Integrate.CharacterReality
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import PropertyF.Ground.Dimensions.MultiplicityDefect
public import PropertyF.Ground.Dimensions.ENOMatrices
public import PropertyF.Ground.Dimensions.SimpleHomBasis
public import PropertyF.Ground.Dimensions.TensorExtension
public import PropertyF.Ground.Dimensions.SphericalCriterion
public import PropertyF.Ground.Dimensions.ComplexSaturation

/-! # Reciprocity and spherical dimensions

Character duality, phase normalization and trace reciprocity control the dimensions of simple objects.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix ComplexOrder
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
/-- Eigenvalues on a common eigenvector for a real matrix and its transpose
are complex conjugates. -/
theorem conjugate_of_transpose_eigenvector {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : ∀ i j, star (A i j) = A i j)
    (v : ι → ℂ) (hv : v ≠ 0) (z w : ℂ)
    (h : A *ᵥ v = z • v) (ht : Aᵀ *ᵥ v = w • v) : star w = z := by
  have hAt : Aᵀᴴ = A := by
    ext i j
    simp [Matrix.conjTranspose_apply, hA]
  have hs : (star v) ᵥ* A = (star w) • (star v) := by
    have hh := congrArg star ht
    rw [Matrix.star_mulVec, hAt] at hh
    simpa using hh
  have hn : star v ⬝ᵥ v ≠ 0 := by
    intro hz
    exact hv (dotProduct_star_self_eq_zero.mp hz)
  have heq : z * (star v ⬝ᵥ v) = (star w) * (star v ⬝ᵥ v) := by
    calc
      _ = star v ⬝ᵥ (A *ᵥ v) := by rw [h, dotProduct_smul]; rfl
      _ = (star v ᵥ* A) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
      _ = _ := by rw [hs, smul_dotProduct]; rfl
  exact (mul_right_cancel₀ hn heq).symm

/-- Every nonzero fusion character takes complex-conjugate values on dual
simple objects, with no pivotal or spherical hypothesis. -/
theorem fusion_character_dual_eq_conj
    (χ : Fin (Ground.rank C) → ℂ) (i₀ : Fin (Ground.rank C)) (hχ : χ i₀ ≠ 0)
    (hchar : ∀ i j, χ i * χ j = ∑ k, (Ground.fusionCoeff C i j k : ℂ) * χ k)
    (i : Fin (Ground.rank C)) : χ (Ground.dualIndex C i) = star (χ i) := by
  classical
  let A : Matrix (Fin (Ground.rank C)) (Fin (Ground.rank C)) ℂ :=
    fun j k => (Ground.fusionCoeff C i j k : ℂ)
  have hv : χ ≠ 0 := by
    intro hz
    apply hχ
    exact congrFun hz i₀
  have h : A *ᵥ χ = χ i • χ := by
    ext j
    change (∑ k, (Ground.fusionCoeff C i j k : ℂ) * χ k) = χ i * χ j
    exact (hchar i j).symm
  have ht : Aᵀ *ᵥ χ = χ (Ground.dualIndex C i) • χ := by
    ext j
    change (∑ k, (Ground.fusionCoeff C i k j : ℂ) * χ k) =
      χ (Ground.dualIndex C i) * χ j
    simp_rw [Ground.fusionCoeff_dual_transpose C i]
    exact (hchar (Ground.dualIndex C i) j).symm
  have heq := conjugate_of_transpose_eigenvector A (by intro j k; simp [A]) χ hv
    (χ i) (χ (Ground.dualIndex C i)) h ht
  simpa using (congrArg star heq)

/-- Simple pivotal dimensions on duals are conjugate, for any pivotal
structure on a genuine braided fusion category. -/
theorem pivotalDimension_dual_eq_conj
    (p : PivotalStructure (C := C.Obj)) (i : Fin (Ground.rank C)) :
    pivotalDimension C p (Ground.simples C (Ground.dualIndex C i)) =
      star (pivotalDimension C p (Ground.simples C i)) := by
  apply fusion_character_dual_eq_conj C
    (fun j => pivotalDimension C p (Ground.simples C j)) (Ground.unitIndex C)
  · obtain ⟨e⟩ := Ground.unitIndex_iso C
    rw [pivotalDimension_iso C p e, pivotalDimension_unit]
    exact one_ne_zero
  · exact pivotalDimension_character C p

/-- Galois conjugates of pivotal dimensions also interchange complex
conjugation and duality. -/
theorem galois_pivotalDimension_dual_eq_conj
    (p : PivotalStructure (C := C.Obj)) (σ : ℂ ≃+* ℂ) (i : Fin (Ground.rank C)) :
    σ (pivotalDimension C p (Ground.simples C (Ground.dualIndex C i))) =
      star (σ (pivotalDimension C p (Ground.simples C i))) := by
  apply fusion_character_dual_eq_conj C
    (fun j => σ (pivotalDimension C p (Ground.simples C j))) (Ground.unitIndex C)
  · obtain ⟨e⟩ := Ground.unitIndex_iso C
    rw [pivotalDimension_iso C p e, pivotalDimension_unit, map_one]
    exact one_ne_zero
  · intro j k
    simpa using congrArg σ (pivotalDimension_character C p j k)

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The inverse dual of a natural fourth-dual square root is also a root at
the dual object. -/
theorem inverseDualRoot_square (X : C.Obj) :
    (rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm.hom ≫
      (((((rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm.hom)ᘁ)ᘁ)) =
      (fourthDualIso C (Xᘁ)).hom := by
  let j : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  have hroot : j.hom ≫ ((j.homᘁ)ᘁ) = (fourthDualIso C X).hom := by
    exact (congrArg (fun n => (n.app X).hom) (fourthDualRootNaturalSquare_eq C))
  have hiso : j ≪≫ rightDualIsoMap (rightDualIsoMap j) = fourthDualIso C X := by
    apply Iso.ext
    exact hroot
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
  let : Simple (Xᘁ) := Ground.simple_rightDual C X
  let : FiniteDimensional ℂ ((Xᘁ) ⟶ (Xᘁ)) := Ground.IsFusionCategory.hom_finite _ _
  let l : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm
  let k : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (fourthDualRootNaturalIso C).app (Xᘁ)
  obtain ⟨ε, _, he, _⟩ := doubleDualIso_scalar l k
  refine ⟨ε, ?_, he⟩
  have hk : k.hom ≫ ((k.homᘁ)ᘁ) = (fourthDualIso C (Xᘁ)).hom := by
    exact (congrArg (fun n => (n.app (Xᘁ)).hom) (fourthDualRootNaturalSquare_eq C))
  have hl : l.hom ≫ ((l.homᘁ)ᘁ) = (fourthDualIso C (Xᘁ)).hom := inverseDualRoot_square C X
  have hscale : k.hom ≫ ((k.homᘁ)ᘁ) = (ε * ε) • (l.hom ≫ ((l.homᘁ)ᘁ)) := by
    rw [he]
    simp only [rightAdjointMate_smul, Linear.smul_comp, Linear.comp_smul, smul_smul]
  have hm : (ε * ε) • (fourthDualIso C (Xᘁ)).hom = (1 : ℂ) • (fourthDualIso C (Xᘁ)).hom := by
    calc
      _ = (ε * ε) • (l.hom ≫ ((l.homᘁ)ᘁ)) := by rw [hl]
      _ = k.hom ≫ ((k.homᘁ)ᘁ) := hscale.symm
      _ = _ := by simpa using hk
  have hn : (fourthDualIso C (Xᘁ)).hom ≠ 0 := by
    intro h
    have hh := congrArg (fun f => f ≫ (fourthDualIso C (Xᘁ)).inv) h
    simp at hh
    exact id_nonzero (Xᘁ) hh
  exact smul_left_injective ℂ hn hm

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
/-- The sign comparing the root on a simple's dual to the inverse dual root. -/
noncomputable def rootDualSign (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) : ℂ := by
  letI : Simple (Ground.simples C i) := Ground.simples_simple C i
  exact Classical.choose (rootDual_differs_by_sign C (Ground.simples C i))

theorem rootDualSign_sq (i : Fin (Ground.rank C)) :
    rootDualSign C i * rootDualSign C i = 1 := by
  let : Simple (Ground.simples C i) := Ground.simples_simple C i
  exact (Classical.choose_spec (rootDual_differs_by_sign C (Ground.simples C i))).1

theorem rootDualSign_component (i : Fin (Ground.rank C)) :
    ((fourthDualRootNaturalIso C).app ((Ground.simples C i)ᘁ)).hom =
      rootDualSign C i • (rightDualIsoMap ((fourthDualRootNaturalIso C).app (Ground.simples C i))).symm.hom := by
  let : Simple (Ground.simples C i) := Ground.simples_simple C i
  exact (Classical.choose_spec (rootDual_differs_by_sign C (Ground.simples C i))).2

set_option backward.isDefEq.respectTransparency false in
/-- Intrinsic simple norms are signed products of the root dimensions of a
simple and its dual, using the same sign as the dual-root component. -/
theorem squaredNorm_eq_rootDualSign_mul
    (i : Fin (Ground.rank C)) :
    Ground.squaredNorm C (Ground.simples C i) = rootDualSign C i * rootDimension C i *
      rootDimension C (Ground.dualIndex C i) := by
  let X := Ground.simples C i
  let : Simple X := Ground.simples_simple C i
  let j : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  let l : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (rightDualIsoMap j).symm
  let k : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (fourthDualRootNaturalIso C).app (Xᘁ)
  let e : Xᘁ ≅ ᘁX := leftDualIso
    (BraidedCategory.exactPairing_swap X (Xᘁ)) HasLeftDual.exact
  obtain ⟨u⟩ := Ground.dualIndex_iso C i
  have hId (Z : C.Obj) : rootTrace C (𝟙 Z) = rightQuantumTrace ((fourthDualRootNaturalIso C).app Z) := by
    apply End.homEquiv.injective
    simp [rootTrace, rightTraceWith, rightQuantumTrace, tensorHom_def]
  have hq : Ground.unitScalar C (rightQuantumTrace k) = rootDimension C (Ground.dualIndex C i) := by
    change Ground.unitScalar C (rightQuantumTrace ((fourthDualRootNaturalIso C).app (Xᘁ))) = _
    rw [← hId, rootTrace_id_iso C (e ≪≫ u)]
    rfl
  have hx : Ground.unitScalar C (rightQuantumTrace j) = rootDimension C i := by
    change Ground.unitScalar C (rightQuantumTrace ((fourthDualRootNaturalIso C).app X)) = _
    rw [← hId]
    rfl
  have ht : rightQuantumTrace k = rootDualSign C i • rightQuantumTrace l := by
    apply End.homEquiv.injective
    have he : k.hom = rootDualSign C i • l.hom := rootDualSign_component C i
    simp [rightQuantumTrace, he, tensorHom_def]
  rw [target_squaredNorm_choice_independent C X j, leftQuantumTrace_eq_rightDual j]
  change Ground.unitScalar C (rightQuantumTrace j) * Ground.unitScalar C (rightQuantumTrace l) =
    rootDualSign C i * rootDimension C i * rootDimension C (Ground.dualIndex C i)
  rw [← hx, ← hq, ht]
  simp only [← groundUnitScalarEquiv_apply, map_smul, smul_eq_mul]
  have hs := rootDualSign_sq C i
  calc
    _ = (rootDualSign C i * rootDualSign C i) * (groundUnitScalarEquiv C (rightQuantumTrace j) *
      groundUnitScalarEquiv C (rightQuantumTrace l)) := by rw [hs, one_mul]
    _ = _ := by ring

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
/-- A pivotal structure whose simple dimensions and intrinsic norms are the
FP values is spherical. -/
theorem spherical_of_fp_dimensions_and_squaredNorms
    (p : PivotalStructure (C := C.Obj))
    (hdim : ∀ i, pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ))
    (hnorm : ∀ i, Ground.squaredNorm C (Ground.simples C i) =
      ((Ground.fpSimple C i ^ 2 : ℝ) : ℂ)) : p.IsSpherical := by
  apply (isSpherical_iff_simple_dimensions C p).2
  intro i
  let X := Ground.simples C i
  let : Simple X := Ground.simples_simple C i
  have hh := target_squaredNorm_choice_independent C X (p.iso X)
  rw [← rightTrace_id, ← leftTrace_id] at hh
  have hr : Ground.unitScalar C (p.rightTrace (𝟙 X)) = (Ground.fpSimple C i : ℂ) := hdim i
  rw [hr, hnorm i, Complex.ofReal_pow] at hh
  have hf : (Ground.fpSimple C i : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Ground.fpSimple_pos C i)
  have hl : Ground.unitScalar C (p.leftTrace (𝟙 X)) = (Ground.fpSimple C i : ℂ) := by
    apply mul_left_cancel₀ hf
    simpa [pow_two] using hh.symm
  apply (groundUnitScalarEquiv C).injective
  simpa only [groundUnitScalarEquiv_apply] using hl.trans hr.symm

/-- ENO's trace-matrix bound and the root-norm identity turn global
pseudo-unitarity into pointwise FP saturation. -/
theorem eno_root_norm_saturation_of_pseudoUnitary
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (heig : ∀ i j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j)
    (hnorm : ∀ i, Ground.squaredNorm C (Ground.simples C i) =
      ((‖rootDimension C i‖ ^ 2 : ℝ) : ℂ)) (hpu : Ground.PseudoUnitary C) :
    ∀ i, ‖rootDimension C i‖ = Ground.fpSimple C i := by
  let d : Fin (Ground.rank C) → ℝ := fun i => ‖rootDimension C i‖
  have hb : ∀ i, |d i| ≤ Ground.fpSimple C i := by
    intro i
    rw [abs_of_nonneg (norm_nonneg _)]
    exact rootDimension_norm_le_fp_of_trace_matrix C i (hinv i) (heig i)
  have hg : (∑ i, d i ^ 2) = Ground.globalFPDimension C := by
    have h := hpu
    change Ground.globalDimension C = (Ground.globalFPDimension C : ℂ) at h
    unfold Ground.globalDimension at h
    simp only [hnorm, ← Complex.ofReal_sum] at h
    exact Complex.ofReal_injective h
  have h := (global_sum_squares_eq_iff C d hb).1 hg
  intro i
  simpa [d, abs_of_nonneg (norm_nonneg _)] using h i

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
/-- A phase-twisted natural root becomes pivotal when its scaled multiplicity
operators are identities and the double-dual tensorator is natural. -/
def rootPhasePivotal (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hnat : ∀ {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y'),
      (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
        (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ))
    (hdef : ∀ i j k, (c k / (c i * c j)) • (multiplicityDefect C i j k).toLinearMap = 1)
    (hunit : ((rootSignTwist C c hc).app (𝟙_ C.Obj)).hom =
      (doubleDualUnitIso (C := C.Obj)).hom) : PivotalStructure (C := C.Obj) where
  iso X := (rootSignTwist C c hc).app X
  naturality {X Y} f := by
    have h := (rootSignTwist C c hc).hom.naturality f
    change f ≫ ((rootSignTwist C c hc).app Y).hom =
      ((rootSignTwist C c hc).app X).hom ≫ ((fᘁ)ᘁ) at h
    exact h
  tensor X Y := by
    apply doubleDualTensor_extension C (rootSignTwist C c hc) hnat
    intro i j
    exact congrArg Iso.hom (rootPhaseTensor_compatible_of_scaled_defects C c hc i j (hdef i j))
  unit := hunit

set_option backward.isDefEq.respectTransparency false in
theorem rootPhasePivotal_dimension
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hnat : ∀ {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y'),
      (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
        (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ))
    (hdef : ∀ i j k, (c k / (c i * c j)) • (multiplicityDefect C i j k).toLinearMap = 1)
    (hunit : ((rootSignTwist C c hc).app (𝟙_ C.Obj)).hom =
      (doubleDualUnitIso (C := C.Obj)).hom) (i : Fin (Ground.rank C)) :
    pivotalDimension C (rootPhasePivotal C c hc hnat hdef hunit) (Ground.simples C i) =
      c i * rootDimension C i := by
  have ht : (rootPhasePivotal C c hc hnat hdef hunit).rightTrace (𝟙 (Ground.simples C i)) =
      c i • rootTrace C (𝟙 (Ground.simples C i)) := by
    apply End.homEquiv.injective
    have h := rootSignTwist_app_simple C c hc i
    change (rootSignTwist C c hc).hom.app (Ground.simples C i) = _ at h
    simp [PivotalStructure.rightTrace, rootPhasePivotal, rootTrace, rightTraceWith, h, tensorHom_def]
  unfold pivotalDimension rootDimension
  rw [ht]
  simp only [← groundUnitScalarEquiv_apply, map_smul, smul_eq_mul]

/-- The ENO phase construction removes any need to assume the chosen natural
root has real dimensions. The remaining categorical identities are explicit. -/
theorem eno_pseudoUnitary_yields_positive_spherical_of_matrix_identities
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (heig : ∀ i j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j)
    (hnat : ∀ {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y'),
      (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
        (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ))
    (hnorm : ∀ i, Ground.squaredNorm C (Ground.simples C i) =
      ((‖rootDimension C i‖ ^ 2 : ℝ) : ℂ)) (hpu : Ground.PseudoUnitary C) :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  classical
  have hsat := eno_root_norm_saturation_of_pseudoUnitary C hinv heig hnorm hpu
  let q : Fin (Ground.rank C) → ℂ := fun i => rootDimension C i / (Ground.fpSimple C i : ℂ)
  have hq : ∀ i, ‖q i‖ = 1 := by
    intro i
    dsimp [q]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Ground.fpSimple_pos C i), hsat i]
    exact div_self (ne_of_gt (Ground.fpSimple_pos C i))
  have hq0 : ∀ i, q i ≠ 0 := fun i => norm_pos_iff.mp (by rw [hq]; norm_num)
  let c : Fin (Ground.rank C) → ℂ := fun i => (q i)⁻¹
  have hc : ∀ i, c i ≠ 0 := fun i => inv_ne_zero (hq0 i)
  have hdom : ∀ i j k, ‖enoTraceMatrix C i j k‖ ≤ (Ground.fusionCoeff C i j k : ℝ) := by
    intro i j k
    obtain ⟨n, hn, hb⟩ := multiplicityDefect_trace_integer_bound C i j k (hinv i j k)
    change ‖LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap‖ ≤ _
    rw [hn, Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast hb
  have hphase : ∀ i j k, enoTraceMatrix C i j k * (q k / (q i * q j)) =
      (Ground.fusionCoeff C i j k : ℂ) := by
    intro i j k
    simpa [q, div_eq_mul_inv, mul_assoc] using
      (fusion_complex_eigenvalue_saturation C (enoTraceMatrix C) (rootDimension C) hsat hdom heig i j k)
  have hdef : ∀ i j k, (c k / (c i * c j)) • (multiplicityDefect C i j k).toLinearMap = 1 := by
    intro i j k
    let r := q k / (q i * q j)
    have hrnorm : ‖r‖ = 1 := by
      dsimp [r]
      rw [norm_div, norm_mul, hq i, hq j, hq k]
      norm_num
    have hrtrace : LinearMap.trace ℂ _ (multiplicityDefect C i j k).toLinearMap * r =
        (Module.finrank ℂ (Ground.simples C k ⟶ Ground.simples C i ⊗ Ground.simples C j) : ℂ) := by
      exact hphase i j k
    let : FiniteDimensional ℂ
      (Ground.simples C k ⟶ Ground.simples C i ⊗ Ground.simples C j) :=
      Ground.IsFusionCategory.hom_finite _ _
    have hfactor : c k / (c i * c j) = r⁻¹ := by
      dsimp [c, r]
      field_simp [hq0 i, hq0 j, hq0 k]
    rw [hfactor]
    exact involution_phase_inv_eq_one_of_trace _ (hinv i j k) r hrnorm hrtrace
  have hvalue : ∀ i, c i * rootDimension C i = (Ground.fpSimple C i : ℂ) := by
    intro i
    have hf : (Ground.fpSimple C i : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (Ground.fpSimple_pos C i)
    dsimp [c, q]
    field_simp [hf, rootDimension_ne_zero C i]
  have hu : c (Ground.unitIndex C) * rootDimension C (Ground.unitIndex C) = 1 := by
    rw [hvalue, Ground.fpSimple_unit]
    norm_num
  let unitProof := rootSignTwist_unit_of_simple_dimension C c hc hu
  let p := rootPhasePivotal C c hc hnat hdef unitProof
  have hp : ∀ i, pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
    intro i
    rw [rootPhasePivotal_dimension, hvalue]
  refine ⟨p, spherical_of_fp_dimensions_and_squaredNorms C p hp ?_, hp⟩
  intro i
  rw [hnorm i, hsat i]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix ComplexOrder
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
/-- ENO's trace reciprocity identifies the dual root dimension with the
signed complex conjugate of the original one. -/
theorem rootDimension_dual_conjugate_of_trace_reciprocity
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

end PropertyF.Ground.Dimensions

end
