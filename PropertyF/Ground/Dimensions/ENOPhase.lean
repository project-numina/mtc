module
public import PropertyF.Ground.Dimensions.ENOSpherical
public import PropertyF.Ground.Dimensions.ComplexSaturation

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

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
theorem rootPhasePivotal_dimension (C : Ground.BraidedFusionCategory.{v,u})
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
    (C : Ground.BraidedFusionCategory.{v,u})
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
    have h := fusion_complex_eigenvalue_saturation C (enoTraceMatrix C) (rootDimension C) hsat hdom heig i j k
    simpa [q, div_eq_mul_inv, mul_assoc] using h
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
    letI : FiniteDimensional ℂ
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
