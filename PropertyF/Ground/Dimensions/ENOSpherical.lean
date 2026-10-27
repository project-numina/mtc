module
public import PropertyF.Ground.Dimensions.TensorExtension
public import PropertyF.Ground.Dimensions.SphericalCriterion

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u

/-- The real saturated ENO hypotheses yield an actual positive pivotal
structure, provided the double-dual tensor comparison is natural. -/
theorem eno_real_saturated_root_yields_positive_pivotal
    (C : Ground.BraidedFusionCategory.{v,u}) (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, rootDimension C i = (d i : ℂ))
    (hd : ∀ i, |d i| = Ground.fpSimple C i)
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (heig : ∀ i j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j)
    (hnat : ∀ {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y'),
      (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
        (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ)) :
    ∃ p : PivotalStructure (C := C.Obj), ∀ i,
      pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  let s : Fin (Ground.rank C) → ℝ := fun i => d i / Ground.fpSimple C i
  let c : Fin (Ground.rank C) → ℂ := fun i => (s i : ℂ)
  have hsq : ∀ i, d i * d i = Ground.fpSimple C i * Ground.fpSimple C i := by
    intro i
    have h := congrArg (fun x : ℝ => x * x) (hd i)
    simpa only [abs_mul_abs_self] using h
  have hsreal : ∀ i, s i * s i = 1 := by
    intro i
    dsimp [s]
    field_simp [ne_of_gt (Ground.fpSimple_pos C i)]
    nlinarith [hsq i]
  have hs : ∀ i, c i * c i = 1 := by
    intro i
    change (s i : ℂ) * (s i : ℂ) = 1
    exact_mod_cast hsreal i
  have hc : ∀ i, c i ≠ 0 := by
    intro i h
    have hh := hs i
    rw [h, zero_mul] at hh
    exact zero_ne_one hh
  have hdef : ∀ i j k, (multiplicityDefect C i j k).toLinearMap = (c i * c j * c k) • 1 := by
    intro i j k
    have h := enoDefect_eq_sign_of_real_saturated_dimensions C d hreal hd hinv heig i j k
    simpa [c, s] using h
  have hvalue : ∀ i, s i * d i = Ground.fpSimple C i := by
    intro i
    dsimp [s]
    field_simp [ne_of_gt (Ground.fpSimple_pos C i)]
    nlinarith [hsq i]
  have hu : c (Ground.unitIndex C) * rootDimension C (Ground.unitIndex C) = 1 := by
    rw [hreal]
    change (s (Ground.unitIndex C) : ℂ) * (d (Ground.unitIndex C) : ℂ) = 1
    rw [← Complex.ofReal_mul, hvalue, Ground.fpSimple_unit]
    norm_num
  let unitProof := rootSignTwist_unit_of_simple_dimension C c hc hu
  let p := rootSignPivotal C c hc hs hnat hdef unitProof
  refine ⟨p, ?_⟩
  intro i
  rw [rootSignPivotal_dimension, hreal]
  change (s i : ℂ) * (d i : ℂ) = (Ground.fpSimple C i : ℂ)
  exact_mod_cast hvalue i

/-- A pivotal structure whose simple dimensions and intrinsic norms are the
FP values is spherical. -/
theorem spherical_of_fp_dimensions_and_squaredNorms (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj))
    (hdim : ∀ i, pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ))
    (hnorm : ∀ i, Ground.squaredNorm C (Ground.simples C i) =
      ((Ground.fpSimple C i ^ 2 : ℝ) : ℂ)) : p.IsSpherical := by
  apply (isSpherical_iff_simple_dimensions C p).2
  intro i
  let X := Ground.simples C i
  letI : Simple X := Ground.simples_simple C i
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

/-- The real saturated ENO hypotheses and the intrinsic norm identity
construct an actual positive spherical structure. -/
theorem eno_real_saturated_root_yields_positive_spherical
    (C : Ground.BraidedFusionCategory.{v,u}) (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, rootDimension C i = (d i : ℂ))
    (hd : ∀ i, |d i| = Ground.fpSimple C i)
    (hinv : ∀ i j k, (multiplicityDefect C i j k).toLinearMap *
      (multiplicityDefect C i j k).toLinearMap = 1)
    (heig : ∀ i j, ∑ k, enoTraceMatrix C i j k * rootDimension C k =
      rootDimension C i * rootDimension C j)
    (hnat : ∀ {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y'),
      (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
        (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ))
    (hnorm : ∀ i, Ground.squaredNorm C (Ground.simples C i) =
      ((Ground.fpSimple C i ^ 2 : ℝ) : ℂ)) :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  obtain ⟨p, hp⟩ := eno_real_saturated_root_yields_positive_pivotal C d hreal hd hinv heig hnat
  exact ⟨p, spherical_of_fp_dimensions_and_squaredNorms C p hp hnorm, hp⟩

/-- ENO's trace-matrix bound and the root-norm identity turn global
pseudo-unitarity into pointwise FP saturation. -/
theorem eno_root_norm_saturation_of_pseudoUnitary
    (C : Ground.BraidedFusionCategory.{v,u})
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

/-- Once the root dimensions are made real, ENO's remaining categorical
identities and pseudo-unitarity construct the positive spherical structure. -/
theorem eno_pseudoUnitary_real_root_yields_positive_spherical
    (C : Ground.BraidedFusionCategory.{v,u}) (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, rootDimension C i = (d i : ℂ))
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
  have hs := eno_root_norm_saturation_of_pseudoUnitary C hinv heig hnorm hpu
  have hd : ∀ i, |d i| = Ground.fpSimple C i := by
    intro i
    simpa [hreal, Complex.norm_real] using hs i
  apply eno_real_saturated_root_yields_positive_spherical C d hreal hd hinv heig hnat
  intro i
  rw [hnorm i, hs i]


end PropertyF.Ground.Dimensions
