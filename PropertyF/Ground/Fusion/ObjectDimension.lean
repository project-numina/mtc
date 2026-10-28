module
public import PropertyF.Ground.Fusion.Agreement
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! Frobenius–Perron dimension of an arbitrary object. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace PropertyF.Ground

variable (D : BraidedFusionCategory)
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The positive character evaluated on the simple multiplicities of an object. -/
def fpDimension (D : BraidedFusionCategory) (X : D.Obj) : ℝ :=
  ∑ i, (Module.finrank ℂ (simples D i ⟶ X) : ℝ) * fpSimple D i

theorem fpDimension_simple (j : Fin (rank D)) :
    fpDimension D (simples D j) = fpSimple D j := by
  classical
  simp [fpDimension, finrank_simples_hom]

theorem fpDimension_iso {X Y : D.Obj} (e : X ≅ Y) :
    fpDimension D X = fpDimension D Y :=
  Finset.sum_congr rfl fun i _ => congrArg (fun n : ℕ => (n : ℝ) * fpSimple D i)
    (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq

theorem fpDimension_nonneg (X : D.Obj) :
    0 ≤ fpDimension D X :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (fpSimple_pos D i).le

theorem fpDimension_unit : fpDimension D (𝟙_ D.Obj) = 1 :=
  (unitIndex_iso D).elim fun e ↦
    (fpDimension_iso D e).symm.trans ((fpDimension_simple D _).trans (fpSimple_unit D))

/-- A nonzero object has a nonzero simple multiplicity. -/
theorem exists_positive_multiplicity {X : D.Obj}
    (hX : ¬ IsZero X) : ∃ i, 0 < Module.finrank ℂ (simples D i ⟶ X) := by
  classical
  have hid : (𝟙 X : X ⟶ X) ≠ 0 := by simpa [IsZero.iff_id_eq_zero] using hX
  obtain ⟨i, s, _, hs, _⟩ := exists_simple_retract D hid
  let : FiniteDimensional ℂ (X ⟶ simples D i) := IsFusionCategory.hom_finite _ _
  let : Simple (simples D i) := simples_simple D i
  refine ⟨i, ?_⟩
  rw [← finrank_to_simple_eq_from_simple X (simples D i)]
  exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨s, hs⟩

/-- Every nonzero object has FP dimension at least one. -/
theorem one_le_fpDimension {X : D.Obj}
    (hX : ¬ IsZero X) : 1 ≤ fpDimension D X := by
  classical
  obtain ⟨i, hi⟩ := exists_positive_multiplicity D hX
  have hcoeff : (1 : ℝ) ≤ Module.finrank ℂ (simples D i ⟶ X) := by exact_mod_cast hi
  have hterm : (1 : ℝ) ≤
      (Module.finrank ℂ (simples D i ⟶ X) : ℝ) * fpSimple D i :=
    one_le_mul_of_one_le_of_one_le hcoeff (one_le_fpSimple D i)
  unfold fpDimension
  exact hterm.trans (Finset.single_le_sum
    (f := fun j => (Module.finrank ℂ (simples D j ⟶ X) : ℝ) * fpSimple D j)
    (fun j _ => mul_nonneg (Nat.cast_nonneg _) (fpSimple_pos D j).le) (Finset.mem_univ i))

/-- Hom multiplicities of a tensor product are the convolution of the
multiplicities of its factors with the fusion coefficients. -/
theorem tensor_multiplicity_expanded (X Y : D.Obj)
    (k : Fin (rank D)) :
    Module.finrank ℂ (simples D k ⟶ X ⊗ Y) =
      ∑ i, ∑ j, Module.finrank ℂ (simples D i ⟶ X) *
        Module.finrank ℂ (simples D j ⟶ Y) * fusionCoeff D i j k := by
  classical
  have he (j : Fin (rank D)) : Module.finrank ℂ (simples D k ⟶ X ⊗ simples D j) =
      ∑ i, Module.finrank ℂ (simples D i ⟶ X) * fusionCoeff D i j k := by
    rw [(CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (β_ X (simples D j))).finrank_eq,
      tensor_multiplicity]
    change (∑ i, Module.finrank ℂ (simples D i ⟶ X) * fusionCoeff D j i k) = _
    simp_rw [fusionCoeff_comm D j]
  rw [tensor_multiplicity]
  simp_rw [he, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc, mul_comm]

/-- FP dimension is multiplicative on tensor products. -/
theorem fpDimension_tensor (X Y : D.Obj) :
    fpDimension D (X ⊗ Y) = fpDimension D X * fpDimension D Y := by
  classical
  unfold fpDimension
  simp_rw [tensor_multiplicity_expanded, Nat.cast_sum, Nat.cast_mul]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext i
    rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← fpSimple_mul]
  ring

/-- Multiplicity of a simple in a dual object equals the multiplicity of its
dual in the original object. -/
theorem dual_multiplicity (X : D.Obj) (i : Fin (rank D)) :
    Module.finrank ℂ (simples D i ⟶ ᘁX) =
      Module.finrank ℂ (simples D (dualIndex D i) ⟶ X) := by
  obtain ⟨e⟩ := dualIndex_iso D i
  let : Simple (simples D (dualIndex D i)) := simples_simple D _
  exact (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (ρ_ (ᘁX : D.Obj)).symm).trans
    (tensorLeftHomLinearEquiv (simples D i) (ᘁX) X (𝟙_ D.Obj)).symm |>.trans
    (CategoryTheory.Linear.homCongr ℂ (β_ X (simples D i)) (Iso.refl _)) |>.trans
    (tensorLeftHomLinearEquiv X (ᘁ(simples D i)) (simples D i) (𝟙_ D.Obj)) |>.trans
    (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (ρ_ (ᘁ(simples D i) : D.Obj))) |>.trans
    (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e) |>.finrank_eq |>.trans
    (finrank_to_simple_eq_from_simple X (simples D (dualIndex D i)))

/-- FP dimension is invariant under taking a left dual. -/
theorem fpDimension_leftDual (X : D.Obj) :
    fpDimension D (ᘁX) = fpDimension D X := by
  classical
  unfold fpDimension
  have h := Equiv.sum_comp (dualEquiv D)
    (fun i => (Module.finrank ℂ (simples D i ⟶ X) : ℝ) * fpSimple D i)
  change (∑ i, (Module.finrank ℂ (simples D (dualIndex D i) ⟶ X) : ℝ) *
    fpSimple D (dualIndex D i)) = _ at h
  simpa only [dual_multiplicity, fpSimple_dual] using h

/-- FP dimension is invariant under taking a right dual. -/
theorem fpDimension_rightDual (X : D.Obj) :
    fpDimension D (Xᘁ) = fpDimension D X :=
  (fpDimension_iso D (leftDualIso inferInstance
    (BraidedCategory.exactPairing_swap X (Xᘁ)))).symm.trans (fpDimension_leftDual D X)

end PropertyF.Ground

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.Functor.Monoidal
open scoped BigOperators
namespace PropertyF.Ground
universe v u v' u'
attribute [local instance] Abelian.hasFiniteBiproducts

/-- FP dimension is additive over finite biproducts. -/
theorem fpDimension_biproduct (D : BraidedFusionCategory.{v,u})
    {ι : Type} [Fintype ι] (V : ι → D.Obj) :
    fpDimension D (⨁ V) = ∑ i, fpDimension D (V i) := by
  classical
  let : ∀ A B : D.Obj, FiniteDimensional ℂ (A ⟶ B) := IsFusionCategory.hom_finite
  unfold fpDimension
  simp_rw [finrank_hom_biproduct, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- Applying an additive functor to a canonical decomposition expresses the
FP dimension of the image as the sum of the dimensions of image simples. -/
theorem fpDimension_functor_decomposition (C : BraidedFusionCategory.{v,u})
    (D : BraidedFusionCategory.{v',u'})
    (F : C.Obj ⥤ D.Obj) [F.Additive] (X : C.Obj) :
    fpDimension D (F.obj X) = ∑ i,
      (Module.finrank ℂ (simples C i ⟶ X) : ℝ) * fpDimension D (F.obj (simples C i)) := by
  classical
  let m : Fin (rank C) → ℕ := fun i => Module.finrank ℂ (simples C i ⟶ X)
  let V : (Σ i, Fin (m i)) → C.Obj := fun p => simples C p.1
  obtain ⟨e⟩ := exists_canonical_decomposition C X
  let e' : F.obj X ≅ ⨁ (fun p => F.obj (V p)) := F.mapIso e ≪≫ F.mapBiproduct V
  rw [fpDimension_iso D e', fpDimension_biproduct, Fintype.sum_sigma]
  simp [V, m]

/-- An additive faithful strong monoidal functor preserves FP dimension. -/
theorem fpDimension_functor (C : BraidedFusionCategory.{v,u})
    (D : BraidedFusionCategory.{v',u'})
    (F : C.Obj ⥤ D.Obj) [F.Additive] [F.Faithful] [F.Monoidal] (X : C.Obj) :
    fpDimension D (F.obj X) = fpDimension C X := by
  classical
  let f : Fin (rank C) → ℝ := fun i => fpDimension D (F.obj (simples C i))
  have hpos (i) : 0 < f i :=
    letI : Simple (simples C i) := simples_simple C i
    lt_of_lt_of_le zero_lt_one (one_le_fpDimension D fun hz ↦
      id_nonzero _ (F.map_eq_zero_iff.mp (by simpa using (IsZero.iff_id_eq_zero _).mp hz)))
  have hunit : f (unitIndex C) = 1 :=
    (unitIndex_iso C).elim fun e ↦
      (fpDimension_iso D (F.mapIso e ≪≫ (εIso F).symm)).trans (fpDimension_unit D)
  have hmul (i j) : f i * f j = ∑ k, (fusionCoeff C i j k : ℝ) * f k :=
    (fpDimension_tensor D _ _).symm.trans ((fpDimension_iso D (μIso F _ _)).trans
      (fpDimension_functor_decomposition C D F _))
  have heq : f = fpSimple C := positive_symmetric_eigenvector_unique (totalFusionMatrix_pos C)
    (Matrix.ext fun i j ↦ totalFusionMatrix_symmetric C j i) hpos (fpSimple_pos C)
    hunit (fpSimple_unit C) (character_total_eigenvector C hmul)
    (character_total_eigenvector C (fpSimple_mul C))
  simpa only [fpDimension, ← heq, f] using fpDimension_functor_decomposition C D F X

end PropertyF.Ground
