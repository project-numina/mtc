module
public import MTC.Fusion.Agreement
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

open MTC.Braided

/-! # Frobenius–Perron dimensions of objects

`fpDimension` is the sum of simple multiplicities weighted by `fpSimple`.
It is invariant under isomorphisms and duality, additive on finite biproducts,
and multiplicative under tensor products. Faithful additive monoidal functors
preserve it.

See Etingof–Gelaki–Nikshych–Ostrik, *Tensor Categories*, §3.3.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators

namespace MTC

variable (D : BraidedFusionCategory)
attribute [local instance] Abelian.hasFiniteBiproducts

/-- The positive character evaluated on the simple multiplicities of an object. -/
def fpDimension (D : BraidedFusionCategory) (X : D.Obj) : ℝ :=
  ∑ i, (simpleMultiplicity D i X : ℝ) * fpSimple D i

variable {D} in
theorem fpDimension_simple (j : Fin (rank D)) :
    fpDimension D (simples D j) = fpSimple D j :=
  by simp [fpDimension, finrank_simples_hom]

variable {D} in
theorem fpDimension_iso {X Y : D.Obj} (e : X ≅ Y) :
    fpDimension D X = fpDimension D Y :=
  Finset.sum_congr rfl fun i _ => congrArg (fun n : ℕ => (n : ℝ) * fpSimple D i)
    (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e).finrank_eq

variable {D} in
theorem fpDimension_nonneg (X : D.Obj) :
    0 ≤ fpDimension D X :=
  Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (fpSimple_pos D i).le

theorem fpDimension_unit : fpDimension D (𝟙_ D.Obj) = 1 :=
  (unitIndex_iso D).elim fun e ↦
    (fpDimension_iso e).symm.trans ((fpDimension_simple _).trans (fpSimple_unit D))

variable {D} in
/-- Every nonzero object has FP dimension at least one. -/
theorem one_le_fpDimension {X : D.Obj}
    (hX : ¬ IsZero X) : 1 ≤ fpDimension D X :=
  (exists_positive_multiplicity (simples_decompose D X)
    (fun _ ↦ IsFusionCategory.hom_finite _ _) hX).elim fun i hi ↦
    (one_le_mul_of_one_le_of_one_le (Nat.one_le_cast.mpr hi) (one_le_fpSimple i)).trans
      (Finset.single_le_sum
        (fun j _ ↦ mul_nonneg (Nat.cast_nonneg _) (fpSimple_pos D j).le) (Finset.mem_univ i))

variable {D} in
/-- Hom multiplicities of a tensor product are the convolution of the
multiplicities of its factors with the fusion coefficients. -/
theorem tensor_multiplicity_expanded (X Y : D.Obj) (k : Fin (rank D)) :
    simpleMultiplicity D k (X ⊗ Y) =
      ∑ i, ∑ j, simpleMultiplicity D i X *
        simpleMultiplicity D j Y * fusionCoeff D i j k := by
  have he (j : Fin (rank D)) : simpleMultiplicity D k (X ⊗ simples D j) =
      ∑ i, simpleMultiplicity D i X * fusionCoeff D i j k := by
    rw [show simpleMultiplicity D k (X ⊗ simples D j) =
        simpleMultiplicity D k (simples D j ⊗ X) from
          (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (β_ X (simples D j))).finrank_eq,
      tensor_multiplicity]
    change (∑ i, simpleMultiplicity D i X * fusionCoeff D j i k) = _
    simp_rw [fusionCoeff_comm D j]
  rw [tensor_multiplicity, Finset.sum_comm]
  simp [he, Finset.mul_sum, mul_comm, mul_left_comm]

variable {D} in
/-- FP dimension is multiplicative on tensor products. -/
theorem fpDimension_tensor (X Y : D.Obj) :
    fpDimension D (X ⊗ Y) = fpDimension D X * fpDimension D Y := by
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

variable {D} in
/-- Multiplicity of a simple in a dual object equals the multiplicity of its
dual in the original object. -/
theorem dual_multiplicity (X : D.Obj) (i : Fin (rank D)) :
    simpleMultiplicity D i (ᘁX) = simpleMultiplicity D (dualIndex D i) X := by
  obtain ⟨e⟩ := dualIndex_iso i
  let : Simple (simples D (dualIndex D i)) := simples_simple D _
  exact (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (ρ_ (ᘁX : D.Obj)).symm).trans
    (tensorLeftHomLinearEquiv (k := ℂ) (simples D i) (ᘁX) X (𝟙_ D.Obj)).symm |>.trans
    (CategoryTheory.Linear.homCongr ℂ (β_ X (simples D i)) (Iso.refl _)) |>.trans
    (tensorLeftHomLinearEquiv (k := ℂ) X (ᘁ(simples D i)) (simples D i) (𝟙_ D.Obj)) |>.trans
    (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (ρ_ (ᘁ(simples D i) : D.Obj))) |>.trans
    (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) e) |>.finrank_eq |>.trans
    (finrank_to_simple_eq_from_simple X (simples D (dualIndex D i)))

variable {D} in
/-- FP dimension is invariant under taking a right dual. -/
theorem fpDimension_rightDual (X : D.Obj) :
    fpDimension D (Xᘁ) = fpDimension D X :=
  (fpDimension_iso (leftDualIso inferInstance
    (BraidedCategory.exactPairing_swap X (Xᘁ)))).symm.trans
      (show fpDimension D (ᘁX) = fpDimension D X from by
        simpa only [fpDimension, dual_multiplicity, fpSimple_dual,
          show ⇑(dualEquiv D) = dualIndex D from rfl] using
          Equiv.sum_comp (dualEquiv D) (fun i ↦ (simpleMultiplicity D i X : ℝ) * fpSimple D i))

end MTC

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.Functor.Monoidal
open scoped BigOperators
namespace MTC
universe v u v' u'
attribute [local instance] Abelian.hasFiniteBiproducts IsFusionCategory.hom_finite
variable (C : BraidedFusionCategory.{v,u}) (D : BraidedFusionCategory.{v',u'})

variable {D} in
/-- FP dimension is additive over finite biproducts. -/
theorem fpDimension_biproduct {ι : Type} [Fintype ι] (V : ι → D.Obj) :
    fpDimension D (⨁ V) = ∑ i, fpDimension D (V i) := by
  simp only [fpDimension, finrank_hom_biproduct, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

variable {C D} in
/-- Applying an additive functor to a canonical decomposition expresses the
FP dimension of the image as the sum of the dimensions of image simples. -/
theorem fpDimension_functor_decomposition (F : C.Obj ⥤ D.Obj) [F.Additive] (X : C.Obj) :
    fpDimension D (F.obj X) = ∑ i,
      (simpleMultiplicity C i X : ℝ) * fpDimension D (F.obj (simples C i)) :=
  (exists_canonical_decomposition C X).elim fun e ↦ by
    simp [fpDimension_iso (F.mapIso e ≪≫ F.mapBiproduct _), fpDimension_biproduct,
      Fintype.sum_sigma]

variable {C D} in
/-- An additive faithful strong monoidal functor preserves FP dimension. -/
theorem fpDimension_functor (F : C.Obj ⥤ D.Obj) [F.Additive] [F.Faithful] [F.Monoidal]
    (X : C.Obj) :
    fpDimension D (F.obj X) = fpDimension C X := by
  let f : Fin (rank C) → ℝ := fun i => fpDimension D (F.obj (simples C i))
  have hpos (i) : 0 < f i :=
    letI : Simple (simples C i) := simples_simple C i
    lt_of_lt_of_le zero_lt_one (one_le_fpDimension fun hz ↦
      id_nonzero _ (F.map_eq_zero_iff.mp (by simpa using (IsZero.iff_id_eq_zero _).mp hz)))
  have hunit : f (unitIndex C) = 1 :=
    (unitIndex_iso C).elim fun e ↦
      (fpDimension_iso (F.mapIso e ≪≫ (εIso F).symm)).trans (fpDimension_unit D)
  have hmul (i j) : f i * f j = ∑ k, (fusionCoeff C i j k : ℝ) * f k :=
    (fpDimension_tensor _ _).symm.trans ((fpDimension_iso (μIso F _ _)).trans
      (fpDimension_functor_decomposition F _))
  have heq : f = fpSimple C := positive_symmetric_eigenvector_unique (totalFusionMatrix_pos C)
    (Matrix.ext fun i j ↦ totalFusionMatrix_symmetric C j i) hpos (fpSimple_pos C)
    hunit (fpSimple_unit C) (character_total_eigenvector hmul)
    (character_total_eigenvector (fpSimple_mul C))
  simpa only [fpDimension, ← heq, f] using fpDimension_functor_decomposition F X

end MTC
