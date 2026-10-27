module
public import PropertyF.Ground.Fusion.Schur
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! Algebraic integrality of the character values from the fusion equations. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators Matrix

namespace PropertyF.FusionData
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C] [Abelian C] [Linear ℂ C] [RigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Each simple character value is integral, since it is an eigenvalue of
the integer matrix of multiplication by that simple. -/
theorem fpSimple_isIntegral (F : FusionData C) (i : Fin F.rank) :
    IsIntegral ℤ (F.fpSimple i) := by
  classical
  let A : Matrix (Fin F.rank) (Fin F.rank) ℤ := fun j k =>
    Module.finrank ℂ (F.simpleObject k ⟶ F.simpleObject i ⊗ F.simpleObject j)
  let B : Matrix (Fin F.rank) (Fin F.rank) ℝ := A.map (Int.castRingHom ℝ)
  have heigen : B *ᵥ F.fpSimple = F.fpSimple i • F.fpSimple := by
    ext j
    change (∑ k, ((Module.finrank ℂ (F.simpleObject k ⟶ F.simpleObject i ⊗
      F.simpleObject j) : ℤ) : ℝ) * F.fpSimple k) = F.fpSimple i * F.fpSimple j
    simpa using (F.fp_character i j).symm
  have hzero : (Matrix.scalar (Fin F.rank) (F.fpSimple i) - B) *ᵥ F.fpSimple = 0 := by
    rw [Matrix.sub_mulVec, heigen]
    ext j
    simp [Matrix.scalar_apply]
  have hdet : (Matrix.scalar (Fin F.rank) (F.fpSimple i) - B).det = 0 := by
    apply Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hzero
      (i := F.unitIndex)
    exact mem_nonZeroDivisors_of_ne_zero (ne_of_gt (F.fp_positive F.unitIndex))
  refine ⟨A.charpoly, A.charpoly_monic, ?_⟩
  change Polynomial.eval₂ (Int.castRingHom ℝ) (F.fpSimple i) A.charpoly = 0
  rw [Polynomial.eval₂_eq_eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  exact hdet

/-- The FP dimension of any object is an algebraic integer. -/
theorem fpDimension_isIntegral (F : FusionData C) (X : C) :
    IsIntegral ℤ (F.fpDimension X) := by
  unfold fpDimension
  apply IsIntegral.sum
  intro i _
  exact (isIntegral_natCast _).mul (F.fpSimple_isIntegral i)

/-- The global FP dimension is an algebraic integer. -/
theorem globalFPDimension_isIntegral (F : FusionData C) :
    IsIntegral ℤ F.globalFPDimension := by
  unfold globalFPDimension
  apply IsIntegral.sum
  intro i _
  exact (F.fpSimple_isIntegral i).pow 2

end PropertyF.FusionData
