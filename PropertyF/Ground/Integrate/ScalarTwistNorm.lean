module
public import PropertyF.Ground.Integrate.ScalarTwistModular

/-! Galois transport of intrinsic squared norms and global dimensions. -/

@[expose] public noncomputable section
set_option linter.style.haveILetI false
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.ScalarTwist
universe v u
variable (C : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ)

set_option backward.isDefEq.respectTransparency false in
/-- Each intrinsic squared norm transforms by σ. -/
theorem squaredNorm_twist (X : C.Obj) :
    squaredNorm (category C σ) X = σ (squaredNorm C X) := by
  unfold squaredNorm
  rw [map_mul]
  congr 1
  · exact unitScalar_twist C σ _
  · exact unitScalar_twist C σ _

set_option backward.isDefEq.respectTransparency false in
/-- The categorical global dimension transforms by σ. -/
theorem globalDimension_twist : globalDimension (category C σ) = σ (globalDimension C) := by
  obtain ⟨e, he⟩ := Modular.simpleLabels_equiv C (category C σ) (conjugate C σ).equivalence
  unfold globalDimension
  calc
    ∑ j, squaredNorm (category C σ) (simples (category C σ) j) =
        ∑ i, squaredNorm (category C σ) (simples (category C σ) (e i)) :=
      (e.sum_comp (fun j => squaredNorm (category C σ) (simples (category C σ) j))).symm
    _ = ∑ i, σ (squaredNorm C (simples C i)) := by
      apply Finset.sum_congr rfl
      intro i _
      letI : Simple ((conjugate C σ).equivalence.functor.obj (simples C i)) := by
        letI : Simple (simples C i) := simples_simple C i
        exact CategoryTheory.simple_obj (conjugate C σ).equivalence.functor _
      letI : Simple (simples (category C σ) (e i)) := simples_simple _ _
      rw [← Dimensions.target_squaredNorm_iso (category C σ) (he i).some]
      exact squaredNorm_twist C σ _
    _ = σ (∑ i, squaredNorm C (simples C i)) := by rw [map_sum]

/-- Scalar twisting preserves the global FP dimension. -/
theorem globalFPDimension_twist : globalFPDimension (category C σ) = globalFPDimension C :=
  (Modular.conjugate_globalFPDimension C (category C σ) (conjugate C σ)).symm

end PropertyF.Ground.ScalarTwist
