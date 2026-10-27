module
public import PropertyF.Ground.CentreInduction.Underlying
public import PropertyF.Ground.Integrate.CenterBundle

/-! The numerical consequence of the induction adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreInduction
universe v u

/-- Once induced simple representatives have the expected underlying objects
and the adjunction supplies the displayed Hom dimension equality, the global
FP dimension of the actual centre is the square of that of the base. The
hypotheses explicitly isolate the still-unconstructed induction adjunction. -/
theorem globalFPDimension_square_of_induction
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (I : Fin (rank C) → (Integrate.bundledCenter C).Obj)
    (hI : ∀ i, Nonempty ((I i).1 ≅ underlying C (simples C i)))
    (hadj : ∀ i j,
      Module.finrank ℂ ((simples (Integrate.bundledCenter C) j : CategoryTheory.Center C.Obj) ⟶ I i) =
      Module.finrank ℂ ((simples (Integrate.bundledCenter C) j).1 ⟶ simples C i)) :
    globalFPDimension (Integrate.bundledCenter C) = (globalFPDimension C) ^ 2 := by
  classical
  have hdim (i : Fin (rank C)) :
      fpDimension (Integrate.bundledCenter C) (I i) = globalFPDimension C * fpSimple C i := by
    obtain ⟨e⟩ := hI i
    calc
      _ = fpDimension C (I i).1 := (Integrate.center_forget_fpDimension C (I i)).symm
      _ = fpDimension C (underlying C (simples C i)) := fpDimension_iso C e
      _ = _ := by rw [fpDimension_underlying, fpDimension_simple]
  have hbase (j : Fin (rank (Integrate.bundledCenter C))) :
      ∑ i, (Module.finrank ℂ ((simples (Integrate.bundledCenter C) j).1 ⟶ simples C i) : ℝ) * fpSimple C i =
        fpSimple (Integrate.bundledCenter C) j := by
    calc
      _ = fpDimension C (simples (Integrate.bundledCenter C) j).1 := by
        unfold fpDimension
        apply Finset.sum_congr rfl
        intro i _
        rw [finrank_to_simple_eq_from_simple C]
      _ = fpDimension (Integrate.bundledCenter C) (simples (Integrate.bundledCenter C) j) := Integrate.center_forget_fpDimension C _
      _ = _ := fpDimension_simple (Integrate.bundledCenter C) j
  have hsum : (∑ i, fpSimple C i * fpDimension (Integrate.bundledCenter C) (I i)) = globalFPDimension (Integrate.bundledCenter C) := by
    simp_rw [fpDimension]
    simp_rw [hadj]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, fpSimple (Integrate.bundledCenter C) j *
          (∑ i, (Module.finrank ℂ ((simples (Integrate.bundledCenter C) j).1 ⟶ simples C i) : ℝ) * fpSimple C i) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by simp_rw [hbase]; simp [globalFPDimension, pow_two]
  calc
    globalFPDimension (Integrate.bundledCenter C) = ∑ i, fpSimple C i * fpDimension (Integrate.bundledCenter C) (I i) := hsum.symm
    _ = (globalFPDimension C) ^ 2 := by
      simp_rw [hdim]
      rw [pow_two]
      conv_rhs => lhs; rw [globalFPDimension]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

end PropertyF.Ground.CentreInduction
