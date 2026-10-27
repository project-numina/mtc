module
public import PropertyF.Ground.Integrate.CenterBundle
public import PropertyF.Ground.Dimensions.PositiveCanonical

/-! The global-dimension calculation from the two numerical consequences of
centre induction. The induction construction and these consequences are not
assumed proved here. -/

@[expose] public noncomputable section
open CategoryTheory
open scoped BigOperators
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)]
variable [IsFusionCategory (CategoryTheory.Center C.Obj)]

/-- An induction family with the adjunction multiplicities and expected FP
sizes forces the global FP dimension of the actual centre to be the square of
that of the original category. No spherical structure is used. -/
theorem center_globalFPDimension_of_induction
    (I : Fin (rank C) → (Integrate.bundledCenter C).Obj)
    (hmult : ∀ i j,
      Module.finrank ℂ (simples (Integrate.bundledCenter C) j ⟶ I i) =
      Module.finrank ℂ ((CategoryTheory.Center.forget C.Obj).obj
        (simples (Integrate.bundledCenter C) j) ⟶ simples C i))
    (hsize : ∀ i, fpDimension (Integrate.bundledCenter C) (I i) =
      globalFPDimension C * fpSimple C i) :
    globalFPDimension (Integrate.bundledCenter C) = globalFPDimension C ^ 2 := by
  classical
  let Z := Integrate.bundledCenter C
  have hforget (j : Fin (rank Z)) :
      fpDimension C ((CategoryTheory.Center.forget C.Obj).obj (simples Z j)) = fpSimple Z j := by
    rw [Integrate.center_forget_fpDimension, fpDimension_simple]
  have hmult' (i : Fin (rank C)) (j : Fin (rank Z)) :
      Module.finrank ℂ (simples Z j ⟶ I i) =
      Module.finrank ℂ ((CategoryTheory.Center.forget C.Obj).obj (simples Z j) ⟶ simples C i) :=
    hmult i j
  have hsize' (i : Fin (rank C)) : fpDimension Z (I i) =
      globalFPDimension C * fpSimple C i := hsize i
  have hsum : (∑ i, fpSimple C i * fpDimension Z (I i)) =
      globalFPDimension Z := by
    simp only [fpDimension] at hforget ⊢
    simp_rw [hmult', finrank_to_simple_eq_from_simple C, Finset.mul_sum]
    rw [Finset.sum_comm]
    calc
      _ = ∑ j, (∑ i, (Module.finrank ℂ
            (simples C i ⟶ (CategoryTheory.Center.forget C.Obj).obj (simples Z j)) : ℝ) *
            fpSimple C i) * fpSimple Z j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = ∑ j, fpSimple Z j ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hforget j]
          ring
      _ = globalFPDimension Z := rfl
  rw [← hsum]
  simp_rw [hsize']
  calc
    _ = (∑ i, fpSimple C i ^ 2) * globalFPDimension C := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = globalFPDimension C ^ 2 := by rw [globalFPDimension, pow_two]

/-- With a positive spherical structure, the same calculation gives the
categorical global dimension required by the centre reduction. -/
theorem center_globalDimension_of_induction
    (I : Fin (rank C) → (Integrate.bundledCenter C).Obj)
    (hmult : ∀ i j,
      Module.finrank ℂ (simples (Integrate.bundledCenter C) j ⟶ I i) =
      Module.finrank ℂ ((CategoryTheory.Center.forget C.Obj).obj
        (simples (Integrate.bundledCenter C) j) ⟶ simples C i))
    (hsize : ∀ i, fpDimension (Integrate.bundledCenter C) (I i) =
      globalFPDimension C * fpSimple C i)
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hp : p.IsSpherical) (d : Fin (rank (Integrate.bundledCenter C)) → ℝ)
    (hreal : ∀ i, Dimensions.pivotalDimension (Integrate.bundledCenter C) p
      (simples (Integrate.bundledCenter C) i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) :
    globalDimension (Integrate.bundledCenter C) = (globalFPDimension C : ℂ) ^ 2 := by
  have hpu := Dimensions.positive_spherical_isPseudoUnitary (Integrate.bundledCenter C)
    p hp d hreal hpos
  change globalDimension (Integrate.bundledCenter C) =
    (globalFPDimension (Integrate.bundledCenter C) : ℂ) at hpu
  rw [hpu, center_globalFPDimension_of_induction C I hmult hsize, Complex.ofReal_pow]

end PropertyF.Ground.CentreModular
