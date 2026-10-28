module
public import PropertyF.Ground.CentreInduction.Adjunction
public import PropertyF.Ground.Dimensions.IntrinsicNonzero

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

/-- An actual right adjoint with the standard underlying induction objects
supplies the categorical square formula when the centre is spherical with
FP-valued dimensions. Existence of the adjoint and the centre instances remains
an explicit premise. -/
theorem center_globalDimension_of_adjunction
    (I : C.Obj ⥤ CategoryTheory.Center C.Obj)
    (adj : CategoryTheory.Center.forget C.Obj ⊣ I)
    (hI : ∀ i, Nonempty ((I.obj (simples C i)).1 ≅
      CentreInduction.underlying C (simples C i)))
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hp : p.IsSpherical)
    (hdim : Modular.HasFPSimpleDimensions (Integrate.bundledCenter C) p) :
    globalDimension (Integrate.bundledCenter C) = (globalFPDimension C : ℂ) ^ 2 := by
  have hpu : PseudoUnitary (Integrate.bundledCenter C) := by
    unfold PseudoUnitary globalFPDimension
    rw [Dimensions.target_globalDimension_eq_sum_squares (Integrate.bundledCenter C) p hp]
    simp only [← Dimensions.rightTrace_id, Complex.ofReal_sum, Complex.ofReal_pow]
    apply Finset.sum_congr rfl
    intro i _
    change Dimensions.pivotalDimension (Integrate.bundledCenter C) p
      (simples (Integrate.bundledCenter C) i) ^ 2 = _
    rw [show Dimensions.pivotalDimension (Integrate.bundledCenter C) p
        (simples (Integrate.bundledCenter C) i) = (fpSimple (Integrate.bundledCenter C) i : ℂ) by
      simpa [Modular.simpleDimension, Dimensions.pivotalDimension, Dimensions.rightTrace_id,
        unitScalar_eq_equiv] using hdim i]
  change globalDimension (Integrate.bundledCenter C) =
    (globalFPDimension (Integrate.bundledCenter C) : ℂ) at hpu
  rw [hpu, CentreInduction.globalFPDimension_square_of_adjunction C I adj hI, Complex.ofReal_pow]

end PropertyF.Ground.CentreModular
