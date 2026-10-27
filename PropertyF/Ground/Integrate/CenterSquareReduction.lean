module
public import PropertyF.Ground.CentreCabling.TargetReduction
public import PropertyF.Ground.CentreInduction.ActualFusion
public import PropertyF.Ground.CentreModular.InductionDimension

/-! The constructed induction adjunction removes the centre square premise. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- The centre square follows from its actual induction adjunction as soon as
its genuine fusion structure and FP-valued spherical structure are available. -/
theorem center_globalDimension_square_of_actual_induction
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (p : Dimensions.PivotalStructure (C := (Integrate.bundledCenter C).Obj))
    (hp : p.IsSpherical)
    (hdim : ∀ i, Modular.simpleDimension (Integrate.bundledCenter C) p i =
      (fpSimple (Integrate.bundledCenter C) i : ℂ)) :
    globalDimension (Integrate.bundledCenter C) = (globalFPDimension C : ℂ) ^ 2 := by
  apply CentreModular.center_globalDimension_of_adjunction C
    (CentreInduction.induction C) (CentreInduction.actualAdjunction C)
    (fun _ => ⟨Iso.refl _⟩) p hp
  intro i
  simpa [Modular.simpleDimension, Dimensions.pivotalDimension, Dimensions.rightTrace_id,
    Dimensions.groundUnitScalarEquiv_apply, unitScalar_eq_equiv] using hdim i

/-- The target reduces to the actual positive modular centre, core
integrality, and finite mixed monodromy on the specified image labels. Its
categorical dimension square is a theorem, not an extra premise. -/
theorem target_of_center_image_monodromy_no_square
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}), PseudoUnitary C →
      HasPropertyF C.Obj →
      ∃ (hR : RigidCategory (CategoryTheory.Center C.Obj)),
        letI := hR
        ∃ (hFusion : IsFusionCategory (CategoryTheory.Center C.Obj)),
          letI := hFusion
          let Z := Integrate.bundledCenter C
          ∃ (p : Dimensions.PivotalStructure (C := Z.Obj)),
            p.IsSpherical ∧
            (∀ i, Modular.simpleDimension Z p i = (fpSimple Z i : ℂ)) ∧
            (Modular.categoricalS Z p).det ≠ 0 ∧
            (∀ y ∈ CentreCabling.symmetricCore C,
              ∃ z : ℤ, Modular.simpleDimension Z p y = z) ∧
            (∀ y, (∀ a ∈ CentreCabling.imageLabels C,
              Modular.categoricalS Z p a y = Modular.simpleDimension Z p a * Modular.simpleDimension Z p y) →
              ∀ a ∈ CentreCabling.imageLabels C,
                IsOfFinOrder (End.of (Modular.doubleBraiding (simples Z a) (simples Z y))))) :
    TargetStatement.{v,u} := by
  apply target_of_center_image_monodromy
  intro C hPU hF
  obtain ⟨hR, hFusion, p, hp, hdim, hdet, hintegral, hfinite⟩ := hCenter C hPU hF
  letI := hR
  letI := hFusion
  exact ⟨hR, hFusion, p, hp, hdim, hdet,
    center_globalDimension_square_of_actual_induction C p hp hdim, hintegral, hfinite⟩

end PropertyF.Ground
