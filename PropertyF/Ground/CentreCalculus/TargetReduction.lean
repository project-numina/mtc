module
public import PropertyF.Ground.CentreCalculus.ActualCoreIntegrality
public import PropertyF.Ground.Integrate.CenterSquareReduction

/-! Wire the proved symmetric-core integrality into the target reduction. -/
@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground.CentreCalculus
universe v u

/-- The target follows from an FP-valued spherical modular centre and the
remaining finite mixed-monodromy assertion. Centre dimension and symmetric-core
integrality are supplied by theorems. -/
theorem target_of_center_image_monodromy
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
            (∀ y, (∀ a ∈ CentreCabling.imageLabels C,
              Modular.categoricalS Z p a y = Modular.simpleDimension Z p a * Modular.simpleDimension Z p y) →
              ∀ a ∈ CentreCabling.imageLabels C,
                IsOfFinOrder (End.of (Modular.doubleBraiding (simples Z a) (simples Z y))))) :
    TargetStatement.{v,u} := by
  apply Ground.target_of_center_image_monodromy_no_square
  intro C hPU hF
  obtain ⟨hR, hFusion, p, hp, hdim, hdet, hfinite⟩ := hCenter C hPU hF
  letI := hR
  letI := hFusion
  exact ⟨hR, hFusion, p, hp, hdim, hdet,
    actual_symmetricCore_integrality C p hp hdim, hfinite⟩

end PropertyF.Ground.CentreCalculus
