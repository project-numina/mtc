module
public import PropertyF.Ground.CentreCabling.ImageCore
public import PropertyF.Ground.Integrate.ActualCenterReduction

/-! The frozen target reduced using the actual symmetric core. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

/-- The target follows if the simple constituents of the canonical embeddings,
paired with labels passing their S-centralizer test, have finite-order mixed
monodromy. -/
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
            (Modular.HasFPSimpleDimensions Z p) ∧
            (Modular.categoricalS Z p).det ≠ 0 ∧
            globalDimension Z = (globalFPDimension C : ℂ) ^ 2 ∧
            (HasIntegralSimpleDimensionsOn Z p (CentreCabling.symmetricCore C)) ∧
            (CentreCabling.HasFiniteImageCentralizerMonodromy C p)) :
    TargetStatement.{v,u} := by
  apply target_of_actual_center
  intro C hPU hF
  obtain ⟨hR, hFusion, p, hp, hdim, hdet, hglobal, hintegral, hfinite⟩ := hCenter C hPU hF
  let := hR
  let := hFusion
  refine ⟨hR, hFusion, p, CentreCabling.symmetricCore C,
    (↑(CentreCabling.productLabels C) : Set _), hp, hdim, hdet, hglobal, hintegral, ?_, ?_⟩
  · intro y hy
    exact (CentreCabling.mem_productLabels C y).mpr
      (CentreCabling.productLabels_doubleCentralizer_of_image_monodromy C p hp hdet hdim hfinite y hy)
  · intro y hy
    exact (CentreCabling.mem_productLabels C y).mp hy

end PropertyF.Ground
