module
public import PropertyF.Ground.Dimensions.DefectBraiding
public import PropertyF.Ground.Dimensions.ENOMatrices

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
/-- Braiding intertwines the actual root defect operators. -/
theorem multiplicityDefect_braiding (C : Ground.BraidedFusionCategory.{v,u})
    (i j k : Fin (Ground.rank C))
    (f : Ground.simples C k ⟶ Ground.simples C i ⊗ Ground.simples C j) :
    multiplicityDefect C i j k f ≫ (β_ (Ground.simples C i) (Ground.simples C j)).hom =
      multiplicityDefect C j i k (f ≫ (β_ (Ground.simples C i) (Ground.simples C j)).hom) := by
  simp only [multiplicityDefect_apply, Category.assoc, rootTensorDefect_braiding]

/-- The ENO trace coefficients are symmetric in the two tensor factors. -/
theorem enoTraceMatrix_braiding_symmetry (C : Ground.BraidedFusionCategory.{v,u})
    (i j k : Fin (Ground.rank C)) : enoTraceMatrix C i j k = enoTraceMatrix C j i k := by
  let X := Ground.simples C i
  let Y := Ground.simples C j
  let K := Ground.simples C k
  let E := Linear.homCongr ℂ (Iso.refl K) (β_ X Y)
  let A := (multiplicityDefect C i j k).toLinearMap
  let B := (multiplicityDefect C j i k).toLinearMap
  have hc : E.conj A = B := by
    ext w
    obtain ⟨f, rfl⟩ := E.surjective w
    change E (A (E.symm (E f))) = B (E f)
    rw [E.symm_apply_apply]
    simpa [E, A, B, Linear.homCongr_apply] using multiplicityDefect_braiding C i j k f
  letI : FiniteDimensional ℂ (K ⟶ X ⊗ Y) := Ground.IsFusionCategory.hom_finite _ _
  letI : FiniteDimensional ℂ (K ⟶ Y ⊗ X) := Ground.IsFusionCategory.hom_finite _ _
  have ht := congrArg (LinearMap.trace ℂ _) hc
  simpa only [LinearMap.trace_conj', enoTraceMatrix, A, B] using ht
end PropertyF.Ground.Dimensions
