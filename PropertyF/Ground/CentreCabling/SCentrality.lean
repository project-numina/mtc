module
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.Dimensions.DimensionCharacter
public import PropertyF.Ground.Centre.Embeddings

/-! Categorical centrality implies the numerical S-matrix test. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCabling
universe v u

/-- Centralizing simple objects satisfy the S-matrix equality. This direction
needs neither nondegeneracy nor positivity. -/
theorem categoricalS_eq_of_doubleBraiding (D : Ground.BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := D.Obj)) (i j : Fin (rank D))
    (h : Modular.doubleBraiding (simples D i) (simples D j) = 𝟙 _) :
    Modular.categoricalS D p i j =
      Modular.simpleDimension D p i * Modular.simpleDimension D p j := by
  change Ground.unitScalarEquiv D (p.rightTrace
      (Modular.doubleBraiding (simples D i) (simples D j))) = _
  rw [h]
  have ht := Dimensions.pivotalDimension_tensor D p (simples D i) (simples D j)
  simpa [Dimensions.pivotalDimension, Modular.simpleDimension,
    Ground.unitScalar_eq_equiv] using ht

end PropertyF.Ground.CentreCabling
