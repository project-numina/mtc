module
public import PropertyF.Ground.Cabling.Generated
public import PropertyF.Ground.Modular.BraidFunctor

/-! The generated full subcategory has the ambient braid images. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C]

/-- The braided full inclusion identifies braid images on every number of
strands; neither rigidity nor fusion data is required. -/
def generatedInclusionBraidImageIso (X : C) (Y : generatedCategory X) (n : ℕ) :
    braidImage Y n ≃* braidImage ((generatedInclusion X).obj Y) n :=
  Ground.Modular.braidImageFunctorIso (generatedInclusion X) Y n

end PropertyF
