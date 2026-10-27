module
public import PropertyF.Ground.Fusion.GeneratedStructure
public import PropertyF.Ground.Cabling.Generated
public import PropertyF.Ground.Fusion.SemisimpleSplit

/-! The generated full subcategory is abelian in a genuine fusion category. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Cabling
universe v u

/-- Semisimplicity of the ambient fusion category supplies the splittings
needed to construct the abelian structure on the generated subcategory. -/
@[instance_reducible] def generatedCategoryAbelian
    (D : Ground.BraidedFusionCategory.{v,u}) (X : D.Obj) :
    Abelian (generatedCategory X) :=
  Ground.generatedCategoryAbelian D X

end PropertyF.Ground.Cabling
