module
public import MTC.Center.BraidWords.TypeA
public import MTC.Center.Helpers

/-! # Finite braid images of self-transparent objects -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Braided MTC.Center.Trace
namespace MTC.PropertyF.Pivotal
set_option linter.style.haveILetI false
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The actual braid image of a self-transparent object is a subgroup of
its actual permutation image and hence finite. -/
theorem objectPropertyF_of_selfTransparent {X : C} (hX : SelfTransparent X) :
    ObjectPropertyF X := by
  intro n
  let ρ := permAction X hX n
  have hsub : braidImage X n ≤ ρ.range := by
    apply (Subgroup.closure_le ρ.range).2
    rintro _ ⟨i, rfl⟩
    exact ⟨adjacentSwap i, permAction_swap hX i⟩
  letI : Finite ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  exact Finite.of_injective (Subgroup.inclusion hsub) (Subgroup.inclusion_injective hsub)

/-- Every transparent object has finite braid images. -/
theorem objectPropertyF_of_transparent {X : C} (hX : MTC.Center.Transparent X) :
    ObjectPropertyF X :=
  objectPropertyF_of_selfTransparent (hX X)

/-- Any symmetric braided monoidal category has property F. -/
theorem propertyF_of_symmetric (D : Type u) [Category.{v} D] [MonoidalCategory D]
    [SymmetricCategory D] : HasPropertyF D := by
  intro X
  apply objectPropertyF_of_selfTransparent
  exact SymmetricCategory.symmetry X X

end MTC.PropertyF.Pivotal
end
