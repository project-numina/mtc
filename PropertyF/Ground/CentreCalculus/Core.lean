module
public import PropertyF.Ground.Centre.Basic

/-! The common centralizer consists of self-centralizing objects. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- An object centralizing both canonical images centralizes itself. The
negative-image condition places it in the positive image, to which the
positive-image condition can then be applied. -/
theorem commonCentralizer_self (Y : CategoryTheory.Center C)
    (hp : ∀ X : C, Centre.Centralizes Y ((CategoryTheory.Center.ofBraided C).obj X))
    (hn : ∀ X : C, Centre.Centralizes Y ((Centre.negative C).obj X)) :
    Centre.Centralizes Y Y := by
  let e := Centre.positiveIsoOfCentralizesNegative Y hn
  apply Centre.centralizes_symm
  apply Centre.centralizes_of_iso_left e
  exact Centre.centralizes_symm (hp Y.1)

end PropertyF.Ground.CentreCalculus
