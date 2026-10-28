module
public import PropertyF.Ground.Cabling.MoveHead
public import PropertyF.Ground.Calculus.StrandCoherence
open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Calculus
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

end PropertyF
