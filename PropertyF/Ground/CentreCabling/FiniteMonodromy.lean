module
public import PropertyF.Ground.Calculus.ThreeRigidity
public import PropertyF.Ground.Modular.SAdditivity

/-! Property F gives finite order for mixed double braidings. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreCabling
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Double braiding is natural simultaneously in both strands. -/
theorem doubleBraiding_natural {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] {X X' Y Y' : D} (f : X ⟶ X') (g : Y ⟶ Y') :
    Modular.doubleBraiding X Y ≫ (f ⊗ₘ g) =
      (f ⊗ₘ g) ≫ Modular.doubleBraiding X' Y' := by
  unfold Modular.doubleBraiding
  rw [Category.assoc, ← BraidedCategory.braiding_naturality g f,
    ← Category.assoc, ← BraidedCategory.braiding_naturality f g, Category.assoc]

end PropertyF.Ground.CentreCabling
