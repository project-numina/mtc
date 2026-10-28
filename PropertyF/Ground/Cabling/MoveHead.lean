module
public import PropertyF.Ground.Cabling.Generated
public import PropertyF.Ground.Cabling.Strands
public import Mathlib.Tactic
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C]

/-- Move the first strand past a block of n strands, retaining the canonical
right-associated tensor power. -/
def moveHead (X : C) (n : ℕ) : Aut (tensorPower X (n+1)) := Aut.of (
  (β_ X (tensorPower X n)) ≪≫
    (Iso.refl (tensorPower X n) ⊗ᵢ (ρ_ X).symm) ≪≫ tensorPowerTensorIso X n 1)

def whiskerMoveHead (X : C) (n : ℕ) : Aut (tensorPower X (n + 2)) := by
  change Aut (X ⊗ tensorPower X (n + 1))
  exact Aut.of (Iso.refl X ⊗ᵢ (moveHead X n).asIso)

end PropertyF
