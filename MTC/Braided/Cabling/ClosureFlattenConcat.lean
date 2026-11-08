module
public import MTC.Braided.Cabling.ClosureFlattenCoherence

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

theorem iso_heq_iff_transport {A B D : C} (f : A ≅ B) (g : A ≅ D) (h : B = D) :
    f ≍ g ↔ f ≪≫ eqToIso h = g := by
  cases h
  simp

theorem blockStrandCount_sum (k p q : ℕ) :
    blockStrandCount k (strandSum p q) =
      strandSum (blockStrandCount k p) (blockStrandCount k q) := by
  simp [blockStrandCount_eq_mul, strandSum_eq_add, Nat.add_mul]

