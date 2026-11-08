module
public import MTC.Braided.Cabling.ClosureColoredFlatten
public import MTC.Braided.Cabling.PureSumColored

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- The heterogeneous tuple is the actual colored tensor of these powers. -/
theorem coloredTensor_powers_eq (X : C) : ∀ (n : ℕ) (k : Fin n → ℕ),
    Cabling.coloredTensor n (fun i => tensorPower X (k i)) = heterogeneousPowerTensor X n k
  | 0, _ => rfl
  | n+1, k => by
    simp only [Cabling.coloredTensor, heterogeneousPowerTensor]
    rw [coloredTensor_powers_eq X n (fun i => k i.succ)]

/-- Canonical flattening for the actual colored tensor of heterogeneous powers. -/
def coloredTensorPowersFlatten (X : C) (n : ℕ) (k : Fin n → ℕ) :
    Cabling.coloredTensor n (fun i => tensorPower X (k i)) ≅
      tensorPower X (∑ i, k i) :=
  eqToIso (coloredTensor_powers_eq X n k) ≪≫ heterogeneousPowerFlattenSum X n k
