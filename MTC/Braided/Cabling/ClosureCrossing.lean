module
public import MTC.Braided.Cabling.Naturality

/-! Explicit crossings of blocks of identical strands, expanded into individual
crossings and associators by the braided hexagon identities. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Move one strand through a block, using one crossing per strand. -/
def singleAcrossPower (X : C) : ∀ m : ℕ, X ⊗ tensorPower X m ≅ tensorPower X m ⊗ X
  | 0 => (ρ_ X) ≪≫ (λ_ X).symm
  | m + 1 => (α_ X X (tensorPower X m)).symm ≪≫
      whiskerRightIso (β_ X X) (tensorPower X m) ≪≫
      α_ X X (tensorPower X m) ≪≫ whiskerLeftIso X (singleAcrossPower X m) ≪≫
      (α_ X (tensorPower X m) X).symm

/-- The recursive strand-by-strand crossing is the actual braiding. -/
theorem singleAcrossPower_eq_braiding (X : C) (m : ℕ) :
    singleAcrossPower X m = β_ X (tensorPower X m) := by
  induction m with
  | zero =>
    apply Iso.ext
    simp [singleAcrossPower, tensorPower, braiding_tensorUnit_right]
  | succ m ih =>
    apply Iso.ext
    simp only [singleAcrossPower, tensorPower, Iso.trans_hom, Iso.symm_hom,
      whiskerRightIso_hom, whiskerLeftIso_hom]
    rw [ih]
    exact (braiding_tensor_right_hom X X (tensorPower X m)).symm

/-- Cross two blocks by moving each strand of the left block through the right. -/
def powerAcrossPower (X : C) (m : ℕ) : ∀ n : ℕ,
    tensorPower X n ⊗ tensorPower X m ≅ tensorPower X m ⊗ tensorPower X n
  | 0 => (λ_ (tensorPower X m)) ≪≫ (ρ_ (tensorPower X m)).symm
  | n + 1 => α_ X (tensorPower X n) (tensorPower X m) ≪≫
      whiskerLeftIso X (powerAcrossPower X m n) ≪≫
      (α_ X (tensorPower X m) (tensorPower X n)).symm ≪≫
      whiskerRightIso (singleAcrossPower X m) (tensorPower X n) ≪≫
      α_ (tensorPower X m) X (tensorPower X n)

/-- The explicit block crossing is the actual categorical braiding. -/
theorem powerAcrossPower_eq_braiding (X : C) (m n : ℕ) :
    powerAcrossPower X m n = β_ (tensorPower X n) (tensorPower X m) := by
  induction n with
  | zero =>
    apply Iso.ext
    simp [powerAcrossPower, tensorPower, braiding_tensorUnit_left]
  | succ n ih =>
    apply Iso.ext
    simp only [powerAcrossPower, tensorPower, Iso.trans_hom, Iso.symm_hom,
      whiskerRightIso_hom, whiskerLeftIso_hom]
    rw [ih, singleAcrossPower_eq_braiding]
    exact (braiding_tensor_left_hom X (tensorPower X n) (tensorPower X m)).symm

end MTC.Braided
