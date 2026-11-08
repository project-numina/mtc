module
public import MTC.Braided.Cabling.Generated

/-! Coherent flattening of powers of a tensor-power block. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]

/-- Flatten `n` consecutive blocks of `k` strands into `n*k` strands. -/
def flattenPower (X : C) (k : ℕ) : ∀ n : ℕ,
    tensorPower (tensorPower X k) n ≅ tensorPower X (n * k)
  | 0 => by simpa [tensorPower] using (Iso.refl (𝟙_ C))
  | n + 1 => by
      simpa only [tensorPower, Nat.succ_mul, Nat.add_comm] using
        ((Iso.refl (tensorPower X k) ⊗ᵢ flattenPower X k n) ≪≫
          tensorPowerTensorIso X k (n * k))

/-- Flatten the positive-width blocks used by an actual braid representation. -/
def flattenPositiveBraidPower (X : C) (k n : ℕ) :
    tensorPower (tensorPower X (k + 1)) (n + 2) ≅
      tensorPower X (((n + 2) * (k + 1) - 2) + 2) := by
  have h : 2 ≤ (n + 2) * (k + 1) := by
    nlinarith
  simpa only [Nat.sub_add_cancel h] using flattenPower X (k + 1) (n + 2)

end MTC.Braided
