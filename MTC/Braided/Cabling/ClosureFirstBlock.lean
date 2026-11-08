module
public import MTC.Braided.Cabling.ClosureBlockContext
public import MTC.Braided.Cabling.ClosureTwoBlockPower
public import MTC.Braided.Cabling.ClosureFlatten

/-! A flattening adapted to the first crossing of equal tensor-power blocks. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- Flatten the first two blocks together and all remaining blocks as a tail. -/
def firstBlockFlatten (X : C) (k n : ℕ) :
    tensorPower (tensorPower X (k+1)) (n+2) ≅
      tensorPower X (((n+2)*(k+1)-2)+2) :=
  powerIndexIso (tensorPower X (k+1)) (by omega : n+2 = 0+n+2) ≪≫
    (Trace.insertRightPowerIso (tensorPower X (k+1)) 0 n).symm ≪≫
    (twoBlockFlatten X k ⊗ᵢ flattenPower X (k+1) n) ≪≫
    Trace.insertRightPowerIso X (k+k) (n*(k+1)) ≪≫
    powerIndexIso X (by
      have h := blockGenerator_index k n 0
      simp only [Fin.val_zero, Nat.zero_mul, Nat.sub_zero, Nat.add_zero] at h
      omega : ((k+k)+(n*(k+1)))+2 = ((n+2)*(k+1)-2)+2)

/-- The image element for the first adjacent generator. -/
def firstGeneratorImage (X : C) (n : ℕ) : braidImage X n :=
  ⟨braidGenerator X n 0, Subgroup.subset_closure ⟨0, rfl⟩⟩

omit [Abelian C] in
/-- Adding identity strands on the right preserves the first generator. -/
theorem addRightStrands_firstGenerator (X : C) : ∀ n : ℕ,
    Trace.addRightStrands X 0 n (firstGeneratorImage X 0) = firstGeneratorImage X (0+n)
  | 0 => rfl
  | n+1 => by
    change Trace.addRightStrand X (0+n) (Trace.addRightStrands X 0 n (firstGeneratorImage X 0)) = _
    rw [addRightStrands_firstGenerator X n]
    apply Subtype.ext
    change Trace.addRightAut X (0+n) (braidGenerator X (0+n) 0) = braidGenerator X (0+n+1) 0
    have h := Trace.addRightAut_generator X (0 : Fin (0+n+1))
    simpa only [Fin.castSucc_zero] using h

end MTC.Braided
