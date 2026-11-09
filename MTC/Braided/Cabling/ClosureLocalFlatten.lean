module
public import MTC.Braided.Cabling.ClosureLeftInsertion

/-! Position-adapted flattenings for all equal-width block generators. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- Flatten a prefix of `p` full blocks, the next two crossing blocks, and
then a suffix of `q` full blocks. -/
def localBlockFlatten (X : C) (k p q : ℕ) :
    tensorPower (tensorPower X (k+1)) ((0+q)+p+2) ≅
      tensorPower X (((k+k)+(q*(k+1)))+(p*(k+1))+2) :=
  (Trace.insertLeftPowerIso (tensorPower X (k+1)) (0+q) p).symm ≪≫
    (flattenPower X (k+1) p ⊗ᵢ firstBlockFlattenIndexed X k q) ≪≫
      Trace.insertLeftPowerIso X ((k+k)+(q*(k+1))) (p*(k+1))

set_option backward.isDefEq.respectTransparency false in
/-- Under the position-adapted flattening, the actual local block generator is
the corresponding actual original-strand block crossing with prefix and tail. -/
theorem localBlockFlatten_generator (X : C) (k p q : ℕ) :
    (localBlockFlatten X k p q).conjAut
      (Trace.addLeftStrands (tensorPower X (k+1)) (0+q) p
        (firstGeneratorImage (tensorPower X (k+1)) (0+q))).val =
      (Trace.addLeftStrands X ((k+k)+(q*(k+1))) (p*(k+1))
        (Trace.addRightStrands X (k+k) (q*(k+1)) (blockSweepImage X k k))).val := by
  simp only [localBlockFlatten, Iso.trans_conjAut]
  rw [leftInsertion_inverse_conjAut, tensor_conj_left]
  change (Trace.insertLeftPowerIso X ((k+k)+(q*(k+1))) (p*(k+1))).conjAut
      ((tensorLeft (tensorPower X (p*(k+1)))).mapAut _
        ((firstBlockFlattenIndexed X k q).conjAut
          (braidGenerator (tensorPower X (k+1)) (0+q) 0))) = _
  rw [firstBlockFlattenIndexed_generator, leftInsertion_conjAut]

/-- The adjacent-generator index after inserting `p` strands on the left. -/
def shiftedFirstIndex (n p : ℕ) : Fin (n+p+1) := ⟨p, by omega⟩

/-- Left insertion of the first generator is the actual generator at the
correspondingly shifted position. -/
theorem addLeftStrands_firstGenerator (X : C) (n : ℕ) : ∀ p : ℕ,
    (Trace.addLeftStrands X n p (firstGeneratorImage X n)).val =
      braidGenerator X (n+p) (shiftedFirstIndex n p)
  | 0 => by
    have h : shiftedFirstIndex n 0 = 0 := by ext; rfl
    simp [Trace.addLeftStrands, firstGeneratorImage, h]
  | p+1 => by
    change ((addLeftStrand X (n+p))
      (Trace.addLeftStrands X n p (firstGeneratorImage X n))).val = _
    have ih := addLeftStrands_firstGenerator X n p
    have hs : (shiftedFirstIndex n p).succ = shiftedFirstIndex n (p+1) := by
      apply Fin.ext
      rfl
    rw [← hs]
    change (tensorLeft X).mapAut (tensorPower X ((n+p)+2))
      (Trace.addLeftStrands X n p (firstGeneratorImage X n)).val = _
    rw [ih]
    exact MTC.Center.Trace.braidGenerator_succ X _

/-- Every adjacent block generator has a concrete position-adapted flattening
under which it is a padded original-strand block crossing. -/
theorem localBlockFlatten_adjacent (X : C) (k p q : ℕ) :
    (localBlockFlatten X k p q).conjAut
      (braidGenerator (tensorPower X (k+1)) ((0+q)+p) (shiftedFirstIndex (0+q) p)) =
      (Trace.addLeftStrands X ((k+k)+(q*(k+1))) (p*(k+1))
        (Trace.addRightStrands X (k+k) (q*(k+1)) (blockSweepImage X k k))).val := by
  have h := localBlockFlatten_generator X k p q
  rw [addLeftStrands_firstGenerator] at h
  exact h

end MTC.Braided
