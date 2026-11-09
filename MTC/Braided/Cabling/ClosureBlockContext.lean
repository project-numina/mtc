module
public import MTC.Braided.Cabling.ClosureBlockProof
public import MTC.Braided.Cabling.ClosureMergeCommon

/-! Local rectangular block crossings inside a larger braid image. -/

@[expose] public noncomputable section
open CategoryTheory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Any positive rectangular block crossing, with arbitrary preceding and
following identity strands, is the action of an explicit adjacent braid word. -/
theorem blockSweepWord_action_with_surrounding (X : C) (s r p t : ℕ) :
    braidWordAction X (((s+r)+t)+p)
      (insertLeftWords ((s+r)+t) p (insertRightWords (s+r) t (blockSweepWord s r))) =
      Trace.addLeftStrands X ((s+r)+t) p
        (Trace.addRightStrands X (s+r) t (blockSweepImage X s r)) := by
  rw [braidWordAction_insertLeftWords, braidWordAction_insertRightWords,
    blockSweepWord_action]

/-- The number of original-strand generators after surrounding an equal-width
block crossing with its prefix and suffix of full blocks. -/
theorem blockGenerator_index (k n : ℕ) (i : Fin (n+1)) :
    (((k+k)+(n-i.val)*(k+1))+i.val*(k+1)) = (n+2)*(k+1)-2 := by
  have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  have hsub : (n-i.val)*(k+1) + i.val*(k+1) = n*(k+1) := by
    rw [← Nat.add_mul, Nat.sub_add_cancel hi]
  have htotal_expr : (n+2)*(k+1) = n*(k+1)+2*k+2 := by ring
  have htotal : 2 ≤ (n+2)*(k+1) := by nlinarith
  omega

/-- Explicit original-strand word for the i-th adjacent crossing of equal
positive-width blocks, including all preceding and following full blocks. -/
def blockGeneratorWord (k n : ℕ) (i : Fin (n+1)) :
    BraidWords ((n+2)*(k+1)-2) :=
  cast (congrArg BraidWords (blockGenerator_index k n i))
    (insertLeftWords ((k+k)+(n-i.val)*(k+1)) (i.val*(k+1))
      (insertRightWords (k+k) ((n-i.val)*(k+1)) (blockSweepWord k k)))

/-- Transporting a word's strand index transports its actual action along the
same canonical tensor-power isomorphism. -/
theorem braidWordAction_cast (X : C) {a b : ℕ} (h : a = b) (w : BraidWords a) :
    (braidWordAction X b (cast (congrArg BraidWords h) w)).val =
      (powerIndexIso X (congrArg (fun n => n+2) h)).conjAut (braidWordAction X a w).val := by
  subst b
  apply Aut.ext
  apply Iso.ext
  simp [powerIndexIso, Iso.conjAut_hom]

/-- Each candidate generator word acts as the actual local block crossing,
shifted to its position and transported to the common original-strand count. -/
theorem blockGeneratorWord_action (X : C) (k n : ℕ) (i : Fin (n+1)) :
    (braidWordAction X ((n+2)*(k+1)-2) (blockGeneratorWord k n i)).val =
      (powerIndexIso X (congrArg (fun q => q+2) (blockGenerator_index k n i))).conjAut
        ((Trace.addLeftStrands X ((k+k)+(n-i.val)*(k+1)) (i.val*(k+1))
          (Trace.addRightStrands X (k+k) ((n-i.val)*(k+1)) (blockSweepImage X k k))).val) := by
  unfold blockGeneratorWord
  rw [braidWordAction_cast X (blockGenerator_index k n i)]
  congr 1
  exact congrArg Subtype.val (blockSweepWord_action_with_surrounding X k k
    (i.val*(k+1)) ((n-i.val)*(k+1)))

end MTC.Braided
