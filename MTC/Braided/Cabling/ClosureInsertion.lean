module
public import MTC.Braided.Cabling.Naturality
public import MTC.Braided.Cabling.Strands
public import MTC.Braided.Trace.RightStrand

/-! Word-level identity-strand insertions and their categorical actions. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Insert one identity strand on the left of a word. -/
def insertLeftWord (n : ℕ) : BraidWords n →* BraidWords (n + 1) :=
  FreeGroup.map Fin.succ

/-- Insert one identity strand on the right of a word. -/
def insertRightWord (n : ℕ) : BraidWords n →* BraidWords (n + 1) :=
  FreeGroup.map Fin.castSucc

/-- The word-level left insertion is the actual categorical left insertion. -/
theorem braidWordAction_insertLeft (X : C) (n : ℕ) (w : BraidWords n) :
    braidWordAction X (n + 1) (insertLeftWord n w) =
      addLeftStrand X n (braidWordAction X n w) := by
  have h : (braidWordAction X (n + 1)).comp (insertLeftWord n) =
      (addLeftStrand X n).comp (braidWordAction X n) := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, insertLeftWord, FreeGroup.map.of, braidWordAction,
      MonoidHom.codRestrict_apply, FreeGroup.lift_apply_of]
    apply Subtype.ext
    apply Aut.ext
    apply Iso.ext
    rcases i with ⟨i, hi⟩
    change (braidGenerator X (n + 1) ⟨i+1, Nat.succ_lt_succ hi⟩).asIso.hom = X ◁ (braidGenerator X n ⟨i, hi⟩).asIso.hom
    simp [braidGenerator, tensorIso_hom, id_tensorHom]
    rfl
  exact DFunLike.congr_fun h w

/-- The word-level right insertion is the actual categorical right insertion. -/
theorem braidWordAction_insertRight (X : C) (n : ℕ) (w : BraidWords n) :
    braidWordAction X (n + 1) (insertRightWord n w) =
      Trace.addRightStrand X n (braidWordAction X n w) := by
  have h : (braidWordAction X (n + 1)).comp (insertRightWord n) =
      (Trace.addRightStrand X n).comp (braidWordAction X n) := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, insertRightWord, FreeGroup.map.of, braidWordAction,
      MonoidHom.codRestrict_apply, FreeGroup.lift_apply_of]
    apply Subtype.ext
    change braidGenerator X (n + 1) i.castSucc = Trace.addRightAut X n (braidGenerator X n i)
    exact (Trace.addRightAut_generator X i).symm
  exact DFunLike.congr_fun h w

/-- Add any number of identity strands to the left of a word. -/
def insertLeftWords (n : ℕ) : ∀ k, BraidWords n →* BraidWords (n + k)
  | 0 => MonoidHom.id _
  | k + 1 => (insertLeftWord (n + k)).comp (insertLeftWords n k)

/-- Add any number of identity strands to the right of a word. -/
def insertRightWords (n : ℕ) : ∀ k, BraidWords n →* BraidWords (n + k)
  | 0 => MonoidHom.id _
  | k + 1 => (insertRightWord (n + k)).comp (insertRightWords n k)

/-- Iterated word insertion agrees with actual left strand insertion. -/
theorem braidWordAction_insertLeftWords (X : C) (n k : ℕ) (w : BraidWords n) :
    braidWordAction X (n + k) (insertLeftWords n k w) =
      Trace.addLeftStrands X n k (braidWordAction X n w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change braidWordAction X (n + k + 1) (insertLeftWord (n+k) (insertLeftWords n k w)) =
      addLeftStrand X (n+k) (Trace.addLeftStrands X n k (braidWordAction X n w))
    rw [braidWordAction_insertLeft, ih]

/-- Iterated word insertion agrees with actual right strand insertion. -/
theorem braidWordAction_insertRightWords (X : C) (n k : ℕ) (w : BraidWords n) :
    braidWordAction X (n + k) (insertRightWords n k w) =
      Trace.addRightStrands X n k (braidWordAction X n w) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change braidWordAction X (n + k + 1) (insertRightWord (n+k) (insertRightWords n k w)) =
      Trace.addRightStrand X (n+k) (Trace.addRightStrands X n k (braidWordAction X n w))
    rw [braidWordAction_insertRight, ih]

end MTC.Braided
