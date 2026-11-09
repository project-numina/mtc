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

omit [BraidedCategory C] [Abelian C] in
set_option backward.isDefEq.respectTransparency false in
/-- Conjugating an operator and an independent identity factor by tensor
isomorphisms transports only the operator. -/
theorem tensor_conj_right {A B D E : C} (e : A ≅ B) (f : D ≅ E) (a : Aut A) :
    (e ⊗ᵢ f).conjAut ((tensorRight D).mapAut A a) =
      (tensorRight E).mapAut B (e.conjAut a) := by
  apply Aut.ext
  apply Iso.ext
  change (e ⊗ᵢ f).inv ≫ (a.asIso.hom ▷ D) ≫ (e ⊗ᵢ f).hom =
    (e.inv ≫ a.asIso.hom ≫ e.hom) ▷ E
  simp only [tensorIso_inv, tensorIso_hom, ← Category.assoc, tensorHom_def,
    whisker_exchange_assoc, comp_whiskerRight, Category.assoc]
  simp

omit [Abelian C] in
/-- The conjugated action on an operator with an identity tail is exactly
its actual iterated right-strand insertion. -/
theorem rightInsertion_conjAut (X : C) (n t : ℕ) (a : braidImage X n) :
    (Trace.insertRightPowerIso X n t).conjAut
      ((tensorRight (tensorPower X t)).mapAut (tensorPower X (n+2)) a.val) =
        (Trace.addRightStrands X n t a).val := by
  apply Aut.ext
  apply Iso.ext
  change (Trace.insertRightPowerIso X n t).inv ≫
      (a.val.asIso.hom ▷ tensorPower X t) ≫ (Trace.insertRightPowerIso X n t).hom = _
  exact (addRightStrands_asHom X n t a).symm

omit [BraidedCategory C] [Abelian C] in
/-- Conjugation by an isomorphism and its inverse cancel on automorphisms. -/
theorem conjAut_symm_cancel {A B : C} (e : A ≅ B) (a : Aut A) :
    e.symm.conjAut (e.conjAut a) = a := by
  apply Aut.ext
  apply Iso.ext
  simp [Iso.conjAut_hom, Iso.conj_apply_asHom]

omit [Abelian C] in
/-- Recover the local operator and its identity tail from an inserted braid. -/
theorem rightInsertion_inverse_conjAut (X : C) (n t : ℕ) (a : braidImage X n) :
    (Trace.insertRightPowerIso X n t).symm.conjAut (Trace.addRightStrands X n t a).val =
      (tensorRight (tensorPower X t)).mapAut (tensorPower X (n+2)) a.val := by
  rw [← rightInsertion_conjAut, conjAut_symm_cancel]

/-- The same first-crossing flattening in insertion-native indices, avoiding
arithmetic transports in the categorical conjugacy calculation. -/
def firstBlockFlattenIndexed (X : C) (k n : ℕ) :
    tensorPower (tensorPower X (k+1)) (0+n+2) ≅
      tensorPower X ((k+k)+(n*(k+1))+2) :=
  (Trace.insertRightPowerIso (tensorPower X (k+1)) 0 n).symm ≪≫
    (twoBlockFlatten X k ⊗ᵢ flattenPower X (k+1) n) ≪≫
      Trace.insertRightPowerIso X (k+k) (n*(k+1))

set_option backward.isDefEq.respectTransparency false in
/-- Under the first-crossing flattening, generator zero becomes the actual
original-strand block crossing with a tail of identity strands. -/
theorem firstBlockFlattenIndexed_generator (X : C) (k n : ℕ) :
    (firstBlockFlattenIndexed X k n).conjAut
        (braidGenerator (tensorPower X (k+1)) (0+n) 0) =
      (Trace.addRightStrands X (k+k) (n*(k+1)) (blockSweepImage X k k)).val := by
  have hg := congrArg Subtype.val (addRightStrands_firstGenerator (tensorPower X (k+1)) n)
  change (Trace.addRightStrands (tensorPower X (k+1)) 0 n
    (firstGeneratorImage (tensorPower X (k+1)) 0)).val =
      braidGenerator (tensorPower X (k+1)) (0+n) 0 at hg
  rw [← hg]
  simp only [firstBlockFlattenIndexed, Iso.trans_conjAut]
  rw [rightInsertion_inverse_conjAut, tensor_conj_right]
  change (Trace.insertRightPowerIso X (k+k) (n*(k+1))).conjAut
      ((tensorRight (tensorPower X (n*(k+1)))).mapAut _
        ((twoBlockFlatten X k).conjAut (braidGenerator (tensorPower X (k+1)) 0 0))) = _
  rw [twoBlockFlatten_generator_word, blockSweepWord_action, rightInsertion_conjAut]

end MTC.Braided
