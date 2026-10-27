module
public import PropertyF.Ground.Cabling.Blocks
public import PropertyF.Ground.Cabling.Pure
open CategoryTheory CategoryTheory.Limits
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]

/-- An automorphism permutes the projectors of a finite biproduct. -/
def permutesBlocks {I : Type} [Fintype I] (f : I → C)
    (a : Aut (⨁ f)) (p : Equiv.Perm I) : Prop :=
  ∀ i, (biproduct.π f i ≫ biproduct.ι f i) ≫ a.asIso.hom =
    a.asIso.hom ≫ (biproduct.π f (p i) ≫ biproduct.ι f (p i))

theorem permutesBlocks_one {I : Type} [Fintype I] (f : I → C) :
    permutesBlocks f 1 1 := by simp [permutesBlocks]

theorem permutesBlocks_mul {I : Type} [Fintype I] (f : I → C)
    {a b : Aut (⨁ f)} {p q : Equiv.Perm I}
    (ha : permutesBlocks f a p) (hb : permutesBlocks f b q) :
    permutesBlocks f (a * b) (p * q) := by
  intro i
  simp only [Aut.mul_asIso, Iso.trans_hom, Equiv.Perm.mul_apply, Category.assoc]
  calc
    _ = b.asIso.hom ≫ (biproduct.π f (q i) ≫ biproduct.ι f (q i)) ≫ a.asIso.hom := by
      simpa [Category.assoc] using congrArg (fun z => z ≫ a.asIso.hom) (hb i)
    _ = _ := by rw [ha (q i)]

theorem permutesBlocks_inv {I : Type} [Fintype I] (f : I → C)
    {a : Aut (⨁ f)} {p : Equiv.Perm I} (h : permutesBlocks f a p) :
    permutesBlocks f a⁻¹ p⁻¹ := by
  intro i
  simp only [Aut.inv_asIso, Iso.symm_hom]
  apply (cancel_epi a.asIso.hom).mp
  apply (cancel_mono a.asIso.hom).mp
  have hi := h (p⁻¹ i)
  have hp : p (p⁻¹ i) = i := Equiv.apply_symm_apply p i
  rw [hp] at hi
  simpa [Category.assoc] using hi.symm

/-- Words in generators which permute blocks continue to do so with the
corresponding word in permutations. -/
theorem braidWords_permuteBlocks {I : Type} [Fintype I] (f : I → C)
    (n : ℕ) (ρ : BraidWords n →* Aut (⨁ f)) (π : BraidWords n →* Equiv.Perm I)
    (hgen : ∀ i, permutesBlocks f (ρ (FreeGroup.of i)) (π (FreeGroup.of i))) :
    ∀ w, permutesBlocks f (ρ w) (π w) := by
  intro w
  induction w using FreeGroup.induction_on with
  | one => simpa using permutesBlocks_one f
  | of i => exact hgen i
  | inv_of i ih => simpa using permutesBlocks_inv f ih
  | mul x y ihx ihy => simpa using permutesBlocks_mul f ihx ihy

/-- An automorphism fixing every block projector preserves every summand. -/
theorem fixesBlocks_preservesSummands {I : Type} [Fintype I] (f : I → C)
    (a : Aut (⨁ f)) (h : permutesBlocks f a 1) :
    ∀ i, biproduct.ι f i ≫ a.asIso.hom =
      (biproduct.ι f i ≫ a.asIso.hom ≫ biproduct.π f i) ≫ biproduct.ι f i := by
  intro i
  have hi := h i
  simp only [Equiv.Perm.one_apply] at hi
  have := congrArg (fun z => biproduct.ι f i ≫ z) hi
  simpa [Category.assoc] using this
/-- A permutation of strands acts on tuples of block labels. -/
def tuplePermutation (I : Type) (n : ℕ) : Equiv.Perm (Fin n) →* Equiv.Perm (Fin n → I) where
  toFun p := Equiv.arrowCongr p (Equiv.refl I)
  map_one' := rfl
  map_mul' p q := by ext t i; rfl

/-- A pure word fixes each label tuple. -/
theorem pureWord_fixes_tuples (I : Type) (n : ℕ) (w : pureWords n) :
    (tuplePermutation I (n + 2)).comp (strandPermutation n) w.val = 1 := by
  have hw : strandPermutation n w.val = 1 := w.property
  simp [hw]

/-- If crossing generators permute tuple blocks according to the induced
strand permutation, every pure word preserves every block. -/
theorem pureWord_preserves_tupleBlocks {I : Type} [Fintype I] (f : (Fin (n + 2) → I) → C)
    (ρ : BraidWords n →* Aut (⨁ f))
    (hgen : ∀ i, permutesBlocks f (ρ (FreeGroup.of i))
      (((tuplePermutation I (n + 2)).comp (strandPermutation n)) (FreeGroup.of i))) :
    ∀ (w : pureWords n) i, biproduct.ι f i ≫ (ρ w.val).asIso.hom =
      (biproduct.ι f i ≫ (ρ w.val).asIso.hom ≫ biproduct.π f i) ≫ biproduct.ι f i := by
  intro w
  apply fixesBlocks_preservesSummands f
  have h := braidWords_permuteBlocks f n ρ ((tuplePermutation I (n + 2)).comp (strandPermutation n)) hgen w.val
  rw [pureWord_fixes_tuples] at h
  exact h
/-- Pure words act on each tuple block under the generator-permutation law. -/
def pureTupleBlockAction {I : Type} [Fintype I] (f : (Fin (n + 2) → I) → C)
    (ρ : BraidWords n →* Aut (⨁ f))
    (hgen : ∀ i, permutesBlocks f (ρ (FreeGroup.of i))
      (((tuplePermutation I (n + 2)).comp (strandPermutation n)) (FreeGroup.of i))) :
    pureWords n →* ∀ i, Aut (f i) :=
  blockRestrictionHom f (ρ.comp (pureWords n).subtype)
    (pureWord_preserves_tupleBlocks f ρ hgen)

/-- These pure block actions jointly detect the action on the biproduct. -/
theorem pureTupleBlockAction_ker_le {I : Type} [Fintype I] (f : (Fin (n + 2) → I) → C)
    (ρ : BraidWords n →* Aut (⨁ f))
    (hgen : ∀ i, permutesBlocks f (ρ (FreeGroup.of i))
      (((tuplePermutation I (n + 2)).comp (strandPermutation n)) (FreeGroup.of i))) :
    (pureTupleBlockAction f ρ hgen).ker ≤ (ρ.comp (pureWords n).subtype).ker :=
  blockRestriction_ker_le f (ρ.comp (pureWords n).subtype) _
end PropertyF
