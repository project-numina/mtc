module
public import MTC.Braided.Cabling.ClosureSplitMerge
public import MTC.Braided.Cabling.ClosureBlockProof
public import MTC.Braided.Cabling.ClosureImage

/-! The two-block braid generator for any positive tensor power. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Flatten two copies of a positive tensor-power block to the original strands. -/
def twoBlockFlatten (X : C) (k : ℕ) :
    tensorPower (tensorPower X (k+1)) 2 ≅ tensorPower X (k+k+2) :=
  (Iso.refl (tensorPower X (k+1)) ⊗ᵢ ρ_ (tensorPower X (k+1))) ≪≫
    (sweepBlockSplit X k k).symm

set_option backward.isDefEq.respectTransparency false in
/-- After removing the trailing unit, the two-strand generator is the
ordinary categorical self-braiding. -/
theorem twoPower_generator_conj (B : C) :
    (Iso.refl B ⊗ᵢ ρ_ B).conjAut (braidGenerator B 0 0) = Aut.of (β_ B B) := by
  apply Aut.ext
  apply Iso.ext
  change (Iso.refl B ⊗ᵢ ρ_ B).inv ≫ (braidGenerator B 0 0).asIso.hom ≫
    (Iso.refl B ⊗ᵢ ρ_ B).hom = (β_ B B).hom
  simp [braidGenerator, tensorPower, tensorIso_hom, tensorIso_inv]

set_option backward.isDefEq.respectTransparency false in
/-- The checked rectangular crossing is conjugate to self-braiding when the
blocks have equal width. -/
theorem sweepBlockCross_equal_width (X : C) (k : ℕ) :
    sweepBlockCross X k k =
      (sweepBlockSplit X k k).symm.conjAut (Aut.of (β_ (tensorPower X (k+1))
        (tensorPower X (k+1)))) := by
  have hm : sweepBlockMerge X k k = (sweepBlockSplit X k k).symm := by
    simpa [powerIndexIso] using sweepBlockMerge_eq_split X k k
  apply Aut.ext
  apply Iso.ext
  simp [sweepBlockCross, hm, Iso.conjAut_hom, Iso.conj_apply_asHom]

set_option backward.isDefEq.respectTransparency false in
/-- The two-block categorical braid generator is an explicit original-strand word. -/
theorem twoBlockFlatten_generator_word (X : C) (k : ℕ) :
    (twoBlockFlatten X k).conjAut (braidGenerator (tensorPower X (k+1)) 0 0) =
      (braidWordAction X (k+k) (blockSweepWord k k)).val := by
  calc
    _ = (sweepBlockSplit X k k).symm.conjAut
        ((Iso.refl (tensorPower X (k+1)) ⊗ᵢ ρ_ (tensorPower X (k+1))).conjAut
          (braidGenerator (tensorPower X (k+1)) 0 0)) := by
      exact Iso.trans_conjAut _ _ _
    _ = (sweepBlockSplit X k k).symm.conjAut (Aut.of (β_ (tensorPower X (k+1))
          (tensorPower X (k+1)))) := by
      exact congrArg ((sweepBlockSplit X k k).symm.conjAut)
        (twoPower_generator_conj (tensorPower X (k+1)))
    _ = _ := (sweepBlockCross_equal_width X k).symm.trans (sweepBlockCross_word X k k)

/-- Finite original braid image implies finite two-block image for every
positive tensor power. -/
theorem finite_twoBlock_image_of_power (X : C) (k : ℕ)
    [Finite (braidImage X (k+k))] : Finite (braidImage (tensorPower X (k+1)) 0) := by
  apply finite_braidImage_of_generator_words X (tensorPower X (k+1)) 0 (k+k)
    (twoBlockFlatten X k) (fun _ => blockSweepWord k k)
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact twoBlockFlatten_generator_word X k

end MTC.Braided
