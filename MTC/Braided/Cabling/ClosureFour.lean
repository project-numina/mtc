module
public import MTC.Braided.Cabling.ClosureBlockWord
public import MTC.Braided.Cabling.ClosureImage
public import Mathlib.Tactic

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- First crossing among four right-associated tensor factors. -/
def fourCrossing0 (X : C) : End (X ⊗ (X ⊗ (X ⊗ X))) :=
  End.of ((α_ X X (X ⊗ X)).inv ≫ ((β_ X X).hom ▷ (X ⊗ X)) ≫
    (α_ X X (X ⊗ X)).hom)

/-- Second crossing among four right-associated tensor factors. -/
def fourCrossing1 (X : C) : End (X ⊗ (X ⊗ (X ⊗ X))) :=
  End.of (X ◁ ((α_ X X X).inv ≫ ((β_ X X).hom ▷ X) ≫ (α_ X X X).hom))

/-- Third crossing among four right-associated tensor factors. -/
def fourCrossing2 (X : C) : End (X ⊗ (X ⊗ (X ⊗ X))) :=
  End.of (X ◁ X ◁ (β_ X X).hom)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- The self-braiding of a pair is its four elementary adjacent crossings. -/
theorem fourBlock_crossing (X : C) :
    ((α_ X X (X ⊗ X)).conj (End.of (β_ (X ⊗ X) (X ⊗ X)).hom)) =
      fourCrossing1 X * fourCrossing0 X * (fourCrossing2 X * fourCrossing1 X) := by
  apply End.ext
  simp only [Iso.conj_apply_asHom, End.mul_asHom, fourCrossing0,
    fourCrossing1, fourCrossing2]
  rw [braiding_tensor_left_hom]
  simp only [braiding_tensor_right_hom, comp_whiskerRight, whiskerLeft_comp]
  monoidal

/-- Remove the trailing tensor unit from four strands. -/
def fourPowerIso (X : C) : tensorPower X 4 ≅ X ⊗ (X ⊗ (X ⊗ X)) :=
  Iso.refl X ⊗ᵢ (Iso.refl X ⊗ᵢ (Iso.refl X ⊗ᵢ ρ_ X))

set_option backward.isDefEq.respectTransparency false in
/-- The first categorical generator is the first ordinary crossing. -/
theorem fourGenerator0_transport (X : C) :
    ((fourPowerIso X).conj (Aut.toEnd (braidGenerator X 2 0))) = fourCrossing0 X := by
  apply End.ext
  simp [fourPowerIso, fourCrossing0, braidGenerator, tensorPower, Iso.conj_apply_asHom]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The second categorical generator is the second ordinary crossing. -/
theorem fourGenerator1_transport (X : C) :
    ((fourPowerIso X).conj (Aut.toEnd (braidGenerator X 2 1))) = fourCrossing1 X := by
  apply End.ext
  simp [fourPowerIso, fourCrossing1, braidGenerator, tensorPower, Iso.conj_apply_asHom]
  monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The third categorical generator is the third ordinary crossing. -/
theorem fourGenerator2_transport (X : C) :
    ((fourPowerIso X).conj (Aut.toEnd (braidGenerator X 2 2))) = fourCrossing2 X := by
  apply End.ext
  simp [fourPowerIso, fourCrossing2, braidGenerator, tensorPower, Iso.conj_apply_asHom]

/-- Remove the trailing unit from a pair of strands. -/
def pairPowerIso (X : C) : tensorPower X 2 ≅ X ⊗ X :=
  Iso.refl X ⊗ᵢ ρ_ X

/-- Normalize two blocks of two strands to the ordinary pair of pairs. -/
def pairBlockIso (X : C) : tensorPower (tensorPower X 2) 2 ≅ (X ⊗ X) ⊗ (X ⊗ X) :=
  (Iso.refl (tensorPower X 2) ⊗ᵢ ρ_ (tensorPower X 2)) ≪≫
    (pairPowerIso X ⊗ᵢ pairPowerIso X)

set_option backward.isDefEq.respectTransparency false in
/-- The two-block categorical generator is the ordinary block braiding. -/
theorem pairBlockIso_generator (X : C) :
    (pairBlockIso X).conj (Aut.toEnd (braidGenerator (tensorPower X 2) 0 0)) =
      End.of (β_ (X ⊗ X) (X ⊗ X)).hom := by
  let B := tensorPower X 2
  let e : B ⊗ B ≅ (X ⊗ X) ⊗ (X ⊗ X) := pairPowerIso X ⊗ᵢ pairPowerIso X
  have hB : (Iso.refl B ⊗ᵢ ρ_ B).conj (Aut.toEnd (braidGenerator B 0 0)) =
      End.of (β_ B B).hom := by
    apply End.ext
    simp [Iso.conj_apply_asHom, braidGenerator, tensorPower, tensorIso_hom, tensorIso_inv]
  change ((Iso.refl B ⊗ᵢ ρ_ B) ≪≫ e).conj _ = _
  rw [Iso.trans_conj]
  change e.conj ((Iso.refl B ⊗ᵢ ρ_ B).conj (Aut.toEnd (braidGenerator B 0 0))) = _
  rw [hB]
  apply End.ext
  change e.inv ≫ (β_ B B).hom ≫ e.hom = _
  have hn := braiding_naturality (pairPowerIso X).hom (pairPowerIso X).hom
  change e.hom ≫ (β_ (X ⊗ X) (X ⊗ X)).hom = (β_ B B).hom ≫ e.hom at hn
  rw [← hn]
  simp

/-- Flatten two two-strand blocks into four strands. -/
def fourBlockFlatten (X : C) : tensorPower (tensorPower X 2) 2 ≅ tensorPower X 4 :=
  pairBlockIso X ≪≫ α_ X X (X ⊗ X) ≪≫ (fourPowerIso X).symm

set_option backward.isDefEq.respectTransparency false in
/-- The width-two block crossing is the explicit four-strand braid word. -/
theorem fourBlock_word (X : C) :
    (fourBlockFlatten X).conjAut (braidGenerator (tensorPower X 2) 0 0) =
      (braidWordAction X 2 (blockCrossingWord 1 0)).val := by
  apply (fourPowerIso X).conjAut.injective
  apply Aut.ext
  apply Iso.ext
  rw [Iso.conjAut_hom]
  change ((fourPowerIso X).conj (Aut.toEnd ((fourBlockFlatten X).conjAut
    (braidGenerator (tensorPower X 2) 0 0)))).asHom = _
  have hleft : (fourPowerIso X).conj (Aut.toEnd ((fourBlockFlatten X).conjAut
      (braidGenerator (tensorPower X 2) 0 0))) =
      (α_ X X (X ⊗ X)).conj (End.of (β_ (X ⊗ X) (X ⊗ X)).hom) := by
    have hconj {A B : C} (e : A ≅ B) (f : Aut A) :
        Aut.toEnd (e.conjAut f) = e.conj (Aut.toEnd f) := by
      apply End.ext
      exact Iso.conjAut_hom e f
    rw [hconj]
    simp only [fourBlockFlatten, Iso.trans_conj, Iso.self_symm_conj, pairBlockIso_generator]
  rw [hleft, fourBlock_crossing]
  rw [Iso.conjAut_hom]
  simp only [blockCrossingWord_one_zero, braidWordAction, MonoidHom.codRestrict_apply,
    map_mul, FreeGroup.lift_apply_of]
  change (fourCrossing1 X * fourCrossing0 X * (fourCrossing2 X * fourCrossing1 X)).asHom =
    ((fourPowerIso X).conj (Aut.toEnd ((braidGenerator X 2 1 * braidGenerator X 2 0) *
      (braidGenerator X 2 2 * braidGenerator X 2 1)))).asHom
  simp only [map_mul]
  change _ = ((fourPowerIso X).conj (Aut.toEnd (braidGenerator X 2 1)) *
    (fourPowerIso X).conj (Aut.toEnd (braidGenerator X 2 0)) *
    ((fourPowerIso X).conj (Aut.toEnd (braidGenerator X 2 2)) *
      (fourPowerIso X).conj (Aut.toEnd (braidGenerator X 2 1)))).asHom
  rw [fourGenerator0_transport, fourGenerator1_transport, fourGenerator2_transport]

/-- Finite four-strand image for `X` gives finite two-block image for `X²`. -/
theorem finite_twoBlock_image_of_four (X : C) [Finite (braidImage X 2)] :
    Finite (braidImage (tensorPower X 2) 0) := by
  apply finite_braidImage_of_generator_words X (tensorPower X 2) 0 2
    (fourBlockFlatten X) (fun _ => blockCrossingWord 1 0)
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact fourBlock_word X

end MTC.Braided

end

/-! Appending arbitrarily many original strands to the checked four-strand
block crossing, with an explicit word and actual categorical action. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The width-two block crossing as an element of the actual four-strand image. -/
def fourBlockImage (X : C) : braidImage X 2 :=
  ⟨(fourBlockFlatten X).conjAut (braidGenerator (tensorPower X 2) 0 0), by
    rw [fourBlock_word]
    exact (braidWordAction X 2 (blockCrossingWord 1 0)).property⟩

/-- The checked block crossing with any number of identity strands appended
is represented by the explicit adjacent-strand word with those strands appended. -/
theorem fourBlock_word_with_tail (X : C) (t : ℕ) :
    braidWordAction X (2+t) (insertRightWords 2 t (blockCrossingWord 1 0)) =
      Trace.addRightStrands X 2 t (fourBlockImage X) := by
  rw [braidWordAction_insertRightWords]
  congr 1
  apply Subtype.ext
  exact (fourBlock_word X).symm

/-- The same crossing, with arbitrary numbers of identity strands before and
behind it, is evaluated by the explicitly shifted and padded braid word. -/
theorem fourBlock_word_with_surrounding (X : C) (p t : ℕ) :
    braidWordAction X ((2+t)+p)
      (insertLeftWords (2+t) p (insertRightWords 2 t (blockCrossingWord 1 0))) =
      Trace.addLeftStrands X (2+t) p (Trace.addRightStrands X 2 t (fourBlockImage X)) := by
  rw [braidWordAction_insertLeftWords, fourBlock_word_with_tail]

end MTC.Braided
