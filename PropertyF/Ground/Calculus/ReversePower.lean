module
public import PropertyF.Ground.Calculus.StrandCoherence

/-! Cast-free recursive tensor-power concatenation. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Concatenate tensor powers, recording the total in reverse arithmetic order
so that the recursive associators need no casts. -/
def reverseConcatIso (X : C) : ∀ a b : ℕ,
    tensorPower X a ⊗ tensorPower X b ≅ tensorPower X (b + a)
  | 0, b => λ_ (tensorPower X b)
  | a + 1, b => (α_ X (tensorPower X a) (tensorPower X b)) ≪≫
      (Iso.refl X ⊗ᵢ reverseConcatIso X a b)

omit [BraidedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Associativity of the cast-free concatenation. -/
theorem reverseConcat_assoc (X : C) (a b c : ℕ) :
    ((reverseConcatIso X a b).hom ▷ tensorPower X c) ≫
      (reverseConcatIso X (b + a) c).hom =
    (α_ (tensorPower X a) (tensorPower X b) (tensorPower X c)).hom ≫
      (tensorPower X a ◁ (reverseConcatIso X b c).hom) ≫
      (reverseConcatIso X a (c + b)).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : (c + b) + a = c + (b + a))) := by
  induction a with
  | zero =>
    simp only [reverseConcatIso, tensorPower, Nat.add_zero, eqToHom_refl, Category.comp_id]
    monoidal
  | succ a ih =>
    have h : (c + b) + (a + 1) = c + (b + (a + 1)) := by omega
    have h₀ : (c + b) + a = c + (b + a) := by omega
    have hcomp : eqToHom (congrArg (tensorPower X) h) =
        X ◁ eqToHom (congrArg (tensorPower X) h₀) := by
      rw [whiskerLeft_eqToHom]
    simp only [reverseConcatIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, comp_whiskerRight, Category.assoc]
    rw [hcomp]
    rw [associator_naturality_middle_assoc, ← whiskerLeft_comp]
    change (α_ X (tensorPower X a) (tensorPower X b)).hom ▷ tensorPower X c ≫
      (α_ X (tensorPower X a ⊗ tensorPower X b) (tensorPower X c)).hom ≫
      X ◁ ((reverseConcatIso X a b).hom ▷ tensorPower X c ≫
        (reverseConcatIso X (b + a) c).hom) = _
    rw [ih]
    simp only [whiskerLeft_comp]
    monoidal

omit [BraidedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Concatenation with an empty right block is the right unitor. -/
theorem reverseConcat_zero_right (X : C) (a : ℕ) :
    (reverseConcatIso X a 0).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : 0 + a = a)) =
        (ρ_ (tensorPower X a)).hom := by
  induction a with
  | zero =>
    simp only [reverseConcatIso, tensorPower, Nat.add_zero, eqToHom_refl, Category.comp_id]
    monoidal
  | succ a ih =>
    have h₀ : 0 + a = a := by omega
    have h : 0 + (a + 1) = a + 1 := by omega
    have hcomp : eqToHom (congrArg (tensorPower X) h) =
        X ◁ eqToHom (congrArg (tensorPower X) h₀) := by
      rw [whiskerLeft_eqToHom]
    simp only [reverseConcatIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, tensorPower, Category.assoc]
    rw [hcomp, ← whiskerLeft_comp, ih]
    monoidal

omit [BraidedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Concatenating one right strand agrees with the append isomorphism. -/
theorem reverseConcat_one_right (X : C) (a : ℕ) :
    (reverseConcatIso X a 1).hom =
      (𝟙 (tensorPower X a) ⊗ₘ (ρ_ X).hom) ≫ (appendIso X a).hom ≫
        eqToHom (congrArg (tensorPower X) (by omega : a + 1 = 1 + a)) := by
  induction a with
  | zero =>
    simp only [reverseConcatIso, tensorPower, appendIso, Nat.add_zero,
      eqToHom_refl, Category.comp_id, Iso.trans_hom, Iso.symm_hom]
    monoidal
  | succ a ih =>
    have h₀ : a + 1 = 1 + a := by omega
    have h : (a + 1) + 1 = 1 + (a + 1) := by omega
    have hcomp : eqToHom (congrArg (tensorPower X) h) =
        X ◁ eqToHom (congrArg (tensorPower X) h₀) := by
      rw [whiskerLeft_eqToHom]
    simp only [reverseConcatIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, appendIso_succ]
    rw [ih, hcomp]
    simp only [whiskerLeft_comp, tensorPower]
    monoidal

end PropertyF.Ground.Calculus
