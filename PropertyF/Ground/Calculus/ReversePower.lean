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

omit [BraidedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Adding one strand to the right commutes with tensor-power concatenation. -/
theorem reverseConcat_succ_right (X : C) (a b : ℕ) :
    (reverseConcatIso X a (b + 1)).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : (b + 1) + a = (b + a) + 1)) =
    (tensorPower X a ◁ (appendIso X b).inv) ≫
      (α_ (tensorPower X a) (tensorPower X b) X).inv ≫
      ((reverseConcatIso X a b).hom ▷ X) ≫ (appendIso X (b + a)).hom := by
  induction a with
  | zero =>
    simp only [reverseConcatIso, tensorPower, Nat.add_zero, eqToHom_refl, Category.comp_id]
    have hc : (α_ (𝟙_ C) (tensorPower X b) X).inv ≫ (λ_ (tensorPower X b)).hom ▷ X =
        (λ_ (tensorPower X b ⊗ X)).hom := by monoidal
    simp only [← Category.assoc, hc, leftUnitor_naturality]
    simp [Category.assoc]
  | succ a ih =>
    have h₀ : (b + 1) + a = (b + a) + 1 := by omega
    have h : (b + 1) + (a + 1) = (b + (a + 1)) + 1 := by omega
    have hcomp : eqToHom (congrArg (tensorPower X) h) =
        X ◁ eqToHom (congrArg (tensorPower X) h₀) := by
      rw [whiskerLeft_eqToHom]
    simp only [reverseConcatIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, comp_whiskerRight, Category.assoc]
    rw [hcomp, ← whiskerLeft_comp, ih]
    have happ : appendIso X (b + (a + 1)) =
        (α_ X (tensorPower X (b + a)) X) ≪≫ (Iso.refl X ⊗ᵢ appendIso X (b + a)) :=
      appendIso_succ X (b + a)
    rw [happ]
    simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom,
      whiskerLeft_comp]
    monoidal

omit [BraidedCategory C] in
/-- Appending a strand commutes with equality transport of the prefix length. -/
theorem appendIso_eqToHom_natural (X : C) {i j : ℕ} (h : i = j) :
    (eqToHom (congrArg (tensorPower X) h) ▷ X) ≫ (appendIso X j).hom =
      (appendIso X i).hom ≫ eqToHom (congrArg (tensorPower X) (congrArg Nat.succ h)) := by
  cases h
  simp

omit [BraidedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Repeated right insertion is canonical reverse-indexed concatenation. -/
theorem insertRightPowerIso_eq_reverseConcat (X : C) (n k : ℕ) :
    (insertRightPowerIso X n k).hom = (reverseConcatIso X (n + 2) k).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : k + (n + 2) = (n + k) + 2)) := by
  induction k with
  | zero =>
    simpa only [insertRightPowerIso, Nat.add_zero] using
      (reverseConcat_zero_right X (n + 2)).symm
  | succ k ih =>
    have h₀ : k + (n + 2) = (n + k) + 2 := by omega
    have h₁ : (k + 1) + (n + 2) = (k + (n + 2)) + 1 := by omega
    have h₂ : (k + (n + 2)) + 1 = (n + (k + 1)) + 2 := by omega
    have hcomp : eqToHom (congrArg (tensorPower X)
        (by omega : (k + 1) + (n + 2) = (n + (k + 1)) + 2)) =
        eqToHom (congrArg (tensorPower X) h₁) ≫ eqToHom (congrArg (tensorPower X) h₂) := by
      rw [eqToHom_trans]
    rw [hcomp, ← Category.assoc, reverseConcat_succ_right]
    simp only [insertRightPowerIso, Iso.trans_hom, Iso.symm_hom,
      tensorIso_hom, Iso.refl_hom, tensorHom_id, id_tensorHom, Category.assoc]
    rw [ih, comp_whiskerRight]
    simp only [Category.assoc]
    rw [appendIso_eqToHom_natural X h₀]

omit [BraidedCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- A shared strand can be attached to the left block before concatenating
the right tail, or kept as the head of the right block. -/
theorem reverseConcat_overlap (X : C) (a b : ℕ) :
    (reverseConcatIso X a (b + 1)).hom =
      (α_ (tensorPower X a) X (tensorPower X b)).inv ≫
      ((appendIso X a).hom ▷ tensorPower X b) ≫
      (reverseConcatIso X (a + 1) b).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : b + (a + 1) = (b + 1) + a)) := by
  induction a with
  | zero =>
    simp only [reverseConcatIso, appendIso, tensorPower, Nat.add_zero, eqToHom_refl,
      Category.comp_id, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, comp_whiskerRight]
    monoidal
  | succ a ih =>
    have h₀ : b + (a + 1) = (b + 1) + a := by omega
    have h : b + ((a + 1) + 1) = (b + 1) + (a + 1) := by omega
    have hcomp : eqToHom (congrArg (tensorPower X) h) =
        X ◁ eqToHom (congrArg (tensorPower X) h₀) := by
      rw [whiskerLeft_eqToHom]
    simp only [reverseConcatIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, Category.assoc]
    rw [hcomp]
    rw [ih, appendIso_succ]
    simp only [reverseConcatIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    monoidal

end PropertyF.Ground.Calculus
