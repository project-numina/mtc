module
public import PropertyF.Ground.Cabling.Generated
public import PropertyF.Ground.Cabling.Strands
public import PropertyF.Ground.Calculus.OverlapCoherence
public import Mathlib.Tactic

open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Dimensions

@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C]

theorem castIso_hom_comp {A B D : C} (h : B = D) (e : A ≅ D) :
    (cast (congrArg (fun Z : C => A ≅ Z) h.symm) e).hom ≫ eqToHom h = e.hom := by
  cases h
  simp

variable [MonoidalCategory C] [BraidedCategory C] [Abelian C] [MonoidalPreadditive C]

omit [BraidedCategory C] [Abelian C] [MonoidalPreadditive C] in
/-- Expand the standard tensor-power comparison one factor on the left. -/
theorem powerTensor_succ_general (X : C) (n m : ℕ) :
    (tensorPowerTensorIso X (n+1) m).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : (n+1)+m = (n+m)+1)) =
    ((α_ X (tensorPower X n) (tensorPower X m)) ≪≫
      (Iso.refl X ⊗ᵢ tensorPowerTensorIso X n m)).hom := by
  have h : tensorPower X ((n+1)+m) = X ⊗ tensorPower X (n+m) := by
    change tensorPower X ((n+1)+m) = tensorPower X ((n+m)+1)
    congr 1
    omega
  let e := (α_ X (tensorPower X n) (tensorPower X m)) ≪≫
    (Iso.refl X ⊗ᵢ tensorPowerTensorIso X n m)
  change (cast (congrArg (fun Z : C => ((X ⊗ tensorPower X n) ⊗ tensorPower X m) ≅ Z) h.symm) e).hom ≫ eqToHom h = e.hom
  exact castIso_hom_comp h e
end PropertyF

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

/-! Coherence of the canonical tensor-power concatenation isomorphisms. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

omit [BraidedCategory C] [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- Repeated left insertion agrees with canonical concatenation, up to the
arithmetic equality of strand counts. -/
theorem insertLeftPowerIso_eq_concat (X : C) (n k : ℕ) :
    (insertLeftPowerIso X n k).hom =
      (tensorPowerTensorIso X k (n + 2)).hom ≫
        eqToHom (congrArg (tensorPower X) (by omega : k + (n + 2) = (n + k) + 2)) := by
  induction k with
  | zero =>
    change (λ_ (tensorPower X (n + 2))).hom = _
    symm
    apply castIso_hom_comp
  | succ k ih =>
    have h₁ : (k + 1) + (n + 2) = (k + (n + 2)) + 1 := by omega
    have h₂ : k + (n + 2) = (n + k) + 2 := by omega
    have hcomp :
        eqToHom (congrArg (tensorPower X) (by omega : (k + 1) + (n + 2) = (n + (k + 1)) + 2)) =
        eqToHom (congrArg (tensorPower X) h₁) ≫
          (X ◁ eqToHom (congrArg (tensorPower X) h₂)) := by
      rw [whiskerLeft_eqToHom, eqToHom_trans]
    rw [hcomp, ← Category.assoc, powerTensor_succ_general]
    simp only [insertLeftPowerIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom]
    rw [ih, whiskerLeft_comp, Category.assoc]

omit [BraidedCategory C] [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- Cast-free reverse concatenation agrees with the standard tensor-power
concatenation up to the commutativity of the length indices. -/
theorem reverseConcat_eq_concat (X : C) (a b : ℕ) :
    (reverseConcatIso X a b).hom =
      (tensorPowerTensorIso X a b).hom ≫
        eqToHom (congrArg (tensorPower X) (by omega : a + b = b + a)) := by
  induction a with
  | zero =>
    change (λ_ (tensorPower X b)).hom = _
    symm
    apply castIso_hom_comp
  | succ a ih =>
    have h₁ : (a + 1) + b = (a + b) + 1 := by omega
    have h₂ : a + b = b + a := by omega
    have hcomp :
        eqToHom (congrArg (tensorPower X) (by omega : (a + 1) + b = b + (a + 1))) =
        eqToHom (congrArg (tensorPower X) h₁) ≫
          (X ◁ eqToHom (congrArg (tensorPower X) h₂)) := by
      rw [whiskerLeft_eqToHom, eqToHom_trans]
    rw [hcomp, ← Category.assoc, powerTensor_succ_general]
    simp only [reverseConcatIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom]
    rw [ih, whiskerLeft_comp, Category.assoc]

omit [BraidedCategory C] [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- Repeated left insertion agrees with reverse-indexed concatenation. -/
theorem insertLeftPowerIso_eq_reverseConcat (X : C) (n k : ℕ) :
    (insertLeftPowerIso X n k).hom = (reverseConcatIso X k (n + 2)).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : (n + 2) + k = (n + k) + 2)) := by
  rw [insertLeftPowerIso_eq_concat, reverseConcat_eq_concat, Category.assoc, eqToHom_trans]

omit [BraidedCategory C] [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- Concatenation is natural under equality transport of the left length. -/
@[reassoc] theorem reverseConcat_eqToHom_left (X : C) {a b : ℕ} (h : a = b) (c : ℕ) :
    (eqToHom (congrArg (tensorPower X) h) ▷ tensorPower X c) ≫
      (reverseConcatIso X b c).hom =
    (reverseConcatIso X a c).hom ≫
      eqToHom (congrArg (tensorPower X) (congrArg (fun n => c + n) h)) := by
  cases h
  simp

omit [BraidedCategory C] [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- The two canonical overlap isomorphisms agree. -/
theorem freshOverlapIso_eq_overlapPowerIso (X : C) (t k : ℕ) :
    freshOverlapIso X t k =
      (α_ (tensorPower X (overlapIndex t k + 1)) X (tensorPower X (t + 1))).symm ≪≫
        overlapPowerIso X t k := by
  apply Iso.ext
  simp only [freshOverlapIso, overlapPowerIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Iso.refl_hom, tensorHom_id]
  rw [insertLeftPowerIso_eq_reverseConcat, insertRightPowerIso_eq_reverseConcat]
  simp only [Category.assoc]
  simp only [eqToIso.hom]
  rw [reverseConcat_eqToHom_left_assoc X (overlap_prefix_count t k)]
  rw [reverseConcat_overlap X (overlapIndex t k + 1) (t + 1)]
  simp only [Category.assoc, eqToHom_trans]

/-- The intrinsic overlap trace identity holds for every actual braid-algebra
element on a simple strand. -/
theorem overlap_trace_power (C : Ground.BraidedFusionCategory.{v,u})
    {X : C.Obj} [Simple X] (p : PivotalStructure (C := C.Obj))
    {t : ℕ} (u : braidAlgebra X t) :
    ∀ k, actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
      (groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k =
        actualBraidTrace C X p t u ^ (k + 1) :=
  overlap_trace_power_of_isos C p u (freshOverlapIso_eq_overlapPowerIso X t)

end PropertyF.Ground.Calculus
