module
public import PropertyF.Ground.Cabling.Strands
public import PropertyF.Ground.Calculus.OverlapCoherence
public import Mathlib.Tactic

open CategoryTheory CategoryTheory.MonoidalCategory
open PropertyF.Ground.Dimensions

/-!
# Tensor-power concatenation

The recursively defined `reverseConcatIso` proves coherence of the two ways to
insert overlapping braid factors, and hence their trace recurrence.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable (X : C)

/-- Concatenate tensor powers, recording the total in reverse arithmetic order
so that the recursive associators need no casts. -/
def reverseConcatIso : ∀ a b : ℕ,
    tensorPower X a ⊗ tensorPower X b ≅ tensorPower X (b + a)
  | 0, b => λ_ (tensorPower X b)
  | a + 1, b => (α_ X (tensorPower X a) (tensorPower X b)) ≪≫
      (Iso.refl X ⊗ᵢ reverseConcatIso a b)

set_option backward.isDefEq.respectTransparency false in
/-- Concatenation with an empty right block is the right unitor. -/
theorem reverseConcat_zero_right (a : ℕ) :
    (reverseConcatIso X a 0).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : 0 + a = a)) =
        (ρ_ (tensorPower X a)).hom := by
  induction a with
  | zero =>
    simp only [reverseConcatIso, tensorPower, Nat.add_zero, eqToHom_refl, Category.comp_id]
    monoidal
  | succ a ih =>
    have h₀ : 0 + a = a := by omega
    simp only [reverseConcatIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, tensorPower, Category.assoc]
    rw [← whiskerLeft_eqToHom X (congrArg (tensorPower X) h₀), ← whiskerLeft_comp, ih]
    monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Adding one strand to the right commutes with tensor-power concatenation. -/
theorem reverseConcat_succ_right (a b : ℕ) :
    (reverseConcatIso X a (b + 1)).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : (b + 1) + a = (b + a) + 1)) =
    (tensorPower X a ◁ (appendIso X b).inv) ≫
      (α_ (tensorPower X a) (tensorPower X b) X).inv ≫
      ((reverseConcatIso X a b).hom ▷ X) ≫ (appendIso X (b + a)).hom := by
  induction a with
  | zero => simp [reverseConcatIso, tensorPower]
  | succ a ih =>
    have h₀ : (b + 1) + a = (b + a) + 1 := by omega
    simp only [reverseConcatIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, comp_whiskerRight, Category.assoc]
    rw [← whiskerLeft_eqToHom X (congrArg (tensorPower X) h₀), ← whiskerLeft_comp, ih]
    simp only [Nat.add_succ, appendIso_succ, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, whiskerLeft_comp]
    monoidal

set_option backward.isDefEq.respectTransparency false in
/-- Repeated right insertion is canonical reverse-indexed concatenation. -/
theorem insertRightPowerIso_eq_reverseConcat (n k : ℕ) :
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
    rw [← eqToHom_trans (congrArg (tensorPower X) h₁) (congrArg (tensorPower X) h₂),
      ← Category.assoc, reverseConcat_succ_right]
    simp only [insertRightPowerIso, Iso.trans_hom, Iso.symm_hom,
      tensorIso_hom, Iso.refl_hom, tensorHom_id, id_tensorHom, Category.assoc,
      ih, comp_whiskerRight, eqToHom_whiskerRight,
      ← eqToHom_iso_hom_naturality (appendIso X) h₀]

set_option backward.isDefEq.respectTransparency false in
/-- A shared strand can be attached to the left block before concatenating
the right tail, or kept as the head of the right block. -/
theorem reverseConcat_overlap (a b : ℕ) :
    (reverseConcatIso X a (b + 1)).hom =
      (α_ (tensorPower X a) X (tensorPower X b)).inv ≫
      ((appendIso X a).hom ▷ tensorPower X b) ≫
      (reverseConcatIso X (a + 1) b).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : b + (a + 1) = (b + 1) + a)) := by
  induction a with
  | zero => simp [reverseConcatIso, appendIso, tensorPower]
  | succ a ih =>
    have h₀ : b + (a + 1) = (b + 1) + a := by omega
    simp only [reverseConcatIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, Category.assoc]
    rw [← whiskerLeft_eqToHom X (congrArg (tensorPower X) h₀), ih, appendIso_succ]
    simp only [reverseConcatIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    monoidal

end PropertyF.Ground.Calculus

/-! Coherence of the canonical tensor-power concatenation isomorphisms. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]


section
variable (X : C)

set_option backward.isDefEq.respectTransparency false in
/-- Repeated left insertion agrees with reverse-indexed concatenation. -/
theorem insertLeftPowerIso_eq_reverseConcat (n k : ℕ) :
    (insertLeftPowerIso X n k).hom = (reverseConcatIso X k (n + 2)).hom ≫
      eqToHom (congrArg (tensorPower X) (by omega : (n + 2) + k = (n + k) + 2)) := by
  induction k with
  | zero => simp [insertLeftPowerIso, reverseConcatIso]
  | succ k ih =>
    have h : (n + 2) + k = (n + k) + 2 := by omega
    simp only [insertLeftPowerIso, reverseConcatIso, Iso.trans_hom, tensorIso_hom,
      Iso.refl_hom, id_tensorHom, Category.assoc]
    rw [← whiskerLeft_eqToHom X (congrArg (tensorPower X) h), ← whiskerLeft_comp, ← ih]

/-- Concatenation is natural under equality transport of the left length. -/
@[reassoc] theorem reverseConcat_eqToHom_left {a b : ℕ} (h : a = b) (c : ℕ) :
    (eqToHom (congrArg (tensorPower X) h) ▷ tensorPower X c) ≫
      (reverseConcatIso X b c).hom =
    (reverseConcatIso X a c).hom ≫
      eqToHom (congrArg (tensorPower X) (congrArg (fun n => c + n) h)) := by
  cases h
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The two canonical overlap isomorphisms agree. -/
theorem freshOverlapIso_eq_overlapPowerIso (t k : ℕ) :
    HasOverlapCoherence X t k := by
  apply Iso.ext
  simp only [freshOverlapIso, overlapPowerIso, Iso.trans_hom, Iso.symm_hom,
    tensorIso_hom, Iso.refl_hom, tensorHom_id, insertLeftPowerIso_eq_reverseConcat,
    insertRightPowerIso_eq_reverseConcat, Category.assoc, eqToIso.hom,
    reverseConcat_eqToHom_left_assoc X (overlap_prefix_count t k),
    reverseConcat_overlap X (overlapIndex t k + 1) (t + 1), eqToHom_trans]

end

/-- The intrinsic overlap trace identity holds for every actual braid-algebra
element on a simple strand. -/
theorem overlap_trace_power (C : BraidedFusionCategory.{v,u})
    {X : C.Obj} [Simple X] (p : PivotalStructure (C := C.Obj))
    {t : ℕ} (u : braidAlgebra X t) :
    HasOverlapTracePower C p u :=
  overlap_trace_power_of_step C p u fun k ↦
    overlap_trace_step_of_coherence C p u k
      (overlapProduct_local_of_iso k u (freshOverlapIso_eq_overlapPowerIso X t k))

end PropertyF.Ground.Calculus
