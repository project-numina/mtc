module
public import PropertyF.Ground.Calculus.OverlapCoherence
public import PropertyF.Ground.Cabling.PowerGeneral
public import PropertyF.Ground.Calculus.ReversePower

/-! Coherence of the canonical tensor-power concatenation isomorphisms. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
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

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
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

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
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

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
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
    (X : C.Obj) [Simple X] (p : Dimensions.PivotalStructure (C := C.Obj))
    (t : ℕ) (u : braidAlgebra X t) :
    ∀ k, actualBraidTrace C X p (overlapIndex t k) (overlapProduct X t u k) *
      (Dimensions.groundUnitScalarEquiv C (p.rightTrace (𝟙 X))) ^ k =
        actualBraidTrace C X p t u ^ (k + 1) :=
  overlap_trace_power_of_isos C X p t u (freshOverlapIso_eq_overlapPowerIso X t)

end PropertyF.Ground.Calculus
