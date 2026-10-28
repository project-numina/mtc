module
public import PropertyF.Ground.Centre.Modular.Vafa
public import PropertyF.Ground.CentreCabling.CentralityClosure
public import PropertyF.Ground.CentreCabling.TraceSaturation
public import PropertyF.Ground.Modular.SSquare

/-!
# Kirby identities and nondegeneracy from trivial transparency.
-/

@[expose] public noncomputable section

section
/-! A single Kirby-colour loop identity implies the full S-square identity
and nondegeneracy. The loop identity for the actual centre remains open. -/

open scoped BigOperators
namespace PropertyF.Ground.CentreModular
open Modular

/-- The vacuum-column Kirby identity propagates to all S-square entries by
the categorical Verlinde identity and fusion reciprocity. -/
theorem categoricalS_square_of_kirby
    (C : BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))
    (D : ℂ)
    (hkirby : ∀ k, (∑ z, simpleDimension C p z * categoricalS C p k z) =
      if k = unitIndex C then D else 0)
    (x y : Fin (rank C)) :
    (∑ z, categoricalS C p x z * categoricalS C p z y) =
      if x = dualIndex C y then D else 0 := by
  classical
  have hprod (z : Fin (rank C)) :
      categoricalS C p x z * categoricalS C p z y =
        ∑ k, (fusionCoeff C x y k : ℂ) *
          (simpleDimension C p z * categoricalS C p k z) := by
    rw [categoricalS_symmetric C p z y]
    have h := categoricalS_verlinde C p x y z
    have hd := simpleDimension_ne_zero C p z
    have h' := congrArg (fun a : ℂ => a * simpleDimension C p z ^ 2) h
    simp only [Finset.sum_mul] at h'
    have ht (k : Fin (rank C)) : (fusionCoeff C x y k : ℂ) *
        (categoricalS C p k z / simpleDimension C p z) * simpleDimension C p z ^ 2 =
        (fusionCoeff C x y k : ℂ) * (simpleDimension C p z * categoricalS C p k z) := by
      field_simp
    simp_rw [ht] at h'
    have hl : categoricalS C p x z / simpleDimension C p z *
        (categoricalS C p y z / simpleDimension C p z) * simpleDimension C p z ^ 2 =
        categoricalS C p x z * categoricalS C p y z := by
      field_simp
    rw [hl] at h'
    exact h'
  simp_rw [hprod]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hkirby]
  rw [Finset.sum_eq_single (unitIndex C)]
  · simp only [ite_true]
    rw [fusionCoeff_reciprocity_labels, fusionCoeff_unit]
    split_ifs <;> simp_all
  · intro k _ hk
    simp [hk]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- A nonzero Kirby vacuum-loop scalar suffices for invertibility of the
actual categorical S matrix. -/
theorem categoricalS_det_ne_zero_of_kirby
    (C : BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))
    (D : ℂ) (hD : D ≠ 0)
    (hkirby : ∀ k, (∑ z, simpleDimension C p z * categoricalS C p k z) =
      if k = unitIndex C then D else 0) :
    (categoricalS C p).det ≠ 0 := by
  classical
  let S := categoricalS C p
  let B : Matrix (Fin (rank C)) (Fin (rank C)) ℂ :=
    fun x y => S x (dualIndex C y) / D
  have hSB : S * B = 1 := by
    ext x y
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ z, S x z * (S z (dualIndex C y) / D)) = _
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, categoricalS_square_of_kirby C p D hkirby,
      dualIndex_involutive C]
    split_ifs <;> simp [*]
  exact Matrix.det_ne_zero_of_right_inverse hSB

/-- For FP-valued dimensions the unit Kirby loop is automatic and its value
is nonzero. Thus only the vanishing on non-unit labels remains. -/
theorem categoricalS_det_ne_zero_of_kirby_vanishes_off_unit
    (C : BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, simpleDimension C p i = (fpSimple C i : ℂ))
    (hvanish : ∀ k, k ≠ unitIndex C →
      (∑ z, simpleDimension C p z * categoricalS C p k z) = 0) :
    (categoricalS C p).det ≠ 0 := by
  classical
  apply categoricalS_det_ne_zero_of_kirby C p (globalFPDimension C : ℂ)
  · exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)))
  · intro k
    by_cases hk : k = unitIndex C
    · subst k
      simp only [ite_true]
      simp_rw [categoricalS_symmetric C p (unitIndex C), categoricalS_unit, hdim]
      simp [globalFPDimension, Complex.ofReal_sum, pow_two]
    · rw [ite_eq_right hk]
      exact hvanish k hk

/-- In a category with FP-valued dimensions, it suffices for the unit's
normalized S character to be different from that of every other simple. -/
theorem categoricalS_det_ne_zero_of_unit_character_unique
    (C : BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, simpleDimension C p i = (fpSimple C i : ℂ))
    (hunique : ∀ k, k ≠ unitIndex C →
      (fun i => categoricalS C p i k / simpleDimension C p k) ≠
        (fun i => categoricalS C p i (unitIndex C) /
          simpleDimension C p (unitIndex C))) :
    (categoricalS C p).det ≠ 0 := by
  classical
  apply categoricalS_det_ne_zero_of_kirby_vanishes_off_unit C p hdim
  intro k hk
  let rules : FusionRules (Fin (rank C)) := ⟨unitIndex C, fusionCoeff C⟩
  let cols (j : Fin (rank C)) : Character rules := {
    value := fun i => categoricalS C p i j / simpleDimension C p j
    unit_eq := by rw [categoricalS_symmetric C p, categoricalS_unit]; exact div_self (simpleDimension_ne_zero C p j)
    mul_eq := fun i t => categoricalS_verlinde C p i t j }
  have hne : cols (unitIndex C) ≠ cols k := by
    intro he
    exact hunique k hk (congrArg Character.value he).symm
  have ho := character_orthogonal rules (dualIndex C) (fusionCoeff_dual_adjoint C)
    (cols (unitIndex C)) (cols k) hne
  have hu : ∀ z, (cols (unitIndex C)).value z = simpleDimension C p z := by
    intro z
    simp [cols, categoricalS_unit, simpleDimension_unit]
  have hstar (z : Fin (rank C)) : starRingEnd ℂ (simpleDimension C p z) =
      simpleDimension C p z := by rw [hdim]; simp
  have hzero : (∑ z, simpleDimension C p z *
      (categoricalS C p z k / simpleDimension C p k)) = 0 := by
    simpa only [hu, hstar] using ho
  have h := congrArg (fun x : ℂ => x * simpleDimension C p k) hzero
  rw [Finset.sum_mul] at h
  simp only [zero_mul] at h
  have ht (z : Fin (rank C)) : simpleDimension C p z *
      (categoricalS C p z k / simpleDimension C p k) * simpleDimension C p k =
      simpleDimension C p z * categoricalS C p k z := by
    rw [categoricalS_symmetric C p k z]
    field_simp [simpleDimension_ne_zero C p k]
  simpa only [ht] using h

/-- For FP-valued simple dimensions, S is invertible if the only simple
whose Hopf links all equal the product of dimensions is the unit. -/
theorem categoricalS_det_ne_zero_of_trivial_S_centralizer
    (C : BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, simpleDimension C p i = (fpSimple C i : ℂ))
    (htrivial : ∀ k, (∀ i, categoricalS C p i k =
      simpleDimension C p i * simpleDimension C p k) → k = unitIndex C) :
    (categoricalS C p).det ≠ 0 := by
  apply categoricalS_det_ne_zero_of_unit_character_unique C p hdim
  intro k hk heq
  apply hk
  apply htrivial k
  intro i
  have hh := congrFun heq i
  rw [categoricalS_unit, simpleDimension_unit, div_one] at hh
  exact (div_eq_iff (simpleDimension_ne_zero C p k)).mp hh

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u

/-- Positive FP dimensions and twist balancing upgrade the numerical S-test
to actual transparency of a simple object. -/
theorem transparent_of_S_test_and_balancing
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (hbalance : ∀ X Y, Modular.doubleBraiding X Y ≫
      ((Dimensions.pivotalBraidedTwist C p X).hom ⊗ₘ
        (Dimensions.pivotalBraidedTwist C p Y).hom) =
      (Dimensions.pivotalBraidedTwist C p (X ⊗ Y)).hom)
    (k : Fin (rank C))
    (hs : ∀ i, Modular.categoricalS C p i k =
      Modular.simpleDimension C p i * Modular.simpleDimension C p k) :
    Transparent (simples C k) := by
  have hsimple (i : Fin (rank C)) :
      Modular.doubleBraiding (simples C i) (simples C k) = 𝟙 _ := by
    apply CentreCabling.doubleBraiding_eq_one_of_sTest_of_finite_order C p hdim i k
    · exact mixed_monodromy_finite_of_pivotal_balancing C p hbalance _ _
    · exact hs i
  intro X
  have hx : Modular.doubleBraiding X (simples C k) = 𝟙 _ := by
    apply CentreCabling.doubleBraiding_eq_one_of_simple_constituents C (fun _ => True)
      (fun _ _ => trivial) X (simples C k) trivial
    intro i _
    exact hsimple i
  have hc := congrArg (fun f => (β_ X (simples C k)).inv ≫ f ≫ (β_ X (simples C k)).hom) hx
  change Modular.doubleBraiding (simples C k) X = 𝟙 _
  simpa [Modular.doubleBraiding, Category.assoc] using hc

/-- In a positive pivotal category with balanced twist, S is invertible if the
unit is the only transparent simple object. -/
theorem categoricalS_det_ne_zero_of_trivial_transparency
    (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))
    (hdim : ∀ i, Modular.simpleDimension C p i = (fpSimple C i : ℂ))
    (hbalance : ∀ X Y, Modular.doubleBraiding X Y ≫
      ((Dimensions.pivotalBraidedTwist C p X).hom ⊗ₘ
        (Dimensions.pivotalBraidedTwist C p Y).hom) =
      (Dimensions.pivotalBraidedTwist C p (X ⊗ Y)).hom)
    (htrivial : ∀ k, Transparent (simples C k) → k = unitIndex C) :
    (Modular.categoricalS C p).det ≠ 0 := by
  apply categoricalS_det_ne_zero_of_trivial_S_centralizer C p hdim
  intro k hs
  exact htrivial k (transparent_of_S_test_and_balancing C p hdim hbalance k hs)

end PropertyF.Ground.CentreModular
end
