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
variable (C : BraidedFusionCategory) (p : Dimensions.PivotalStructure (C := C.Obj))

local notation "Sₚ" => categoricalS C p
local notation "dₚ" => simpleDimension C p

/-- The vacuum-column Kirby identity with loop value `D`. -/
abbrev HasKirbyIdentity (D : ℂ) : Prop :=
  ∀ k, (∑ z, dₚ z * Sₚ k z) = if k = unitIndex C then D else 0

/-- A product of S-matrix entries expands using the fusion coefficients. -/
theorem categoricalS_product (x y z : Fin (rank C)) :
    Sₚ x z * Sₚ z y = ∑ k, (fusionCoeff C x y k : ℂ) * (dₚ z * Sₚ k z) := by
  rw [categoricalS_symmetric C p z y]
  simpa only [SEntry_tensor_decomposition, Finset.sum_mul, Finset.mul_sum, mul_left_comm, mul_comm,
    mul_assoc] using
    (hopf_product_of_partialTrace_composition C p (partialTrace_doubleBraiding_tensor C p) x y z).symm

/-- The vacuum-column Kirby identity propagates to all S-square entries by
the categorical Verlinde identity and fusion reciprocity. -/
theorem categoricalS_square_of_kirby
    (D : ℂ)
    (hkirby : HasKirbyIdentity C p D) :
    HasSSquare (Sₚ) (dualIndex C) D := by
  classical
  intro x y
  simp_rw [categoricalS_product C p x y]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hkirby]
  rw [Finset.sum_eq_single_of_mem (unitIndex C) (Finset.mem_univ _)]
  · simp only [ite_true]
    rw [fusionCoeff_reciprocity_labels, fusionCoeff_unit]
    split_ifs <;> simp_all
  · intro k _ hk
    simp [hk]

/-- A nonzero Kirby vacuum-loop scalar suffices for invertibility of the
actual categorical S matrix. -/
theorem categoricalS_det_ne_zero_of_kirby
    (D : ℂ) (hD : D ≠ 0)
    (hkirby : HasKirbyIdentity C p D) :
    (Sₚ).det ≠ 0 :=
  let S := Sₚ
  let B : Matrix (Fin (rank C)) (Fin (rank C)) ℂ := fun x y ↦ S x (dualIndex C y) / D
  Matrix.det_ne_zero_of_right_inverse (by
    classical
    ext x y
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ z, S x z * (S z (dualIndex C y) / D)) = _
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, categoricalS_square_of_kirby C p D hkirby,
      dualIndex_involutive C]
    split_ifs <;> simp [*])

variable (hdim : HasFPSimpleDimensions C p)

include hdim in
/-- For FP-valued dimensions the unit Kirby loop is automatic and its value
is nonzero. Thus only the vanishing on non-unit labels remains. -/
theorem categoricalS_det_ne_zero_of_kirby_vanishes_off_unit
    (hvanish : ∀ k, k ≠ unitIndex C →
      (∑ z, dₚ z * Sₚ k z) = 0) :
    (Sₚ).det ≠ 0 := by
  classical
  apply categoricalS_det_ne_zero_of_kirby C p (globalFPDimension C : ℂ)
  · exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)))
  · intro k
    by_cases hk : k = unitIndex C
    · subst k
      rw [ite_eq_left rfl]
      simp_rw [categoricalS_symmetric C p (unitIndex C), categoricalS_unit, hdim]
      simp [globalFPDimension, Complex.ofReal_sum, pow_two]
    · rw [ite_eq_right hk]
      exact hvanish k hk

include hdim in
/-- In a category with FP-valued dimensions, it suffices for the unit's
normalized S character to be different from that of every other simple. -/
theorem categoricalS_det_ne_zero_of_unit_character_unique
    (hunique : ∀ k, k ≠ unitIndex C →
      normalizedSColumn C p k ≠ normalizedSColumn C p (unitIndex C)) :
    (Sₚ).det ≠ 0 := by
  classical
  apply categoricalS_det_ne_zero_of_kirby_vanishes_off_unit C p hdim
  intro k hk
  let rules : FusionRules (Fin (rank C)) := ⟨unitIndex C, fusionCoeff C⟩
  let cols (j : Fin (rank C)) : Character rules := categoricalSCharacter C p j
  have hzero : (∑ z, dₚ z *
      (Sₚ z k / dₚ k)) = 0 := by
    simpa [cols, categoricalSCharacter, normalizedSColumn, categoricalS_unit, simpleDimension_unit, hdim,
      fpSimple_unit] using
      character_orthogonal rules (dualIndex C) (fusionCoeff_dual_adjoint C)
        (cols (unitIndex C)) (cols k) (fun he ↦ hunique k hk (congrArg Character.value he).symm)
  simp_rw [← mul_div_assoc, ← Finset.sum_div] at hzero
  simpa only [categoricalS_symmetric C p k] using
    (div_eq_zero_iff.mp hzero).resolve_right (simpleDimension_ne_zero C p k)

include hdim in
/-- For FP-valued simple dimensions, S is invertible if the only simple
whose Hopf links all equal the product of dimensions is the unit. -/
theorem categoricalS_det_ne_zero_of_trivial_S_centralizer
    (htrivial : ∀ k, (∀ i, Sₚ i k =
      dₚ i * dₚ k) → k = unitIndex C) :
    (Sₚ).det ≠ 0 :=
  categoricalS_det_ne_zero_of_unit_character_unique C p hdim fun k hk heq ↦
    hk (htrivial k fun i ↦ (div_eq_iff (simpleDimension_ne_zero C p k)).mp (by
      simpa only [normalizedSColumn, categoricalS_unit, simpleDimension_unit, div_one] using congrFun heq i))

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))

local notation "Sₚ" => Modular.categoricalS C p
local notation "dₚ" => Modular.simpleDimension C p

variable (hdim : Modular.HasFPSimpleDimensions C p) (hbalance : IsPivotalTwistBalanced C p)

include hdim hbalance in
/-- Positive FP dimensions and twist balancing upgrade the numerical S-test
to actual transparency of a simple object. -/
theorem transparent_of_S_test_and_balancing (k : Fin (rank C))
    (hs : ∀ i, Sₚ i k =
      dₚ i * dₚ k) :
    Transparent (simples C k) := by
  intro X
  have hx : Modular.doubleBraiding X (simples C k) = 𝟙 _ := by
    apply CentreCabling.doubleBraiding_eq_one_of_simple_constituents C (fun _ => True)
      (fun _ _ => trivial) trivial
    intro i _
    exact CentreCabling.doubleBraiding_eq_one_of_sTest_of_finite_order hdim
      (mixed_monodromy_finite_of_pivotal_balancing C p hbalance _ _) (hs i)
  change Modular.doubleBraiding (simples C k) X = 𝟙 _
  simpa [Modular.doubleBraiding, Category.assoc] using
    congrArg (fun f => (β_ X (simples C k)).inv ≫ f ≫ (β_ X (simples C k)).hom) hx

include hdim hbalance in
/-- In a positive pivotal category with balanced twist, S is invertible if the
unit is the only transparent simple object. -/
theorem categoricalS_det_ne_zero_of_trivial_transparency
    (htrivial : ∀ k, Transparent (simples C k) → k = unitIndex C) :
    (Sₚ).det ≠ 0 :=
  categoricalS_det_ne_zero_of_trivial_S_centralizer C p hdim fun k hs ↦
    htrivial k (transparent_of_S_test_and_balancing C p hdim hbalance k hs)

end PropertyF.Ground.CentreModular
end
