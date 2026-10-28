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

/-- The vacuum-column Kirby identity propagates to all S-square entries by
the categorical Verlinde identity and fusion reciprocity. -/
theorem categoricalS_square_of_kirby
    (D : ℂ)
    (hkirby : ∀ k, (∑ z, simpleDimension C p z * categoricalS C p k z) =
      if k = unitIndex C then D else 0) :
    HasSSquare (categoricalS C p) (dualIndex C) D := by
  classical
  intro x y
  have hprod (z : Fin (rank C)) :
      categoricalS C p x z * categoricalS C p z y =
        ∑ k, (fusionCoeff C x y k : ℂ) *
          (simpleDimension C p z * categoricalS C p k z) := by
    rw [categoricalS_symmetric C p z y]
    have h := categoricalS_verlinde C p x y z
    have hd := simpleDimension_ne_zero C p z
    simp_rw [← mul_div_assoc, ← Finset.sum_div] at h
    field_simp [hd] at h
    simpa only [Finset.sum_mul, Finset.mul_sum, mul_left_comm, mul_comm, mul_assoc] using h
  simp_rw [hprod]
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
    (hdim : HasFPSimpleDimensions C p)
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
    (hdim : HasFPSimpleDimensions C p)
    (hunique : ∀ k, k ≠ unitIndex C →
      (fun i => categoricalS C p i k / simpleDimension C p k) ≠
        (fun i => categoricalS C p i (unitIndex C) /
          simpleDimension C p (unitIndex C))) :
    (categoricalS C p).det ≠ 0 := by
  classical
  apply categoricalS_det_ne_zero_of_kirby_vanishes_off_unit C p hdim
  intro k hk
  let rules : FusionRules (Fin (rank C)) := ⟨unitIndex C, fusionCoeff C⟩
  let cols (j : Fin (rank C)) : Character rules := categoricalSCharacter C p j
  have hne : cols (unitIndex C) ≠ cols k := by
    intro he
    exact hunique k hk (congrArg Character.value he).symm
  have ho := character_orthogonal rules (dualIndex C) (fusionCoeff_dual_adjoint C)
    (cols (unitIndex C)) (cols k) hne
  have hstar (z : Fin (rank C)) : starRingEnd ℂ (simpleDimension C p z) =
      simpleDimension C p z := by rw [hdim]; simp
  have hzero : (∑ z, simpleDimension C p z *
      (categoricalS C p z k / simpleDimension C p k)) = 0 := by
    simpa [cols, categoricalSCharacter, categoricalS_unit, simpleDimension_unit, hstar] using ho
  simp_rw [← mul_div_assoc, ← Finset.sum_div] at hzero
  have h := (div_eq_zero_iff).mp hzero |>.resolve_right (simpleDimension_ne_zero C p k)
  simpa only [categoricalS_symmetric C p k] using h

/-- For FP-valued simple dimensions, S is invertible if the only simple
whose Hopf links all equal the product of dimensions is the unit. -/
theorem categoricalS_det_ne_zero_of_trivial_S_centralizer
    (hdim : HasFPSimpleDimensions C p)
    (htrivial : ∀ k, (∀ i, categoricalS C p i k =
      simpleDimension C p i * simpleDimension C p k) → k = unitIndex C) :
    (categoricalS C p).det ≠ 0 :=
  categoricalS_det_ne_zero_of_unit_character_unique C p hdim fun k hk heq ↦
    hk (htrivial k fun i ↦ (div_eq_iff (simpleDimension_ne_zero C p k)).mp (by
      simpa only [categoricalS_unit, simpleDimension_unit, div_one] using congrFun heq i))

end PropertyF.Ground.CentreModular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := C.Obj))

/-- Positive FP dimensions and twist balancing upgrade the numerical S-test
to actual transparency of a simple object. -/
theorem transparent_of_S_test_and_balancing
    (hdim : Modular.HasFPSimpleDimensions C p)
    (hbalance : IsPivotalTwistBalanced C p)
    (k : Fin (rank C))
    (hs : ∀ i, Modular.categoricalS C p i k =
      Modular.simpleDimension C p i * Modular.simpleDimension C p k) :
    Transparent (simples C k) := by
  have hsimple (i : Fin (rank C)) :
      Modular.doubleBraiding (simples C i) (simples C k) = 𝟙 _ := by
    apply CentreCabling.doubleBraiding_eq_one_of_sTest_of_finite_order hdim
    · exact mixed_monodromy_finite_of_pivotal_balancing C p hbalance _ _
    · exact hs i
  intro X
  have hx : Modular.doubleBraiding X (simples C k) = 𝟙 _ := by
    apply CentreCabling.doubleBraiding_eq_one_of_simple_constituents C (fun _ => True)
      (fun _ _ => trivial) trivial
    intro i _
    exact hsimple i
  have hc := congrArg (fun f => (β_ X (simples C k)).inv ≫ f ≫ (β_ X (simples C k)).hom) hx
  change Modular.doubleBraiding (simples C k) X = 𝟙 _
  simpa [Modular.doubleBraiding, Category.assoc] using hc

/-- In a positive pivotal category with balanced twist, S is invertible if the
unit is the only transparent simple object. -/
theorem categoricalS_det_ne_zero_of_trivial_transparency
    (hdim : Modular.HasFPSimpleDimensions C p)
    (hbalance : IsPivotalTwistBalanced C p)
    (htrivial : ∀ k, Transparent (simples C k) → k = unitIndex C) :
    (Modular.categoricalS C p).det ≠ 0 :=
  categoricalS_det_ne_zero_of_trivial_S_centralizer C p hdim fun k hs ↦
    htrivial k (transparent_of_S_test_and_balancing C p hdim hbalance k hs)

end PropertyF.Ground.CentreModular
end
