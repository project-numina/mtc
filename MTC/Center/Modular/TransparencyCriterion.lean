module
public import MTC.Center.Modular.Vafa
public import MTC.Center.Braid.CentralityClosure
public import MTC.Center.Braid.TraceSaturation
public import MTC.Modular.SSquare

open MTC.Braided

/-!
# Kirby identities and nondegeneracy from trivial transparency.
-/

@[expose] public noncomputable section

section
/-! A Kirby-colour loop identity implies the S-square identity and nondegeneracy.
Trivial transparency provides the needed vanishing in a positive pivotal category. -/

open scoped BigOperators
namespace MTC.Center.Modular
open MTC.Modular
variable (C : BraidedFusionCategory) (p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := C.Obj))

local notation "Sₚ" => categoricalS C p
local notation "dₚ" => simpleDimension C p

/-- The vacuum-column Kirby identity with loop value `D`. -/
abbrev HasKirbyIdentity {ι K : Type*} [Fintype ι] [DecidableEq ι] [Semiring K]
    (S : Matrix ι ι K) (d : ι → K) (u : ι) (D : K) : Prop :=
  ∀ k, (∑ z, d z * S k z) = if k = u then D else 0

section Kirby
variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
variable {N : FusionRules ι} {S : Matrix ι ι K} {d : ι → K} {dual : ι → ι} {D : K}
variable (hsym : ∀ x y, S x y = S y x) (hd : ∀ z, d z ≠ 0)
variable (hVerlinde : HasVerlindeFormula N S d)
variable (hunit : ∀ x y, N.coeff x y N.unit = if x = dual y then 1 else 0)

include hsym hd hVerlinde hunit in
/-- The vacuum-column Kirby identity and fusion rules imply S squared is duality. -/
theorem fusion_S_square_of_kirby (hkirby : HasKirbyIdentity S d N.unit D) : HasSSquare S dual D :=
  fun x y ↦ by
    dsimp only [HasKirbyIdentity] at hkirby
    simp_rw [fusion_character_product hsym hd hVerlinde x y]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hkirby]
    rw [Finset.sum_eq_single_of_mem N.unit (Finset.mem_univ _)]
    · simp only [ite_true, hunit]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]

include hsym hd hVerlinde hunit in
/-- A nonzero Kirby vacuum-loop scalar makes the S matrix invertible. -/
theorem fusion_S_det_ne_zero_of_kirby (hdual : Function.Involutive dual) (hD : D ≠ 0)
    (hkirby : HasKirbyIdentity S d N.unit D) : S.det ≠ 0 :=
  let B : Matrix ι ι K := fun x y ↦ S x (dual y) / D
  Matrix.det_ne_zero_of_right_inverse (by
    ext x y
    rw [Matrix.mul_apply, Matrix.one_apply]
    change (∑ z, S x z * (S z (dual y) / D)) = _
    simp_rw [← mul_div_assoc]
    rw [← Finset.sum_div, fusion_S_square_of_kirby hsym hd hVerlinde hunit hkirby, hdual]
    split_ifs <;> simp [hD])

end Kirby

variable (hdim : HasFPSimpleDimensions C p)

include hdim in
/-- For FP-valued dimensions the unit Kirby loop is automatic and its value
is nonzero. Thus only the vanishing on non-unit labels remains. -/
theorem categoricalS_det_ne_zero_of_kirby_vanishes_off_unit
    (hvanish : ∀ k, k ≠ unitIndex C →
      (∑ z, dₚ z * Sₚ k z) = 0) :
    (Sₚ).det ≠ 0 := by
  refine fusion_S_det_ne_zero_of_kirby (N := ⟨unitIndex C, fusionCoeff C⟩)
    (D := (globalFPDimension C : ℂ)) (categoricalS_symmetric C p)
    (simpleDimension_ne_zero C p) (categoricalS_verlinde C p)
    (fun x y ↦ (fusionCoeff_reciprocity_labels (D := C) x y (unitIndex C)).trans
      (fusionCoeff_unit C (dualIndex C y) x)) (dualIndex_involutive C) ?_ (fun k ↦ ?_)
  · exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_globalFPDimension C)))
  · split_ifs with hk
    · simp [hk, categoricalS_symmetric C p, categoricalS_unit, hdim, globalFPDimension, pow_two]
    · exact hvanish k hk

include hdim in
/-- In a category with FP-valued dimensions, it suffices for the unit's
normalized S character to be different from that of every other simple. -/
theorem categoricalS_det_ne_zero_of_unit_character_unique
    (hunique : ∀ k, k ≠ unitIndex C →
      normalizedSColumn C p k ≠ normalizedSColumn C p (unitIndex C)) :
    (Sₚ).det ≠ 0 :=
  categoricalS_det_ne_zero_of_kirby_vanishes_off_unit C p hdim fun k hk ↦
    (div_eq_zero_iff.mp (show (∑ z, dₚ z * Sₚ k z) / dₚ k = 0 from by
      simpa [categoricalSCharacter, normalizedSColumn, categoricalS_unit, simpleDimension_unit, hdim,
        fpSimple_unit, categoricalS_symmetric C p k, ← mul_div_assoc, ← Finset.sum_div] using
        character_orthogonal _ (dualIndex C) (fun i j k ↦ MTC.fusionCoeff_dual_symmetry C i k j)
          (categoricalSCharacter C p (unitIndex C)) (categoricalSCharacter C p k)
          (fun he ↦ hunique k hk (congrArg Character.value he).symm))).resolve_right
      (simpleDimension_ne_zero C p k)

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

end MTC.Center.Modular
end

section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace MTC.Center.Modular
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : MTC.CategoryTheory.Dimensions.PivotalStructure (C := C.Obj))

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
    obtain ⟨m, ⟨e⟩⟩ := simples_decompose C X
    apply MTC.Center.Braid.doubleBraiding_eq_one_of_constituents (simples C) e (fun _ => True)
      (fun _ _ => trivial) trivial
    intro i _
    exact MTC.Center.Braid.doubleBraiding_eq_one_of_sTest_of_finite_order hdim
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

end MTC.Center.Modular
end
