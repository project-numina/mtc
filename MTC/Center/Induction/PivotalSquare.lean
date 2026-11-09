module
public import MTC.Center.Induction.PivotalFusion
public import MTC.Center.Induction.ActualFusion

open MTC.Fusion MTC.Braided MTC.CategoryTheory.Dimensions MTC.PropertyF.Reduction

/-! # The centre dimension square for general pivotal structures -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits Module
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace MTC.Center.Induction
universe v u
variable {C : BraidedFusionCategory.{v,u}}
  [RigidCategory (Center C.Obj)] [IsFusionCategory (Center C.Obj)]
local notation "𝒵ᶠ" => bundledCenter C

/-- A compatible pivotal structure gives the induced objects their expected
intrinsic dimensions. -/
theorem center_pivotalDimension_induction
    {p : PivotalStructure (C := C.Obj)} {pZ : PivotalStructure (C := Center C.Obj)}
    (hcompat : ∀ Z, PivotalCompatibleAt p pZ Z) (X : C.Obj) :
    pivotalDimension 𝒵ᶠ pZ ((induction C).obj X) =
      globalDimension C * pivotalDimension C p X := by
  rw [center_pivotalDimension_forget (hcompat _)]
  exact pivotalDimension_underlying p X

/-- Forgetting a centre object takes its pivotal dimension to the dimension of
its underlying object, including complex conjugates. -/
theorem center_pivotalDimension_conj_forget
    {p : PivotalStructure (C := C.Obj)} {pZ : PivotalStructure (C := Center C.Obj)}
    (hcompat : ∀ Z, PivotalCompatibleAt p pZ Z) (Z : Center C.Obj) :
    star (pivotalDimension 𝒵ᶠ pZ Z) = star (pivotalDimension C p Z.1) := by
  rw [center_pivotalDimension_forget (hcompat Z)]

/-- The global dimension of the centre is the square of the base global
dimension. The proof uses an arbitrary compatible pivotal structure. -/
theorem globalDimension_square_of_actual_induction
    {p : PivotalStructure (C := C.Obj)} {pZ : PivotalStructure (C := Center C.Obj)}
    (hcompat : ∀ Z, PivotalCompatibleAt p pZ Z) :
    globalDimension 𝒵ᶠ = globalDimension C ^ 2 := by
  have h : globalDimension 𝒵ᶠ =
      ∑ i, star (pivotalDimension C p (simples C i)) *
        pivotalDimension 𝒵ᶠ pZ ((induction C).obj (simples C i)) := by
    symm
    conv_lhs =>
      arg 2
      ext i
      rw [pivotalDimension_decomposition 𝒵ᶠ pZ (X := (induction C).obj (simples C i))]
    simp_rw [simpleMultiplicity, finrank_hom_induction (C := C), Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_comm (star (pivotalDimension C p _)),
      mul_comm _ (pivotalDimension 𝒵ᶠ pZ _), mul_assoc, ← Finset.mul_sum]
    have hsum (Z : C.Obj) :
        (∑ i, (finrank ℂ (Z ⟶ simples C i) : ℂ) *
          star (pivotalDimension C p (simples C i))) = star (pivotalDimension C p Z) := by
      rw [pivotalDimension_decomposition C p (X := Z)]
      simp only [simpleMultiplicity, star_sum, star_mul, star_natCast]
      apply Finset.sum_congr rfl
      intro i hi
      let : Simple (simples C i) := simples_simple C i
      rw [finrank_to_simple_eq_from_simple, mul_comm]
    simp_rw [hsum, ← center_pivotalDimension_conj_forget hcompat]
    simpa only [mul_comm] using (globalDimension_eq_sum_pivotal_conj_mul (C := 𝒵ᶠ) pZ).symm
  rw [h]
  simp_rw [center_pivotalDimension_induction hcompat, mul_left_comm (star _),
    ← Finset.mul_sum, ← globalDimension_eq_sum_pivotal_conj_mul (C := C) p, ← pow_two]

/-- The square formula uses the canonical lift of the given pivotal structure. -/
theorem globalDimension_square_of_pivotal
    (p : PivotalStructure (C := C.Obj)) :
    globalDimension 𝒵ᶠ = globalDimension C ^ 2 :=
  globalDimension_square_of_actual_induction
    (fun Z ↦ liftedPivotalStructure_compatible (pivotalComponentsCentral_proved p) Z)

end MTC.Center.Induction
end
