module
public import PropertyF.Ground.CentreInduction.Underlying
public import PropertyF.Ground.Integrate.CenterBundle
public import Mathlib.CategoryTheory.Adjunction.Additive

/-! The numerical consequence of the induction adjunction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreInduction
universe v u
variable (C : BraidedFusionCategory.{v,u}) [RigidCategory (CategoryTheory.Center C.Obj)]
  [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵ᶠ" => Integrate.bundledCenter C
local notation "𝒵" => CategoryTheory.Center C.Obj

/-- Once induced simple representatives have the expected underlying objects
and the adjunction supplies the displayed Hom dimension equality, the global
FP dimension of the actual centre is the square of that of the base. The
hypotheses isolate the numerical contribution of the induction adjunction. -/
theorem globalFPDimension_square_of_induction
    (I : Fin (rank C) → (𝒵ᶠ).Obj)
    (hI : ∀ i, Nonempty ((I i).1 ≅ underlying C (simples C i)))
    (hadj : ∀ i j,
      Module.finrank ℂ ((simples 𝒵ᶠ j : 𝒵) ⟶ I i) =
      Module.finrank ℂ ((simples 𝒵ᶠ j).1 ⟶ simples C i)) :
    globalFPDimension 𝒵ᶠ = (globalFPDimension C) ^ 2 := by
  classical
  have hdim (i : Fin (rank C)) :
      fpDimension 𝒵ᶠ (I i) = globalFPDimension C * fpSimple C i := by
    simpa only [fpDimension_underlying, fpDimension_simple] using
      (show fpDimension 𝒵ᶠ (I i) = fpDimension C (I i).1 from
        (Integrate.center_forget_fpDimension C (I i)).symm).trans
          (fpDimension_iso C (hI i).some)
  have hbase (j : Fin (rank 𝒵ᶠ)) :
      ∑ i, (Module.finrank ℂ ((simples 𝒵ᶠ j).1 ⟶ simples C i) : ℝ) * fpSimple C i =
        fpSimple 𝒵ᶠ j := by
    simpa only [fpDimension, ← finrank_to_simple_eq_from_simple C] using
      (show fpDimension C (simples 𝒵ᶠ j).1 = fpSimple 𝒵ᶠ j from
        (Integrate.center_forget_fpDimension C (simples 𝒵ᶠ j)).trans (fpDimension_simple 𝒵ᶠ j))
  have hsum : (∑ i, fpSimple C i * fpDimension 𝒵ᶠ (I i)) = globalFPDimension 𝒵ᶠ := by
    simp_rw [fpDimension, hadj, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [mul_comm (fpSimple C _), mul_comm _ (fpSimple 𝒵ᶠ _), mul_assoc]
    simp_rw [← Finset.mul_sum, hbase]
    simp [globalFPDimension, pow_two]
  calc
    globalFPDimension 𝒵ᶠ = ∑ i, fpSimple C i * fpDimension 𝒵ᶠ (I i) := hsum.symm
    _ = (globalFPDimension C) ^ 2 := by
      simp_rw [hdim, mul_left_comm (fpSimple C _) (globalFPDimension C)]
      rw [← Finset.mul_sum]
      simp [globalFPDimension, pow_two]

end PropertyF.Ground.CentreInduction

end

/-! A linear adjunction supplies the multiplicities needed for the FP-square calculation. -/

@[expose] public noncomputable section
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreInduction
universe v u v' u'

/-- The reverse Hom equivalence of an adjunction is linear when its left
adjoint is linear. -/
def homLinearEquivOfAdjunction {k : Type*} [CommSemiring k] {A : Type u} {B : Type u'}
    [Category.{v} A] [Category.{v'} B] [Preadditive A] [Preadditive B]
    [Linear k A] [Linear k B] (F : A ⥤ B) (G : B ⥤ A)
    [F.Additive] [F.Linear k] (adj : F ⊣ G) (X : A) (Y : B) :
    (X ⟶ G.obj Y) ≃ₗ[k] (F.obj X ⟶ Y) := by
  refine { (adj.homAddEquiv X Y).symm with map_smul' := ?_ }
  intro r f
  change (adj.homEquiv X Y).symm (r • f) = r • (adj.homEquiv X Y).symm f
  simp [Adjunction.homEquiv_counit, Functor.map_smul, Linear.smul_comp]

end PropertyF.Ground.CentreInduction
