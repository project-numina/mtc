module
public import MTC.Center.Braid.RegularSupport
public import MTC.CategoryTheory.Dimensions.ENOReciprocity

open MTC.Fusion MTC.Braided MTC.Center.Braid MTC.CategoryTheory.Dimensions

/-! # Dual-label support for fusion subrings -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Normalization
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- If two labels lie in a fusion subring, the tensor of the first simple and
the right dual of the second has no simple summands with dual label outside
that subring. -/
theorem fusionSubring_dualLabel_finrank_zero
    (A : Finset (Fin (rank C))) (hA : IsFusionSubring C A)
    (a i : Fin (rank C)) (ha : a ∈ A) (hi : i ∈ A)
    (j : Fin (rank C)) (hj : j ∉ A) :
    Module.finrank ℂ (simples C (dualIndex C j) ⟶
      simples C a ⊗ (simples C i)ᘁ) = 0 := by
  have hj' : dualIndex C j ∉ A := by
    intro h
    have h' := hA.dual (dualIndex C j) h
    apply hj
    rwa [dualIndex_involutive C j] at h'
  have hcoeff : fusionCoeff C a (dualIndex C i) (dualIndex C j) = 0 := by
    apply Nat.eq_zero_of_not_pos
    intro hp
    exact hj' (hA.fusion a ha (dualIndex C i) (hA.dual i hi) (dualIndex C j) hp)
  have he := (CategoryTheory.Linear.homCongr ℂ (Iso.refl (simples C (dualIndex C j)))
    (Iso.refl (simples C a) ⊗ᵢ rightDualLabelIso C i)).finrank_eq
  change Module.finrank ℂ (simples C (dualIndex C j) ⟶
    simples C a ⊗ (simples C i)ᘁ) = fusionCoeff C a (dualIndex C i) (dualIndex C j) at he
  exact he.trans hcoeff

end MTC.Center.Normalization
end
