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

/-- Tensor products of two subring simples have no constituents with labels
outside the subring. -/
theorem fusionSubring_forward_finrank_zero
    (A : Finset (Fin (rank C))) (hA : IsFusionSubring C A)
    (j a : Fin (rank C)) (hj : j ∈ A) (ha : a ∈ A)
    (i : Fin (rank C)) (hi : i ∉ A) :
    Module.finrank ℂ (simples C i ⟶ simples C j ⊗ simples C a) = 0 := by
  change fusionCoeff C j a i = 0
  apply Nat.eq_zero_of_not_pos
  intro hp
  exact hi (hA.fusion j hj a ha i hp)

/-- If two labels lie in a fusion subring, the tensor of the first simple and
the right dual of the second has no simple summands with dual label outside
that subring. -/
theorem fusionSubring_dualLabel_finrank_zero
    (A : Finset (Fin (rank C))) (hA : IsFusionSubring C A)
    (a i : Fin (rank C)) (ha : a ∈ A) (hi : i ∈ A)
    (j : Fin (rank C)) (hj : j ∉ A) :
    Module.finrank ℂ (simples C (dualIndex C j) ⟶
      simples C a ⊗ (simples C i)ᘁ) = 0 := by
  have hj' : dualIndex C j ∉ A := fun h ↦ hj (by
    simpa only [dualIndex_involutive C j] using hA.dual (dualIndex C j) h)
  have he := (CategoryTheory.Linear.homCongr ℂ (Iso.refl (simples C (dualIndex C j)))
    (Iso.refl (simples C a) ⊗ᵢ rightDualLabelIso C i)).finrank_eq
  exact he.trans (fusionSubring_forward_finrank_zero C A hA a (dualIndex C i)
    ha (hA.dual i hi) (dualIndex C j) hj')

/-- The forward support statement for arbitrary U whose simple constituents
belong to the fusion subring. -/
theorem fusionSubring_forward_finrank_zero_of_supported
    (A : Finset (Fin (rank C))) (hA : IsFusionSubring C A)
    (j : Fin (rank C)) (hj : j ∈ A) (U : C.Obj)
    (hU : ∀ a, 0 < simpleMultiplicity C a U → a ∈ A)
    (i : Fin (rank C)) (hi : i ∉ A) :
    Module.finrank ℂ (simples C i ⟶ simples C j ⊗ U) = 0 := by
  change simpleMultiplicity C i (simples C j ⊗ U) = 0
  rw [tensor_multiplicity]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hz : simpleMultiplicity C a U = 0
  · simp [hz]
  · have hzero : simpleMultiplicity C i (simples C j ⊗ simples C a) = 0 :=
      fusionSubring_forward_finrank_zero C A hA j a hj (hU a (Nat.pos_of_ne_zero hz)) i hi
    rw [hzero, mul_zero]

/-- The restricted dual-label support statement for an arbitrary object U
whose simple constituents all belong to the fusion subring. -/
theorem fusionSubring_dualLabel_finrank_zero_of_supported
    (A : Finset (Fin (rank C))) (hA : IsFusionSubring C A)
    (U : C.Obj) (hU : ∀ a, 0 < simpleMultiplicity C a U → a ∈ A)
    (i : Fin (rank C)) (hi : i ∈ A) (j : Fin (rank C)) (hj : j ∉ A) :
    Module.finrank ℂ (simples C (dualIndex C j) ⟶ U ⊗ (simples C i)ᘁ) = 0 := by
  have hj' : dualIndex C j ∉ A := fun h ↦ hj (by
    simpa only [dualIndex_involutive C j] using hA.dual (dualIndex C j) h)
  have he := (CategoryTheory.Linear.homCongr ℂ (Iso.refl (simples C (dualIndex C j)))
    ((Iso.refl U ⊗ᵢ (rightDualLabelIso C i)) ≪≫ β_ U (simples C (dualIndex C i)))).finrank_eq
  exact he.trans (fusionSubring_forward_finrank_zero_of_supported C A hA
    (dualIndex C i) (hA.dual i hi) U hU (dualIndex C j) hj')

end MTC.Center.Normalization
end
