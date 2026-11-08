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

/-- The restricted dual-label support statement for an arbitrary object U
whose simple constituents all belong to the fusion subring. -/
theorem fusionSubring_dualLabel_finrank_zero_of_supported
    (A : Finset (Fin (rank C))) (hA : IsFusionSubring C A)
    (U : C.Obj) (hU : ∀ a, 0 < simpleMultiplicity C a U → a ∈ A)
    (i : Fin (rank C)) (hi : i ∈ A) (j : Fin (rank C)) (hj : j ∉ A) :
    Module.finrank ℂ (simples C (dualIndex C j) ⟶ U ⊗ (simples C i)ᘁ) = 0 := by
  have he : simpleMultiplicity C (dualIndex C j) (U ⊗ (simples C i)ᘁ) =
      simpleMultiplicity C (dualIndex C j) ((simples C i)ᘁ ⊗ U) :=
    (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (β_ U (simples C i)ᘁ)).finrank_eq
  change simpleMultiplicity C (dualIndex C j) (U ⊗ (simples C i)ᘁ) = 0
  rw [he, tensor_multiplicity]
  apply Finset.sum_eq_zero
  intro a ha
  by_cases hz : simpleMultiplicity C a U = 0
  · simp [hz]
  · have hmem := hU a (Nat.pos_of_ne_zero hz)
    have hbraid : simpleMultiplicity C (dualIndex C j) ((simples C i)ᘁ ⊗ simples C a) =
        simpleMultiplicity C (dualIndex C j) (simples C a ⊗ (simples C i)ᘁ) :=
      (CategoryTheory.Linear.homCongr ℂ (Iso.refl _) (β_ (simples C i)ᘁ (simples C a))).finrank_eq
    have hzero : simpleMultiplicity C (dualIndex C j) (simples C a ⊗ (simples C i)ᘁ) = 0 :=
      fusionSubring_dualLabel_finrank_zero C A hA a i hmem hi j hj
    rw [hbraid, hzero, mul_zero]

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

end MTC.Center.Normalization
end
