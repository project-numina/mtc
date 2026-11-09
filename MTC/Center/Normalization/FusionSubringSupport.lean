module
public import MTC.Center.Braid.RegularSupport
public import MTC.CategoryTheory.Dimensions.ENOReciprocity

open MTC.Fusion MTC.Braided MTC.Center.Braid MTC.CategoryTheory.Dimensions

/-! # Dual-label support for fusion subrings -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- Every constituent of a tensor product arises from constituents of both
factors with a positive fusion coefficient. -/
theorem tensor_constituent_factors (X Y : C.Obj) (k : Fin (rank C))
    (hk : 0 < simpleMultiplicity C k (X ⊗ Y)) :
    ∃ i j, 0 < simpleMultiplicity C i X ∧ 0 < simpleMultiplicity C j Y ∧
      0 < fusionCoeff C i j k := by
  rw [tensor_multiplicity_expanded] at hk
  obtain ⟨i, _, hi⟩ := Finset.sum_pos_iff.mp hk
  obtain ⟨j, _, hj⟩ := Finset.sum_pos_iff.mp hi
  have hm := Nat.pos_of_mul_pos_right hj
  exact ⟨i, j, Nat.pos_of_mul_pos_right hm, Nat.pos_of_mul_pos_left hm,
    Nat.pos_of_mul_pos_left hj⟩

theorem supportedOn_tensor {A : Finset (Fin (rank C))} (hA : IsFusionSubring C A)
    {X Y : C.Obj} (hX : SupportedOn C A X) (hY : SupportedOn C A Y) :
    SupportedOn C A (X ⊗ Y) := by
  intro k hk
  obtain ⟨i, j, hi, hj, hijk⟩ := tensor_constituent_factors C X Y k hk
  exact hA.fusion i (hX i hi) j (hY j hj) k hijk

end MTC.PropertyF.Pivotal

open MTC.PropertyF.Pivotal

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
  have hj' : dualIndex C j ∉ A := by
    intro h
    have h' := hA.dual (dualIndex C j) h
    apply hj
    rwa [dualIndex_involutive C j] at h'
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
  apply Nat.eq_zero_of_not_pos
  intro hp
  exact hi (supportedOn_tensor C hA ((supportedOn_simple_iff C j).2 hj) hU i hp)

/-- The restricted dual-label support statement for an arbitrary object U
whose simple constituents all belong to the fusion subring. -/
theorem fusionSubring_dualLabel_finrank_zero_of_supported
    (A : Finset (Fin (rank C))) (hA : IsFusionSubring C A)
    (U : C.Obj) (hU : ∀ a, 0 < simpleMultiplicity C a U → a ∈ A)
    (i : Fin (rank C)) (hi : i ∈ A) (j : Fin (rank C)) (hj : j ∉ A) :
    Module.finrank ℂ (simples C (dualIndex C j) ⟶ U ⊗ (simples C i)ᘁ) = 0 := by
  have hj' : dualIndex C j ∉ A := by
    intro h
    apply hj
    have h' := hA.dual (dualIndex C j) h
    rwa [dualIndex_involutive C j] at h'
  have he := (CategoryTheory.Linear.homCongr ℂ (Iso.refl (simples C (dualIndex C j)))
    ((Iso.refl U ⊗ᵢ (rightDualLabelIso C i)) ≪≫ β_ U (simples C (dualIndex C i)))).finrank_eq
  exact he.trans (fusionSubring_forward_finrank_zero_of_supported C A hA
    (dualIndex C i) (hA.dual i hi) U hU (dualIndex C j) hj')

end MTC.Center.Normalization
end
