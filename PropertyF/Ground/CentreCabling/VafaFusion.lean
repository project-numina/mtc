module
public import PropertyF.Ground.CentreCabling.VafaAlgebra
public import PropertyF.Ground.Fusion.Agreement

/-! Fusion multiplicities occurring in the Vafa lantern determinant. -/
@[expose] public noncomputable section
open scoped BigOperators
namespace PropertyF.Ground.CentreCabling
universe v u

/-- Dimension of the multiplicity space Hom(X, X ⊗ X* ⊗ X). -/
def vafaMultiplicity (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (rank C)) : ℕ :=
  ∑ j, fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i

/-- Multiplicity of the simple twist in the three pair-twist determinants. -/
def vafaWeight (C : Ground.BraidedFusionCategory.{v,u})
    (i j : Fin (rank C)) : ℕ :=
  2 * fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i +
    fusionCoeff C i i j * fusionCoeff C j (dualIndex C i) i

/-- Associativity makes the three pair-twist multiplicity sums equal. -/
theorem vafaWeight_sum (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    ∑ j, vafaWeight C i j = 3 * vafaMultiplicity C i := by
  classical
  have h := fusionCoeff_assoc C i i (dualIndex C i) i
  simp_rw [fusionCoeff_comm C i] at h
  unfold vafaWeight vafaMultiplicity
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h' : (∑ j, fusionCoeff C i i j * fusionCoeff C j (dualIndex C i) i) =
      ∑ j, fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i := by
    simpa [fusionCoeff_comm C i] using h.symm
  rw [h']
  simp_rw [show ∀ j, 2 * fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i =
    2 * (fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i) from fun j => by ring]
  rw [← Finset.mul_sum]
  omega

/-- The tensor unit contributes to every Vafa multiplicity. -/
theorem vafaMultiplicity_pos (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    0 < vafaMultiplicity C i := by
  classical
  have h := Finset.single_le_sum
    (f := fun j => fusionCoeff C i (dualIndex C i) j * fusionCoeff C j i i)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ (unitIndex C))
  have h' : 1 ≤ vafaMultiplicity C i := by
    simpa [vafaMultiplicity, fusionCoeff_dual_unit, fusionCoeff_unit] using h
  omega

/-- The lantern exponent strictly exceeds the sum of the pair exponents. -/
theorem vafaWeight_sum_lt (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (rank C)) :
    ∑ j, vafaWeight C i j < 4 * vafaMultiplicity C i := by
  rw [vafaWeight_sum]
  have h := vafaMultiplicity_pos C i
  omega

end PropertyF.Ground.CentreCabling
