module
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import PropertyF.Ground.Fusion.Agreement

/-! # Positive pivotal dimensions

Positive spherical dimensions agree with Frobenius–Perron dimensions and imply pseudo-unitarity.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every positive pivotal dimension character is the Frobenius–Perron
character. This does not require pseudo-unitarity or sphericality. -/
theorem positive_pivotalDimension_eq_fpSimple
    (p : PivotalStructure (C := C.Obj)) (d : Fin (rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) : ∀ i, d i = fpSimple C i := by
  have hunit : d (unitIndex C) = 1 := by
    apply Complex.ofReal_injective
    obtain ⟨e⟩ := Ground.unitIndex_iso C
    rw [← hreal, pivotalDimension_iso C p e, pivotalDimension_unit]
    norm_num
  have hchar : ∀ i j, d i * d j = ∑ k, (Ground.fusionCoeff C i j k : ℝ) * d k := by
    intro i j
    have h := pivotalDimension_character C p i j
    simp only [hreal] at h
    exact_mod_cast h
  have h := Ground.positive_character_unique C d (Ground.fpCharacter C) hpos
    (Ground.fpCharacter_pos C) hunit (Ground.fpCharacter_unit C) hchar (Ground.fpCharacter_mul C)
  intro i
  rw [Ground.fpSimple_eq_fpCharacter, ← h]

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions

/-- A positive spherical structure forces pseudo-unitarity. -/
theorem positive_spherical_isPseudoUnitary (C : BraidedFusionCategory)
    (p : PivotalStructure (C := C.Obj)) (hp : p.IsSpherical)
    (d : Fin (rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) : Ground.PseudoUnitary C := by
  unfold Ground.PseudoUnitary globalFPDimension
  rw [target_globalDimension_eq_sum_squares C p hp]
  simp only [← rightTrace_id, Complex.ofReal_sum, Complex.ofReal_pow]
  apply Finset.sum_congr rfl
  intro i _
  change pivotalDimension C p (simples C i) ^ 2 = ((fpSimple C i : ℝ) : ℂ) ^ 2
  rw [hreal, positive_pivotalDimension_eq_fpSimple C p d hreal hpos]

end PropertyF.Ground.Dimensions

end
