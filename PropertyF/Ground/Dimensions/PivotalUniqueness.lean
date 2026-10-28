module
public import PropertyF.Ground.Dimensions.IntrinsicNonzero
public import PropertyF.Ground.Fusion.Agreement

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Every positive pivotal dimension character is the Frobenius–Perron
character. This does not require pseudo-unitarity or sphericality. -/
theorem positive_pivotalDimension_eq_fpSimple (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (d : Fin (Ground.rank C) → ℝ)
    (hreal : ∀ i, pivotalDimension C p (Ground.simples C i) = (d i : ℂ))
    (hpos : ∀ i, 0 < d i) : ∀ i, d i = Ground.fpSimple C i := by
  have hunit : d (Ground.unitIndex C) = 1 := by
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
