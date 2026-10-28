module
public import PropertyF.Ground.Target

/-!
# FP dimension is a fusion-ring character

Status: solved
Source: Etingof–Nikshych–Ostrik, arXiv:math/0203060, Theorem 8.6.
Declaration: MTC.Conjectures.Fusion.fusion_dimension_character

The FP dimension of a tensor product is the product of dimensions. Written
on simple representatives, this gives a common positive eigenvector for all
fusion matrices. It is a strong consistency check for proposed fusion rules
and dimensions. The equivalence between the frozen spectral-radius definition
and the usual FP dimension needs proof in Lean.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Conjectures.Fusion
open PropertyF.Ground
universe v u

/-- The simple dimensions are a character of the fusion rules. -/
theorem fusion_dimension_character (C : BraidedFusionCategory.{v,u})
    (i j : Fin (rank C)) :
    fpSimple C i * fpSimple C j =
      ∑ k, (Module.finrank ℂ (simples C k ⟶ simples C i ⊗ simples C j) : ℝ) *
        fpSimple C k := by
  sorry

end MTC.Conjectures.Fusion
