module
public import PropertyF.Ground.Target

/-!
# Invertible simples and dimension one

Status: solved
Source: Bruillard–Ng–Rowell–Wang, arXiv:1310.7050, Remark 2.2.
Declaration: MTC.Conjectures.Fusion.invertible_iff_dimension_one

A simple object is invertible exactly when its FP dimension is one. This
identifies the pointed part of a fusion category using numerical data. The
statement is restricted to braided categories and uses the existing right
dual. Equivalence of the frozen spectral-radius definition and the usual FP
dimension remains to be proved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Conjectures.Fusion
open PropertyF.Ground
universe v u

/-- A simple is invertible precisely when its FP dimension equals one. -/
theorem invertible_iff_dimension_one (C : BraidedFusionCategory.{v,u})
    (i : Fin (rank C)) :
    Nonempty (simples C i ⊗ (simples C i)ᘁ ≅ 𝟙_ C.Obj) ↔ fpSimple C i = 1 := by
  sorry

end MTC.Conjectures.Fusion
