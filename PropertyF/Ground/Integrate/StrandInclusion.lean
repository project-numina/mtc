module
public import PropertyF.Ground.Fusion.Simples
public import PropertyF.Ground.Cabling.Strands

/-! Wire the split-unit and identity-strand constructions across workstreams. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u

/-- Adding identity strands injects the braid images of a simple object in a
complex braided fusion category. This is the bundle-free form of
`GeneratedInputs.strand_inclusion`. -/
theorem simple_strand_inclusion (C : BraidedFusionCategory.{v,u})
    (X : C.Obj) [Simple X] (n m : ℕ) (h : n ≤ m) :
    Nonempty (braidImage X n ↪ braidImage X m) := by
  obtain ⟨i, r, hr⟩ := unit_retract_leftDual_tensor X
  exact strand_inclusion_of_unit_retract X (ᘁX) i r hr n m h

end PropertyF.Ground
