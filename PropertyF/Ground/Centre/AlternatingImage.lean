module
public import PropertyF.Ground.Centre.Averaging
public import PropertyF.Ground.Dimensions.BiproductTrace
public import Mathlib.CategoryTheory.Idempotents.Basic

/-! Splitting the alternating projector and identifying its pivotal trace. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Centre

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [IsIdempotentComplete C]

/-- A symmetric-group action on an object has a split alternating projector. -/
theorem alternatingProjector_splits (X : C) (n : ℕ)
    [Invertible (Fintype.card (Equiv.Perm (Fin n)) : ℂ)]
    (ρ : Equiv.Perm (Fin n) →* End X) :
    ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y),
      i ≫ r = 𝟙 Y ∧ r ≫ i = (alternatingProjector (k := ℂ) n ρ).asHom := by
  apply IsIdempotentComplete.idempotents_split
  simpa only [End.mul_asHom] using congrArg End.asHom (alternatingProjector_idempotent (k := ℂ) n ρ)

variable [MonoidalCategory C] [RightRigidCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
/-- The trace of the alternating projector is the dimension of its split image. -/
theorem alternatingProjector_trace (X : C) (n : ℕ)
    [Invertible (Fintype.card (Equiv.Perm (Fin n)) : ℂ)]
    (ρ : Equiv.Perm (Fin n) →* End X)
    (p : PropertyF.Ground.Dimensions.PivotalStructure (C := C)) :
    ∃ Y : C, p.rightTrace ((alternatingProjector (k := ℂ) n ρ).asHom) = p.rightTrace (𝟙 Y) := by
  obtain ⟨Y, i, r, hir, hri⟩ := alternatingProjector_splits X n ρ
  refine ⟨Y, ?_⟩
  rw [← hri, p.rightTrace_cyclic, hir]

end PropertyF.Ground.Centre
