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

/-- The split image's dimension is the normalized signed sum of the traces
of the operators in the action. -/
theorem alternatingProjector_dimension_formula (X : C) (n : ℕ)
    [Invertible (Fintype.card (Equiv.Perm (Fin n)) : ℂ)]
    (ρ : Equiv.Perm (Fin n) →* End X)
    (p : PropertyF.Ground.Dimensions.PivotalStructure (C := C)) :
    ∃ Y : C, p.rightTrace (𝟙 Y) =
      ⅟(Fintype.card (Equiv.Perm (Fin n)) : ℂ) •
        ∑ σ : Equiv.Perm (Fin n),
          (permutationSign ℂ n σ : ℂ) • p.rightTrace (ρ σ).asHom := by
  obtain ⟨Y, hY⟩ := alternatingProjector_trace X n ρ p
  refine ⟨Y, ?_⟩
  rw [← hY, alternatingProjector_eq_sum]
  simp only [End.smul_asHom, End.sum_asHom, p.rightTrace_smul]
  congr 1
  have h := map_sum (PropertyF.Ground.Dimensions.rightTraceLinear p X)
      (fun σ : Equiv.Perm (Fin n) => (permutationSign ℂ n σ : ℂ) • (ρ σ).asHom) Finset.univ
  change p.rightTrace (∑ σ : Equiv.Perm (Fin n),
      (permutationSign ℂ n σ : ℂ) • (ρ σ).asHom) =
    ∑ σ : Equiv.Perm (Fin n),
      p.rightTrace ((permutationSign ℂ n σ : ℂ) • (ρ σ).asHom) at h
  simpa only [p.rightTrace_smul] using h

end PropertyF.Ground.Centre
