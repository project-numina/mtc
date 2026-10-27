module
public import PropertyF.Ground.Integrate.CenterBundle

/-! Assembly of the ground fusion interface from centre semisimplicity. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreBundle
universe v u

variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)]

/-- Finite semisimplicity is the remaining fusion property: Hom finiteness and
simplicity of the unit follow from the underlying fusion category. -/
theorem fusionOfFiniteSemisimple
    (h : ∃ (n : ℕ) (S : Fin n → CategoryTheory.Center C.Obj),
      (∀ i, Simple (S i)) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      (∀ X, ∃ m : Fin n → ℕ,
        Nonempty (X ≅ ⨁ (fun p : Σ i, Fin (m i) => S p.1)))) :
    IsFusionCategory (CategoryTheory.Center C.Obj) where
  hom_finite X Y := by
    letI := IsFusionCategory.hom_finite (C := C.Obj) X.1 Y.1
    exact Centre.finiteDimensional_hom ℂ X Y
  unit_simple := by
    letI := IsFusionCategory.unit_simple (C := C.Obj)
    exact Centre.centerUnitSimple
  finite_semisimple := h

end PropertyF.Ground.CentreBundle
