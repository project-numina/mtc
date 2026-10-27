module
public import PropertyF.Ground.CentreRigid.Evaluation
public import PropertyF.Ground.CentreInduction.ActualFusion

/-! Bundle the actual centre using the constructed rigid instance. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreBundle
universe v u

/-- The actual centre is fusion once its finite semisimple decomposition is
constructed; rigidity, finite Hom spaces and a simple unit are supplied. -/
@[instance_reducible] def canonicalFusionOfFiniteSemisimple
    (C : BraidedFusionCategory.{v,u})
    (h : ∃ (n : ℕ) (S : Fin n → Center C.Obj),
      (∀ i, Simple (S i)) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      (∀ X, ∃ m : Fin n → ℕ,
        Nonempty (X ≅ ⨁ (fun p : Σ i, Fin (m i) => S p.1)))) :
    letI := CentreRigid.rigidCenter (C := C.Obj)
    IsFusionCategory (Center C.Obj) := by
  letI := CentreRigid.rigidCenter (C := C.Obj)
  exact fusionOfFiniteSemisimple C h

/-- Bundle the actual centre with its canonical rigid instance and a supplied
finite semisimple decomposition. -/
def bundledOfFiniteSemisimple (C : BraidedFusionCategory.{v,u})
    (h : ∃ (n : ℕ) (S : Fin n → Center C.Obj),
      (∀ i, Simple (S i)) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      (∀ X, ∃ m : Fin n → ℕ,
        Nonempty (X ≅ ⨁ (fun p : Σ i, Fin (m i) => S p.1)))) :
    BraidedFusionCategory.{v,max u v} := by
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := canonicalFusionOfFiniteSemisimple C h
  exact Integrate.bundledCenter C

/-- The assembled centre has the expected FP square, using the constructed
induction adjunction. Finite semisimplicity is the sole remaining premise. -/
theorem globalFPDimension_bundledOfFiniteSemisimple
    (C : BraidedFusionCategory.{v,u})
    (h : ∃ (n : ℕ) (S : Fin n → Center C.Obj),
      (∀ i, Simple (S i)) ∧
      (∀ i j, Nonempty (S i ≅ S j) → i = j) ∧
      (∀ X, ∃ m : Fin n → ℕ,
        Nonempty (X ≅ ⨁ (fun p : Σ i, Fin (m i) => S p.1)))) :
    globalFPDimension (bundledOfFiniteSemisimple C h) = globalFPDimension C ^ 2 := by
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := canonicalFusionOfFiniteSemisimple C h
  exact CentreInduction.globalFPDimension_square_of_actual_induction C

end PropertyF.Ground.CentreBundle
