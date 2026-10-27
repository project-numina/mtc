module
public import PropertyF.Ground.Integrate.Representatives
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.CategoryTheory.Monoidal.Linear

/-! Spectral FP dimensions are independent of the complete simple presentation. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground
universe v u
variable (C : BraidedFusionCategory.{v,u})

/-- A fusion matrix formed from an arbitrary list of objects. -/
def presentationMatrix {n : ℕ} (S : Fin n → C.Obj) (i : Fin n) :
    Matrix (Fin n) (Fin n) ℂ := fun k j =>
  (Module.finrank ℂ (S k ⟶ S i ⊗ S j) : ℂ)

/-- Object isomorphisms identify the two fusion matrices after reindexing. -/
theorem presentationMatrix_reindex {n : ℕ} (S : Fin n → C.Obj)
    (e : Fin n ≃ Fin (rank C))
    (he : ∀ i, Nonempty (S i ≅ simples C (e i))) (i : Fin n) :
    Matrix.reindexAlgEquiv ℂ ℂ e (presentationMatrix C S i) = fusionMatrix C (e i) := by
  classical
  ext k j
  let a := (he i).some
  let b := (he (e.symm j)).some
  let c := (he (e.symm k)).some
  have hc : Module.finrank ℂ (S (e.symm k) ⟶ S i ⊗ S (e.symm j)) =
      Module.finrank ℂ (simples C (e (e.symm k)) ⟶
        simples C (e i) ⊗ simples C (e (e.symm j))) :=
    (CategoryTheory.Linear.homCongr ℂ c (a ⊗ᵢ b)).finrank_eq
  rw [e.apply_symm_apply, e.apply_symm_apply] at hc
  simpa [presentationMatrix, fusionMatrix, Matrix.coe_reindexAlgEquiv,
    Matrix.reindex_apply, Matrix.submatrix_apply] using congrArg (fun x : ℕ => (x : ℂ)) hc

/-- The FP dimension of a simple is the same in any such presentation. -/
theorem fpSimple_presentation {n : ℕ} (S : Fin n → C.Obj)
    (e : Fin n ≃ Fin (rank C))
    (he : ∀ i, Nonempty (S i ≅ simples C (e i))) (i : Fin n) :
    (spectralRadius ℂ (presentationMatrix C S i)).toReal = fpSimple C (e i) := by
  have h := presentationMatrix_reindex C S e he i
  unfold fpSimple
  rw [← h, spectralRadius_eq_of_unital, spectralRadius_eq_of_unital, AlgEquiv.spectrum_eq]

/-- The target global FP dimension can be computed from any complete,
pairwise nonisomorphic finite list of simple objects. -/
theorem globalFPDimension_presentation {n : ℕ} (S : Fin n → C.Obj)
    (hSimple : ∀ i, Simple (S i))
    (hInjective : ∀ i j, Nonempty (S i ≅ S j) → i = j)
    (hCover : ∀ j, ∃ i, Nonempty (S i ≅ simples C j)) :
    (∑ i, ((spectralRadius ℂ (presentationMatrix C S i)).toReal) ^ 2) =
      globalFPDimension C := by
  obtain ⟨e, he⟩ := simple_presentation_equiv C S hSimple hInjective hCover
  unfold globalFPDimension
  calc
    _ = ∑ i, (fpSimple C (e i)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [fpSimple_presentation C S e he i]
    _ = _ := e.sum_comp (fun j => (fpSimple C j) ^ 2)

end PropertyF.Ground
