module
public import MTC.PropertyF.Pivotal.Galois
public import MTC.PropertyF.Pivotal.Nondegenerate

/-! # Categorical S matrices under scalar twisting -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Fusion MTC.Modular MTC.PropertyF.Reduction MTC.CategoryTheory.Dimensions
namespace MTC.PropertyF.Pivotal
universe v u
set_option backward.isDefEq.respectTransparency false
variable (C : BraidedFusionCategory.{v,u}) (σ : ℂ ≃+* ℂ)
variable (p : PivotalStructure (C := C.Obj))
local notation "Cσ" => ScalarTwist.category C σ
local notation "pσ" => ScalarTwist.pivotal C σ p

/-- On fixed objects the categorical S entry is transformed by the field
automorphism. -/
theorem SEntry_scalarTwist (X Y : C.Obj) :
    unitScalarEquiv Cσ (SEntry pσ X Y) = σ (unitScalarEquiv C (SEntry p X Y)) := by
  exact ScalarTwist.rightTrace_twist C σ p (doubleBraiding X Y)

/-- Simples can be relabelled so that the S matrix is carried entrywise by
the scalar automorphism. -/
theorem categoricalS_scalarTwist_labels :
    ∃ e : Fin (rank C) ≃ Fin (rank Cσ), ∀ i j,
      categoricalS Cσ pσ (e i) (e j) = σ (categoricalS C p i j) := by
  obtain ⟨e, he⟩ := simpleLabels_equiv C Cσ (CategoryTheory.Equivalence.refl)
  refine ⟨e, fun i j ↦ ?_⟩
  have hi := (he i).some
  have hj := (he j).some
  change unitScalarEquiv Cσ (SEntry pσ (simples Cσ (e i)) (simples Cσ (e j))) = _
  rw [← SEntry_iso_right pσ _ hj, SEntry_symmetric pσ,
    ← SEntry_iso_right pσ _ hi, SEntry_symmetric pσ]
  exact SEntry_scalarTwist C σ p (simples C i) (simples C j)

/-- Invertibility of the actual pivotal S matrix survives scalar twisting. -/
theorem categoricalS_det_ne_zero_scalarTwist (hdet : (categoricalS C p).det ≠ 0) :
    (categoricalS Cσ pσ).det ≠ 0 := by
  obtain ⟨e, he⟩ := categoricalS_scalarTwist_labels C σ p
  have hm : (categoricalS Cσ pσ).submatrix e e = (categoricalS C p).map σ := by
    ext i j
    exact he i j
  intro hz
  have h := congrArg Matrix.det hm
  rw [Matrix.det_submatrix_equiv_self, hz] at h
  have hmap : ((categoricalS C p).map σ).det = σ ((categoricalS C p).det) := by
    exact (RingHom.map_det σ.toRingHom _).symm
  rw [hmap] at h
  exact hdet (σ.injective (by simpa using h.symm))

/-- Property F and an invertible pivotal S matrix make every scalar twist
pseudo-unitary. -/
theorem scalarTwists_pseudoUnitary_of_invertibleS_of_propertyF
    (hdet : (categoricalS C p).det ≠ 0) (hF : MTC.Braided.HasPropertyF C.Obj)
    (τ : ℂ ≃+* ℂ) : PseudoUnitary (ScalarTwist.category C τ) :=
  pseudoUnitary_of_invertibleS_of_propertyF (ScalarTwist.category C τ)
    (ScalarTwist.pivotal C τ p) (categoricalS_det_ne_zero_scalarTwist C τ p hdet)
    (Modular.conjugate_propertyF (scalarTwistGaloisConjugate C τ) hF)

/-- Property F implies weak integrality when the actual pivotal S matrix is
invertible, without assuming sphericality or a pseudo-unitary conjugate. -/
theorem weaklyIntegral_of_invertibleS_of_propertyF
    (hdet : (categoricalS C p).det ≠ 0) (hF : MTC.Braided.HasPropertyF C.Obj) :
    MTC.Braided.WeaklyIntegral (globalFPDimension C) :=
  weaklyIntegral_of_all_scalarTwists_pseudoUnitary C
    (scalarTwists_pseudoUnitary_of_invertibleS_of_propertyF C p hdet hF)

end MTC.PropertyF.Pivotal
