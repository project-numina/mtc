module
public import PropertyF.Ground.Modular.SMatrix

/-! The Galois-unit finite-image argument without `CenterInputs`. -/

@[expose] public noncomputable section
namespace PropertyF.Ground
universe v u

/-- If the common centralizer has integral dimensions, its double centralizer
contains a simple with the Galois-unit column. Any such simple has property F
when property F holds throughout the generated subcategory. The two label
sets and the categorical double-centralizer and finite-image results are
explicit interim premises, not assumptions in the target. -/
theorem propertyF_of_galois_column
    (Z : BraidedFusionCategory.{v,u}) (p : Dimensions.PivotalStructure (C := Z.Obj))
    (τ : ℂ ≃+* ℂ) (core generated : Set (Fin (rank Z)))
    (hIntegral : ∀ x ∈ core, ∃ z : ℤ, Modular.simpleDimension Z p x = z)
    (hDouble : ∀ y, (∀ x ∈ core, Modular.categoricalS Z p x y =
      Modular.simpleDimension Z p x * Modular.simpleDimension Z p y) → y ∈ generated)
    (hFinite : ∀ y ∈ generated, ObjectPropertyF (simples Z y))
    (y : Fin (rank Z))
    (hColumn : ∀ x, Modular.categoricalS Z p x y =
      Modular.simpleDimension Z p y * τ (Modular.simpleDimension Z p x)) :
    ObjectPropertyF (simples Z y) := by
  apply hFinite y
  apply hDouble y
  intro x hx
  obtain ⟨z, hz⟩ := hIntegral x hx
  rw [hColumn, hz, map_intCast, mul_comm]

end PropertyF.Ground
