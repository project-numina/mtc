module
public import MTC.PropertyF.Pivotal.Nondegeneracy

open MTC.Fusion MTC.Modular MTC.CategoryTheory.Dimensions

/-! Transparency gives numerical centrality for arbitrary pivotal structures. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.PropertyF.Pivotal
universe v u
variable (C : BraidedFusionCategory.{v,u}) (p : PivotalStructure (C := C.Obj))

/-- A transparent simple label satisfies the actual numerical S test. -/
theorem categoricalS_eq_dimension_product_of_transparent
    (k : Fin (rank C)) (hk : MTC.Center.Transparent (simples C k))
    (i : Fin (rank C)) : categoricalS C p i k =
      simpleDimension C p i * simpleDimension C p k := by
  rw [categoricalS_symmetric C p, categoricalS, SEntry]
  rw [show doubleBraiding (simples C k) (simples C i) = 𝟙 _ from hk _]
  rw [← unitScalar_eq_equiv]
  change pivotalDimension C p (simples C k ⊗ simples C i) = _
  rw [pivotalDimension_tensor]
  exact mul_comm _ _

/-- Invertibility of the actual pivotal S matrix implies that every
transparent simple label is the unit label. -/
theorem transparent_label_eq_unit_of_categoricalS_det_ne_zero
    (hdet : (categoricalS C p).det ≠ 0) (k : Fin (rank C))
    (hk : MTC.Center.Transparent (simples C k)) : k = unitIndex C := by
  apply normalized_columns_injective (simpleDimension_ne_zero C p) hdet
  funext i
  simp only [categoricalS_unit, simpleDimension_unit, div_one,
    categoricalS_eq_dimension_product_of_transparent C p k hk i]
  exact mul_div_cancel_right₀ _ (simpleDimension_ne_zero C p k)

end MTC.PropertyF.Pivotal
end
