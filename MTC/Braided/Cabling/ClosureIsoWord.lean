module
public import MTC.Braided.Cabling.ClosureInsertion

/-! Categorical transport of adjacent braid words along object isomorphisms. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Tensor powers carry an object isomorphism to an isomorphism. -/
def tensorPowerMapIso {X Y : C} (e : X ≅ Y) (n : ℕ) : tensorPower X n ≅ tensorPower Y n where
  hom := tensorPowerMap e.hom n
  inv := tensorPowerMap e.inv n
  hom_inv_id := by rw [← tensorPowerMap_comp, e.hom_inv_id, tensorPowerMap_id]
  inv_hom_id := by rw [← tensorPowerMap_comp, e.inv_hom_id, tensorPowerMap_id]

/-- Transporting a generator along a tensor-power isomorphism preserves its index. -/
theorem tensorPowerMapIso_conj_generator {X Y : C} (e : X ≅ Y) (n : ℕ)
    (i : Fin (n+1)) :
    (tensorPowerMapIso e (n+2)).conjAut (braidGenerator X n i) = braidGenerator Y n i := by
  apply Aut.ext
  apply Iso.ext
  change (tensorPowerMap e.inv (n+2)) ≫ (braidGenerator X n i).asIso.hom ≫
    tensorPowerMap e.hom (n+2) = (braidGenerator Y n i).asIso.hom
  rw [braidGenerator_map_natural e.hom n i]
  simp [← Category.assoc, ← tensorPowerMap_comp]

/-- In particular a width-one block generator is the corresponding adjacent
original-strand generator after the tensor-power unitor isomorphism. -/
theorem widthOne_generator_word (X : C) (n : ℕ) (i : Fin (n+1)) :
    (tensorPowerMapIso (ρ_ X) (n+2)).conjAut
      (braidGenerator (tensorPower X 1) n i) =
        (braidWordAction X n (FreeGroup.of i)).val := by
  change (tensorPowerMapIso (ρ_ X) (n+2)).conjAut (braidGenerator (X ⊗ 𝟙_ C) n i) = _
  rw [tensorPowerMapIso_conj_generator]
  simp [braidWordAction]

end MTC.Braided
