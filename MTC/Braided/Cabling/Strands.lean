module
public import MTC.Braided.Definitions
public import Mathlib.CategoryTheory.Endomorphism

open MTC.Braided

/-!
# Adding strands to braid images

Adding an identity strand and faithfulness of tensoring from a unit retract.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Center.Trace
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
local notation "b" => MTC.Braided.braidGenerator

/-- Adding a strand on the left shifts the braid generator by one. -/
theorem braidGenerator_succ (X : C) {n : ℕ} (k : Fin (n + 1)) :
    (tensorLeft X).mapAut (tensorPower X (n + 2)) (b X n k) =
      b X (n + 1) k.succ :=
  Aut.ext <| Iso.ext <| by
    rcases k with ⟨k, hk⟩
    simp [Functor.mapAut, braidGenerator, tensorIso_hom, tensorLeft, id_tensorHom]

end MTC.Center.Trace

namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Add a single identity strand on the left. -/
def addLeftStrand (X : C) (n : ℕ) : braidImage X n →* braidImage X (n + 1) := by
  let f := (tensorLeft X).mapAut (tensorPower X (n + 2))
  have hf : ∀ a ∈ braidImage X n, f a ∈ braidImage X (n + 1) := by
    change braidImage X n ≤ (braidImage X (n + 1)).comap f
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    change f (braidGenerator X n i) ∈ braidImage X (n + 1)
    apply Subgroup.subset_closure
    exact ⟨i.succ, (MTC.Center.Trace.braidGenerator_succ X i).symm⟩
  exact (f.comp (braidImage X n).subtype).codRestrict _ (fun a => hf a a.property)

omit [BraidedCategory C] in
/-- If the unit is a retract of a tensor product with `X` on the right,
then tensoring on the left by `X` is faithful. -/
theorem tensorLeft_faithful_of_unit_retract {X Y : C}
    (i : 𝟙_ C ⟶ Y ⊗ X) (r : Y ⊗ X ⟶ 𝟙_ C) (h : i ≫ r = 𝟙 _) :
    Functor.Faithful (tensorLeft X) := ⟨fun {A B} f g hfg => by
  change X ◁ f = X ◁ g at hfg
  have recover (k : A ⟶ B) :
      (λ_ A).inv ≫ (i ▷ A) ≫ ((Y ⊗ X) ◁ k) ≫ (r ▷ B) ≫ (λ_ B).hom = k := by
    simp only [Category.assoc, ← whisker_exchange_assoc, ← comp_whiskerRight_assoc,
      h, id_whiskerRight, Category.id_comp, id_whiskerLeft, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [← recover f, tensor_whiskerLeft Y X f, hfg, ← tensor_whiskerLeft Y X g, recover g]⟩

end MTC.Braided
