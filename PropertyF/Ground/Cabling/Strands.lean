module
public import PropertyF.Definitions
public import Mathlib.CategoryTheory.Endomorphism

/-! Adding one strand on the left carries each braid generator to the next
one. The only additional input needed for injectivity is injectivity of the
actual tensor-left map on automorphisms. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Add a single identity strand on the left. -/
def addLeftStrand (X : C) (n : ℕ) : braidImage X n →* braidImage X (n + 1) := by
  let f := (tensorLeft X).mapAut (tensorPower X (n + 2))
  have hf : ∀ a ∈ braidImage X n, f a ∈ braidImage X (n + 1) := by
    change braidImage X n ≤ (braidImage X (n + 1)).comap f
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    have hi : f (braidGenerator X n i) = braidGenerator X (n + 1) i.succ := by
      apply Aut.ext
      apply Iso.ext
      rcases i with ⟨i, hi⟩
      simp [f, Functor.mapAut, braidGenerator, tensorIso_hom, tensorLeft, id_tensorHom]
    change f (braidGenerator X n i) ∈ braidImage X (n + 1)
    rw [hi]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  exact (f.comp (braidImage X n).subtype).codRestrict _ (fun a => hf a a.property)

/-- A faithful left-tensor functor gives an injective identity-strand map. -/
theorem addLeftStrand_injective (X : C) (n : ℕ) [Functor.Faithful (tensorLeft X)] :
    Function.Injective (addLeftStrand X n) := by
  intro a b h
  apply Subtype.ext
  apply Aut.ext
  apply Iso.ext
  apply (tensorLeft X).map_injective
  have h' := congrArg (fun x : braidImage X (n + 1) => x.val.asIso.hom) h
  exact h'

omit [BraidedCategory C] in
/-- If the unit is a retract of a tensor product with `X` on the right,
then tensoring on the left by `X` is faithful. -/
theorem tensorLeft_faithful_of_unit_retract (X Y : C)
    (i : 𝟙_ C ⟶ Y ⊗ X) (r : Y ⊗ X ⟶ 𝟙_ C) (h : i ≫ r = 𝟙 _) :
    Functor.Faithful (tensorLeft X) := by
  constructor
  intro A B f g hfg
  have hY : Y ◁ (X ◁ f) = Y ◁ (X ◁ g) := congrArg (fun k => Y ◁ k) hfg
  have hYX : (Y ⊗ X) ◁ f = (Y ⊗ X) ◁ g := by
    simp only [tensor_whiskerLeft, hY]
  have recover (k : A ⟶ B) :
      (λ_ A).inv ≫ (i ▷ A) ≫ ((Y ⊗ X) ◁ k) ≫ (r ▷ B) ≫ (λ_ B).hom = k := by
    simp only [Category.assoc, ← whisker_exchange_assoc, ← comp_whiskerRight_assoc,
      h, id_whiskerRight, Category.id_comp, id_whiskerLeft, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
  rw [← recover f, hYX, recover g]

/-- Repeated identity strands embed every earlier braid image. -/
def strandEmbedding (X : C) [Functor.Faithful (tensorLeft X)] (n : ℕ) :
    ∀ k : ℕ, braidImage X n ↪ braidImage X (n + k)
  | 0 => Function.Embedding.refl _
  | k + 1 => (strandEmbedding X n k).trans
      ⟨addLeftStrand X (n + k), addLeftStrand_injective X (n + k)⟩

/-- The embedding in the strand-inclusion field, assuming faithful tensoring. -/
theorem strand_inclusion_of_faithful_tensor (X : C)
    [Functor.Faithful (tensorLeft X)] (n m : ℕ) (h : n ≤ m) :
    Nonempty (braidImage X n ↪ braidImage X m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨strandEmbedding X n k⟩

/-- Strand inclusion from a split copy of the unit in `Y ⊗ X`. -/
theorem strand_inclusion_of_unit_retract (X Y : C)
    (i : 𝟙_ C ⟶ Y ⊗ X) (r : Y ⊗ X ⟶ 𝟙_ C) (h : i ≫ r = 𝟙 _)
    (n m : ℕ) (hnm : n ≤ m) : Nonempty (braidImage X n ↪ braidImage X m) := by
  let _ : Functor.Faithful (tensorLeft X) := tensorLeft_faithful_of_unit_retract X Y i r h
  exact strand_inclusion_of_faithful_tensor X n m hnm

end PropertyF
