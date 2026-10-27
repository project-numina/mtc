module
public import PropertyF.Definitions
public import Mathlib.GroupTheory.Perm.Sign

/-! A symmetric-group action with the expected adjacent swaps gives a finite
braid image. Constructing such an action remains a separate problem. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Centre

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- An action of the finite symmetric group implementing each adjacent
braiding contains the entire braid image. -/
theorem braidImage_le_symmetricGroup_range (X : C) (n : ℕ)
    (ρ : Equiv.Perm (Fin (n + 2)) →* Aut (tensorPower X (n + 2)))
    (hρ : ∀ i : Fin (n + 1),
      ρ (Equiv.swap i.castSucc i.succ) = braidGenerator X n i) :
    braidImage X n ≤ ρ.range := by
  apply (Subgroup.closure_le ρ.range).2
  rintro _ ⟨i, rfl⟩
  exact ⟨Equiv.swap i.castSucc i.succ, hρ i⟩

/-- Every braid image is finite if it is realized by such a symmetric-group action. -/
theorem objectPropertyF_of_symmetricGroup_actions (X : C)
    (h : ∀ n, ∃ ρ : Equiv.Perm (Fin (n + 2)) →* Aut (tensorPower X (n + 2)),
      ∀ i : Fin (n + 1), ρ (Equiv.swap i.castSucc i.succ) = braidGenerator X n i) :
    ObjectPropertyF X := by
  intro n
  obtain ⟨ρ, hρ⟩ := h n
  have hrange : Finite ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  let f : braidImage X n → ρ.range := fun x => ⟨x.1, braidImage_le_symmetricGroup_range X n ρ hρ x.2⟩
  exact Finite.of_injective f (fun x y hxy => Subtype.ext
    (congrArg (fun z : ρ.range => z.1) hxy))

end PropertyF.Ground.Centre
