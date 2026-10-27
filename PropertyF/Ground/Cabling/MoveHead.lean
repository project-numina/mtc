module
public import PropertyF.Ground.Cabling.Generated
public import PropertyF.Ground.Cabling.Strands
public import Mathlib.Tactic
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
@[expose] public noncomputable section
namespace PropertyF
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Abelian C] [MonoidalPreadditive C]

set_option backward.isDefEq.respectTransparency false in
lemma powerTensor_succ (X : C) (n : ℕ) :
    (tensorPowerTensorIso X (n+1) 1).hom =
      ((α_ X (tensorPower X n) (tensorPower X 1)) ≪≫
        (Iso.refl X ⊗ᵢ tensorPowerTensorIso X n 1)).hom := by
  simp [tensorPowerTensorIso]

/-- Move the first strand past a block of n strands, retaining the canonical
right-associated tensor power. -/
def moveHead (X : C) (n : ℕ) : Aut (tensorPower X (n+1)) := Aut.of (
  (β_ X (tensorPower X n)) ≪≫
    (Iso.refl (tensorPower X n) ⊗ᵢ (ρ_ X).symm) ≪≫ tensorPowerTensorIso X n 1)

def whiskerMoveHead (X : C) (n : ℕ) : Aut (tensorPower X (n + 2)) := by
  change Aut (X ⊗ tensorPower X (n + 1))
  exact Aut.of (Iso.refl X ⊗ᵢ (moveHead X n).asIso)

set_option backward.isDefEq.respectTransparency false in
/-- A block crossing moves the first strand past each successive strand. -/
theorem moveHead_succ (X : C) (n : ℕ) :
    moveHead X (n+1) = whiskerMoveHead X n * braidGenerator X n 0 := by
  apply Aut.ext
  apply Iso.ext
  have hg : braidGenerator X n 0 = Aut.of ((α_ X X (tensorPower X n)).symm ≪≫
    ((β_ X X) ⊗ᵢ Iso.refl _) ≪≫ α_ X X (tensorPower X n)) := by cases n <;> rfl
  rw [hg]
  simp only [whiskerMoveHead, moveHead, Aut.mul_asIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom]
  dsimp only [tensorPower, id, Aut.asIso, Iso.trans_hom, tensorIso_hom, Iso.refl_hom]
  rw [braiding_tensor_right_hom]
  rw [powerTensor_succ]
  simp only [Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Iso.symm_hom]
  monoidal
/-- Crossing the first strand past the empty block is the identity. -/
theorem moveHead_zero (X : C) : moveHead X 0 = 1 := by
  have hz : (tensorPowerTensorIso X 0 1).hom = (λ_ (tensorPower X 1)).hom := by
    rfl
  apply Aut.ext
  apply Iso.ext
  change ((β_ X (𝟙_ C)).hom ≫ (𝟙 (𝟙_ C) ⊗ₘ (ρ_ X).inv) ≫
    (tensorPowerTensorIso X 0 1).hom) = 𝟙 _
  rw [braiding_tensorUnit_right, hz]
  monoidal

/-- The head-to-tail block crossing belongs to the actual braid image. -/
theorem moveHead_mem_braidImage (X : C) : ∀ n : ℕ,
    moveHead X (n+1) ∈ braidImage X n := by
  intro n
  induction n with
  | zero =>
    rw [moveHead_succ]
    have h : whiskerMoveHead X 0 = 1 := by
      apply Aut.ext
      apply Iso.ext
      simp [whiskerMoveHead, moveHead_zero, tensorIso_hom, tensorPower]
    rw [h, one_mul]
    exact Subgroup.subset_closure (Set.mem_range_self _)
  | succ n ih =>
    rw [moveHead_succ]
    apply Subgroup.mul_mem
    · let b : braidImage X n := ⟨moveHead X (n + 1), ih⟩
      have h := (addLeftStrand X n b).property
      have heq : (addLeftStrand X n b).val = whiskerMoveHead X (n+1) := by
        apply Aut.ext
        apply Iso.ext
        change ((tensorLeft X).mapIso (moveHead X (n + 1)).asIso).hom =
          (Iso.refl X ⊗ᵢ (moveHead X (n+1)).asIso).hom
        simp [tensorLeft, tensorIso_hom, id_tensorHom]
      rw [heq] at h
      exact h
    · exact Subgroup.subset_closure (Set.mem_range_self _)
end PropertyF
