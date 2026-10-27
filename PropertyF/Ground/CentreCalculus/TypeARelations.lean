module
public import PropertyF.Ground.CentreCalculus.BraidRelations
public import PropertyF.Ground.CentreCalculus.PureSquares

/-! Type-A relations for the actual tensor-power braid action. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Adjacent Yang–Baxter and distant commutation words in the free group. -/
def braidRelations (n : ℕ) : Set (BraidWords n) :=
  {w | (∃ i j : Fin (n + 1), i.val + 1 = j.val ∧
      w = (FreeGroup.of i * FreeGroup.of j * FreeGroup.of i) *
        (FreeGroup.of j * FreeGroup.of i * FreeGroup.of j)⁻¹) ∨
    (∃ i j : Fin (n + 1), i.val + 1 < j.val ∧
      w = (FreeGroup.of i * FreeGroup.of j) * (FreeGroup.of j * FreeGroup.of i)⁻¹)}

/-- The full normal closure of the type-A braid relations acts trivially. -/
theorem braidRelations_action_trivial (X : C) (n : ℕ) :
    Subgroup.normalClosure (braidRelations n) ≤
      (FreeGroup.lift (braidGenerator X n)).ker := by
  apply Subgroup.normalClosure_le_normal
  intro w hw
  apply MonoidHom.mem_ker.mpr
  rcases hw with h | h
  · obtain ⟨i, j, hij, rfl⟩ := h
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one]
    cases n with
    | zero => have hj := j.isLt; omega
    | succ n =>
      let k : Fin (n + 1) := ⟨i.val, by have hj := j.isLt; omega⟩
      have hi : k.castSucc = i := Fin.ext rfl
      have hj : k.succ = j := Fin.ext hij
      simpa only [hi, hj] using adjacent_braid_relation X n k
  · obtain ⟨i, j, hij, rfl⟩ := h
    simp only [map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one]
    exact distant_braid_commute X n i j hij

/-- All standard symmetric-group relation words act trivially for a
self-transparent object. -/
theorem typeARelations_action_trivial (X : C)
    (hX : (β_ X X).hom ≫ (β_ X X).hom = 𝟙 (X ⊗ X)) (n : ℕ) :
    Subgroup.normalClosure (squareRelations n ∪ braidRelations n) ≤
      (FreeGroup.lift (braidGenerator X n)).ker := by
  apply Subgroup.normalClosure_le_normal
  intro w hw
  rcases hw with hw | hw
  · exact squareRelations_action_trivial X hX n (Subgroup.subset_normalClosure hw)
  · exact braidRelations_action_trivial X n (Subgroup.subset_normalClosure hw)

/-- Every defining type-A relation also has trivial strand permutation. -/
theorem typeARelations_permutation_trivial (n : ℕ) :
    Subgroup.normalClosure (squareRelations n ∪ braidRelations n) ≤
      (strandPermutation n).ker := by
  apply Subgroup.normalClosure_le_normal
  intro w hw
  apply MonoidHom.mem_ker.mpr
  rcases hw with hw | hw
  · obtain ⟨i, rfl⟩ := hw
    simp only [strandPermutation, map_pow, FreeGroup.lift_apply_of, pow_two]
    exact Equiv.swap_mul_self _ _
  · rcases hw with ⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩
    · simp only [strandPermutation, map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one]
      have hm : i.succ = j.castSucc := Fin.ext hij
      rw [← hm]
      have hxy : i.castSucc ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this
      have hxz : i.castSucc ≠ j.succ := by intro h; have := congrArg Fin.val h; simp at this; omega
      have hzy : j.succ ≠ i.succ := by intro h; have := congrArg Fin.val h; simp at this; omega
      have hzX : j.succ ≠ i.castSucc := hxz.symm
      have h₁ := Equiv.swap_mul_swap_mul_swap hxy hxz
      have h₂ := Equiv.swap_mul_swap_mul_swap hzy hzX
      rw [Equiv.swap_comm i.castSucc j.succ] at h₂
      simpa only [Equiv.swap_comm] using h₂.trans h₁.symm
    · simp only [strandPermutation, map_mul, map_inv, FreeGroup.lift_apply_of, mul_inv_eq_one]
      have hdis : [i.castSucc, i.succ, j.castSucc, j.succ].Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil, List.nodup_nil,
          not_or, and_true, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
        simp only [not_false_eq_true, and_true]
        repeat' constructor <;> omega
      exact (Equiv.Perm.disjoint_swap_swap hdis).commute.eq

end PropertyF.Ground.CentreCalculus
