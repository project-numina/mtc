module
public import MTC.Braided.Cabling.ClosureFlattenCoherence

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

theorem iso_heq_iff_transport {A B D : C} (f : A ≅ B) (g : A ≅ D) (h : B = D) :
    f ≍ g ↔ f ≪≫ eqToIso h = g := by
  cases h
  simp

theorem blockStrandCount_sum (k p q : ℕ) :
    blockStrandCount k (strandSum p q) =
      strandSum (blockStrandCount k p) (blockStrandCount k q) := by
  simp [blockStrandCount_eq_mul, strandSum_eq_add, Nat.add_mul]


/-- Reindexing the right input of a join commutes with joining. -/
theorem joinPowerIso_transport_right (X : C) (a : ℕ) {b c : ℕ} (h : b = c) :
    (Iso.refl (tensorPower X a) ⊗ᵢ powerIndexIso X h) ≪≫ joinPowerIso X a c =
      joinPowerIso X a b ≪≫ powerIndexIso X (congrArg (strandSum a) h) := by
  cases h
  apply Iso.ext
  simp [powerIndexIso]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
 theorem flattenBlocksRecursive_concat_heq (X : C) (k : ℕ) : ∀ p q : ℕ,
    flattenBlocksRecursive X k (strandSum p q) ≍
      (joinPowerIso (tensorPower X k) p q).symm ≪≫
        (flattenBlocksRecursive X k p ⊗ᵢ flattenBlocksRecursive X k q) ≪≫
        joinPowerIso X (blockStrandCount k p) (blockStrandCount k q)
  | 0, q => by
    simp only [strandSum, joinPowerIso, flattenBlocksRecursive, blockStrandCount, tensorPower]
    apply heq_of_eq
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom, id_tensorHom]
    monoidal
  | p+1, q => by
    have ih := flattenBlocksRecursive_concat_heq X k p q
    simp only [strandSum, flattenBlocksRecursive, blockStrandCount, joinPowerIso]
    rw [iso_heq_iff_transport _ _ (congrArg (tensorPower X) (by
      simp only [strandSum, blockStrandCount, blockStrandCount_sum, strandSum_assoc]))]
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
      id_tensorHom, tensorHom_id, eqToIso.hom, Category.assoc]
    rw [iso_heq_iff_transport _ _ (congrArg (tensorPower X) (blockStrandCount_sum k p q))] at ih
    have hi := congrArg Iso.hom ih
    simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, eqToIso.hom, Category.assoc] at hi
    have hj := congrArg Iso.hom (joinPowerIso_assoc X k (blockStrandCount k p) (blockStrandCount k q))
    simp only [Iso.trans_hom, Iso.refl_hom, tensorIso_hom, tensorHom_id, id_tensorHom,
      powerIndexIso, eqToIso.hom, Category.assoc] at hj
    have ht := congrArg Iso.hom (joinPowerIso_transport_right X k (blockStrandCount_sum k p q))
    simp only [Iso.trans_hom, Iso.refl_hom, tensorIso_hom, id_tensorHom,
      powerIndexIso, eqToIso.hom, Category.assoc] at ht
    dsimp only [Iso.trans_inv, tensorIso_inv, Iso.refl_inv]
    monoidal_nf
    simp only [Iso.trans_hom, tensorIso_hom, whiskerLeftIso_hom, whiskerRightIso_hom, Iso.refl_hom,
      whiskerLeft_id, id_whiskerRight, id_tensorHom, tensorHom_id, Iso.symm_hom, Iso.inv_hom_id_assoc,
      Category.id_comp, Category.comp_id, Category.assoc]
    apply (cancel_mono (eqToHom (congrArg (tensorPower X)
      (strandSum_assoc k (blockStrandCount k p) (blockStrandCount k q))))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [← ht]
    simp only [← Category.assoc, ← whiskerLeft_comp]
    rw [hi]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [hj]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

