module
public import MTC.Braided.Cabling.ClosureMergeCommon

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Merging a single leading strand is the inverse of splitting it off. -/
theorem sweepBlockMerge_zero_eq_split (X : C) : ∀ r : ℕ,
    sweepBlockMerge X 0 r = (sweepBlockSplit X r 0).symm ≪≫
      powerIndexIso X (by omega : r+0+2 = 0+r+2)
  | 0 => by
    apply Iso.ext
    simp [sweepBlockMerge, sweepBlockSplit, powerIndexIso, Trace.appendIso,
      tensorPower, Category.assoc]
  | r+1 => by
    rw [sweepBlockMerge_succ_prepend, insertRightPowerIso_eq_merge, sweepBlockMerge_zero_eq_split X r]
    apply Iso.ext
    simp only [sweepBlockSplit, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
      Iso.refl_hom, tensorHom_id, id_tensorHom]
    simp only [powerIndexIso, eqToIso.hom, Nat.zero_add, Nat.add_zero, eqToHom_refl,
      Category.comp_id, Category.id_comp, whiskerLeft_id]
    simp only [whiskerLeft_comp, whiskerLeft_eqToHom, tensorIso_inv, Iso.symm_inv,
      Iso.refl_inv, tensorHom_id, Category.assoc]
    simp only [← Category.assoc]
    congr 1
    simp [Trace.appendIso, tensorPower]
    monoidal

set_option backward.isDefEq.respectTransparency false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Merging blocks is the inverse of splitting them, with the commutativity
of the two strand counts made explicit. -/
theorem sweepBlockMerge_eq_split (X : C) : ∀ s r : ℕ,
    sweepBlockMerge X s r = (sweepBlockSplit X r s).symm ≪≫
      powerIndexIso X (by omega : r+s+2 = s+r+2)
  | 0, r => sweepBlockMerge_zero_eq_split X r
  | s+1, r => by
    rw [sweepBlockMerge_succ_left_recursive, sweepBlockMerge_eq_split X s r]
    apply Iso.ext
    simp only [sweepBlockSplit, powerIndexIso, Iso.trans_hom, Iso.symm_hom,
      tensorIso_hom, Iso.refl_hom, tensorHom_id, id_tensorHom, whiskerLeft_comp,
      whiskerLeft_eqToHom, Category.assoc]
    simp only [Iso.trans_inv, Iso.symm_inv, tensorIso_inv, Iso.refl_inv,
      id_tensorHom, eqToIso.hom, whiskerLeft_eqToHom, eqToHom_trans_assoc]
    simp only [← Category.assoc, eqToHom_trans]

end MTC.Braided
