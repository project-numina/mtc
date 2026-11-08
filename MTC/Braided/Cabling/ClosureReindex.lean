module
public import MTC.Braided.Cabling.ClosureLocalFlatten
public import MTC.Braided.Cabling.ClosureBlockContext

/-! Transport actual generators and local flattenings to common indices. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- Reindexing the number of strands transports each actual generator and its
finite index by the same equality. -/
theorem braidGenerator_reindex (X : C) {n m : ℕ} (h : n = m) (i : Fin (n+1)) :
    (powerIndexIso X (congrArg (fun q => q+2) h)).conjAut (braidGenerator X n i) =
      braidGenerator X m (Fin.cast (congrArg (fun q => q+1) h) i) := by
  subst m
  apply Aut.ext
  apply Iso.ext
  simp [powerIndexIso, Iso.conjAut_hom, Iso.conj_apply_asHom]

/-- The position `p` among `p+q+2` blocks. -/
def localBlockPosition (p q : ℕ) : Fin (q+p+1) := ⟨p, by omega⟩

/-- Transport a position-adapted flattening to common source and target
strand counts. -/
def localBlockFlattenCommon (X : C) (k p q : ℕ) :
    tensorPower (tensorPower X (k+1)) ((q+p)+2) ≅
      tensorPower X ((((q+p)+2)*(k+1)-2)+2) :=
  powerIndexIso (tensorPower X (k+1)) (by omega : (q+p)+2 = ((0+q)+p)+2) ≪≫
    localBlockFlatten X k p q ≪≫
    powerIndexIso X (by
      have h := blockGenerator_index k (q+p) (localBlockPosition p q)
      have hpos : (localBlockPosition p q).val = p := rfl
      have hsub : (q+p)-p = q := by omega
      simp only [hpos, hsub] at h
      omega : (((k+k)+(q*(k+1)))+(p*(k+1)))+2 = (((q+p)+2)*(k+1)-2)+2)

/-- The local original-strand word at a position specified by its prefix and
suffix block counts. -/
def localBlockWord (k p q : ℕ) : BraidWords (((q+p)+2)*(k+1)-2) :=
  cast (congrArg BraidWords (by
    have h := blockGenerator_index k (q+p) (localBlockPosition p q)
    have hpos : (localBlockPosition p q).val = p := rfl
    have hsub : (q+p)-p = q := by omega
    simp only [hpos, hsub] at h
    omega : ((k+k)+(q*(k+1)))+(p*(k+1)) = ((q+p)+2)*(k+1)-2))
    (insertLeftWords ((k+k)+(q*(k+1))) (p*(k+1))
      (insertRightWords (k+k) (q*(k+1)) (blockSweepWord k k)))

set_option backward.isDefEq.respectTransparency false in
/-- Every generator is carried to an explicit original-strand word by its
position-adapted flattening, with both indices transported to common counts. -/
theorem localBlockFlattenCommon_word (X : C) (k p q : ℕ) :
    (localBlockFlattenCommon X k p q).conjAut
      (braidGenerator (tensorPower X (k+1)) (q+p) (localBlockPosition p q)) =
      (braidWordAction X (((q+p)+2)*(k+1)-2) (localBlockWord k p q)).val := by
  simp only [localBlockFlattenCommon, Iso.trans_conjAut]
  let h : q+p = (0+q)+p := by omega
  have hi : Fin.cast (congrArg (fun z => z+1) h) (localBlockPosition p q) =
      shiftedFirstIndex (0+q) p := by
    apply Fin.ext
    rfl
  have hg := braidGenerator_reindex (tensorPower X (k+1)) h (localBlockPosition p q)
  rw [hi] at hg
  rw [hg, localBlockFlatten_adjacent]
  unfold localBlockWord
  rw [braidWordAction_cast X (by
    have h := blockGenerator_index k (q+p) (localBlockPosition p q)
    have hpos : (localBlockPosition p q).val = p := rfl
    have hsub : (q+p)-p = q := by omega
    simp only [hpos, hsub] at h
    omega : ((k+k)+(q*(k+1)))+(p*(k+1)) = ((q+p)+2)*(k+1)-2)]
  congr 1
  exact (congrArg Subtype.val (blockSweepWord_action_with_surrounding X k k
    (p*(k+1)) (q*(k+1)))).symm

end MTC.Braided
