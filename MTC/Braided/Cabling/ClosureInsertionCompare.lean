module
public import MTC.Braided.Cabling.ClosureFlattenCompare
public import MTC.Braided.Cabling.ClosureCommonInterface

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- Left strand insertion is the canonical recursive concatenation. -/
theorem insertLeftPowerIso_heq_join (X : C) (n : ℕ) : ∀ k,
    Trace.insertLeftPowerIso X n k ≍ joinPowerIso X k (n+2)
  | 0 => by rfl
  | k+1 => by
    simp only [Trace.insertLeftPowerIso, joinPowerIso]
    have ih := insertLeftPowerIso_heq_join X n k
    congr 2
    all_goals simp [strandSum_eq_add, tensorPower, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]


set_option backward.isDefEq.respectTransparency false in
/-- Positive-width block merge is the same canonical join. -/
theorem sweepBlockMerge_heq_join (X : C) (s r : ℕ) :
    sweepBlockMerge X s r ≍ joinPowerIso X (s+1) (r+1) := by
  have hm := sweepBlockMerge_eq_split X s r
  have hj := joinPowerNormalized_eq_split X r s
  have hmerge : sweepBlockMerge X s r ≍ (sweepBlockSplit X r s).symm := by
    rw [hm]
    exact iso_trans_eqToIso_heq _ _
  have hjoin : joinPowerIso X (s+1) (r+1) ≍ (sweepBlockSplit X r s).symm := by
    have h := iso_trans_eqToIso_heq (joinPowerIso X (s+1) (r+1))
      (congrArg (tensorPower X) (by rw [strandSum_eq_add]; omega :
        strandSum (s+1) (r+1) = r+s+2))
    change joinPowerNormalized X r s ≍ joinPowerIso X (s+1) (r+1) at h
    exact h.symm.trans (heq_of_eq hj)
  exact hmerge.trans hjoin.symm

set_option backward.isDefEq.respectTransparency false in
/-- Right insertion of a nonempty block is canonical concatenation. -/
theorem insertRightPowerIso_succ_heq_join (X : C) (n r : ℕ) :
    Trace.insertRightPowerIso X n (r+1) ≍ joinPowerIso X (n+2) (r+1) := by
  rw [insertRightPowerIso_eq_merge]
  simp only [joinPowerIso]
  have hm := sweepBlockMerge_heq_join X n r
  congr 2
  all_goals try simp [strandSum_eq_add, tensorPower, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  all_goals exact hm


/-- Right strand insertion is canonical concatenation, also for an empty tail. -/
theorem insertRightPowerIso_heq_join (X : C) (n : ℕ) : ∀ r,
    Trace.insertRightPowerIso X n r ≍ joinPowerIso X (n+2) r
  | 0 => by
    change ρ_ (tensorPower X (n+2)) ≍ joinPowerIso X (n+2) 0
    have h := joinPowerIso_heq X (n+2) 0
    rw [tensorPowerTensorIso_zero] at h
    exact h.symm
  | r+1 => insertRightPowerIso_succ_heq_join X n r

/-- Canonical joining of a prefix agrees with the strand-insertion map after
transporting the concatenated strand index. -/
theorem insertLeftPowerIso_eq_join (X : C) (n p : ℕ) :
    joinPowerIso X p (n+2) ≪≫
      powerIndexIso X (by rw [strandSum_eq_add]; omega : strandSum p (n+2) = (n+p)+2) =
    Trace.insertLeftPowerIso X n p := by
  apply eq_of_heq
  exact (iso_trans_eqToIso_heq _ _).trans (insertLeftPowerIso_heq_join X n p).symm

/-- Canonical joining of a suffix agrees with the strand-insertion map after
transporting the concatenated strand index. -/
theorem insertRightPowerIso_eq_join (X : C) (n t : ℕ) :
    joinPowerIso X (n+2) t ≪≫
      powerIndexIso X (by rw [strandSum_eq_add]; omega : strandSum (n+2) t = (n+t)+2) =
    Trace.insertRightPowerIso X n t := by
  apply eq_of_heq
  exact (iso_trans_eqToIso_heq _ _).trans (insertRightPowerIso_heq_join X n t).symm

/-- Prefixing arbitrary strands to an actual braid word gives the explicit
left-inserted braid word under canonical joining. -/
theorem joinPrefix_braidWord (X : C) (n p : ℕ) (w : BraidWords n) :
    (joinPowerIso X p (n+2) ≪≫
      powerIndexIso X (by rw [strandSum_eq_add]; omega : strandSum p (n+2) = (n+p)+2)).conjAut
      ((tensorLeft (tensorPower X p)).mapAut (tensorPower X (n+2)) (braidWordAction X n w).val) =
    (braidWordAction X (n+p) (insertLeftWords n p w)).val := by
  rw [insertLeftPowerIso_eq_join, leftInsertion_conjAut, braidWordAction_insertLeftWords]

/-- Suffixing arbitrary strands to an actual braid word gives the explicit
right-inserted braid word under canonical joining. -/
theorem joinSuffix_braidWord (X : C) (n t : ℕ) (w : BraidWords n) :
    (joinPowerIso X (n+2) t ≪≫
      powerIndexIso X (by rw [strandSum_eq_add]; omega : strandSum (n+2) t = (n+t)+2)).conjAut
      ((tensorRight (tensorPower X t)).mapAut (tensorPower X (n+2)) (braidWordAction X n w).val) =
    (braidWordAction X (n+t) (insertRightWords n t w)).val := by
  rw [insertRightPowerIso_eq_join, rightInsertion_conjAut, braidWordAction_insertRightWords]

set_option backward.isDefEq.respectTransparency false in
/-- Suffix insertion expresses the actual braid-word isomorphism as the
original word tensored with identity and transported by the canonical join. -/
theorem joinSuffix_braidWord_iso (X : C) (n t : ℕ) (w : BraidWords n) :
    (joinPowerIso X (n + 2) t ≪≫
      powerIndexIso X (by rw [strandSum_eq_add]; omega : strandSum (n + 2) t = (n + t) + 2)).symm ≪≫
      (((braidWordAction X n w).val).asIso ⊗ᵢ Iso.refl (tensorPower X t)) ≪≫
      (joinPowerIso X (n + 2) t ≪≫
        powerIndexIso X (by rw [strandSum_eq_add]; omega : strandSum (n + 2) t = (n + t) + 2)) =
    ((braidWordAction X (n + t) (insertRightWords n t w)).val).asIso := by
  have h := congrArg Aut.asIso (joinSuffix_braidWord X n t w)
  apply Iso.ext
  have hh := congrArg Iso.hom h
  simpa [Iso.conjAut_hom, Functor.mapAut, tensorRight, tensorIso_hom, Iso.trans_hom] using hh
