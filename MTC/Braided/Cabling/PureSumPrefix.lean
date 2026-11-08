module
public import MTC.Braided.Cabling.PureSumPositiveState
public import MTC.Braided.Cabling.ClosureInsertionCompare
public import MTC.Braided.Cabling.ClosureColoredContext

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Braided.Cabling
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [Abelian C]

/-- Prefixing arbitrary original strands sends an element of a braid image
to the larger braid image, via the canonical join. -/
theorem braidImage_prefix_mem (X : C) (n p : ℕ)
    (a : Aut (tensorPower X (n + 2))) (ha : a ∈ braidImage X n) :
    (joinPowerIso X p (n + 2) ≪≫
      powerIndexIso X (by rw [strandSum_eq_add]; omega :
        strandSum p (n + 2) = (n + p) + 2)).conjAut
      ((tensorLeft (tensorPower X p)).mapAut (tensorPower X (n + 2)) a) ∈
        braidImage X (n + p) := by
  obtain ⟨w, hw⟩ := braidWordAction_surjective X n ⟨a, ha⟩
  have hw' := congrArg Subtype.val hw
  change (braidWordAction X n w).val = a at hw'
  rw [← hw', joinPrefix_braidWord]
  exact (braidWordAction X (n + p) _).property

set_option backward.isDefEq.respectTransparency false in
/-- Flattening a colored tuple starts by flattening its tail and joining the
first block. -/
theorem coloredFlatten_head_heq (X : C) (n : ℕ) (k : Fin (n + 1) → ℕ) :
    coloredTensorPowersFlatten X (n + 1) k ≍
      (Iso.refl (tensorPower X (k 0)) ⊗ᵢ
        coloredTensorPowersFlatten X n (fun j => k j.succ)) ≪≫
        joinPowerIso X (k 0) (∑ j : Fin n, k j.succ) := by
  have h := coloredTensorPowersFlatten_heq X (n + 1) k
  have ht := coloredTensorPowersFlatten_heq X n (fun j => k j.succ)
  apply h.trans
  simp only [heterogeneousPowerFlatten]
  congr 2
  all_goals try exact ht.symm
  all_goals try simp [heterogeneousStrandCount_eq_sum, heterogeneousPowerTensor, ← coloredTensor_powers_eq, strandSum_eq_add, Fin.sum_univ_succ]

end MTC.Braided.Cabling
end
