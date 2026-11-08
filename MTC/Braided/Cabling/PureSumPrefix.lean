module
public import MTC.Braided.Cabling.PureSumPositiveState
public import MTC.Braided.Cabling.ClosureInsertionCompare

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

end MTC.Braided.Cabling
end
