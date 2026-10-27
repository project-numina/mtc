module
public import PropertyF.Ground.Cabling.Pure
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-! Factoring the actual braid-word action through strand permutations. -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- Adjacent transpositions generate the full symmetric group. -/
theorem strandPermutation_surjective (n : ℕ) : Function.Surjective (strandPermutation n) := by
  apply FreeGroup.lift_surjective_iff_closure_range_eq_top.mpr
  apply Subgroup.closure_eq_top_of_mclosure_eq_top
  exact Equiv.Perm.mclosure_swap_castSucc_succ (n + 1)

/-- Pure-word triviality is the precise remaining condition for the actual
braid action to factor through the symmetric group. -/
def permutationActionOfPureTrivial (X : C) (n : ℕ)
    (h : (strandPermutation n).ker ≤ (FreeGroup.lift (braidGenerator X n)).ker) :
    Equiv.Perm (Fin (n + 2)) →* Aut (tensorPower X (n + 2)) :=
  (QuotientGroup.lift _ (FreeGroup.lift (braidGenerator X n)) h).comp
    (QuotientGroup.liftEquiv _ (strandPermutation_surjective n) rfl).symm.toMonoidHom

/-- The descended action takes each adjacent transposition to its actual
categorical braid generator. -/
theorem permutationActionOfPureTrivial_swap (X : C) (n : ℕ)
    (h : (strandPermutation n).ker ≤ (FreeGroup.lift (braidGenerator X n)).ker)
    (i : Fin (n + 1)) :
    permutationActionOfPureTrivial X n h (Equiv.swap i.castSucc i.succ) =
      braidGenerator X n i := by
  let e := QuotientGroup.liftEquiv (strandPermutation n).ker (strandPermutation_surjective n) rfl
  have he : e (QuotientGroup.mk' (strandPermutation n).ker (FreeGroup.of i)) =
      Equiv.swap i.castSucc i.succ := by
    change strandPermutation n (FreeGroup.of i) = _
    exact FreeGroup.lift_apply_of
  change (QuotientGroup.lift _ (FreeGroup.lift (braidGenerator X n)) h)
    (e.symm (Equiv.swap i.castSucc i.succ)) = _
  rw [← he, e.symm_apply_apply]
  exact FreeGroup.lift_apply_of

end PropertyF.Ground.CentreCalculus
