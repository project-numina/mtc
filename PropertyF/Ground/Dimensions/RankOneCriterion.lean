module
public import PropertyF.Ground.Dimensions.RankOneSpherical

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u
/-- Global FP dimension one forces the fusion category to have one simple label. -/
theorem rank_subsingleton_of_globalFPDimension_eq_one (C : Ground.BraidedFusionCategory.{v,u})
    (h : Ground.globalFPDimension C = 1) : Subsingleton (Fin (Ground.rank C)) := by
  classical
  have hs : ∑ i, Ground.fpSimple C i ^ 2 = 1 := h
  have he : ∑ i ∈ Finset.univ.erase (Ground.unitIndex C), Ground.fpSimple C i ^ 2 = 0 := by
    have ht := Finset.sum_erase_add (Finset.univ : Finset (Fin (Ground.rank C)))
      (fun i => Ground.fpSimple C i ^ 2) (Finset.mem_univ (Ground.unitIndex C))
    simp only [Ground.fpSimple_unit, one_pow] at ht
    rw [hs] at ht
    linarith
  have hall (i : Fin (Ground.rank C)) : i = Ground.unitIndex C := by
    by_contra hi
    have hm : i ∈ Finset.univ.erase (Ground.unitIndex C) := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
    have hle := Finset.single_le_sum (f := fun i => Ground.fpSimple C i ^ 2)
      (fun j _ => sq_nonneg (Ground.fpSimple C j)) hm
    rw [he] at hle
    have hp := Ground.fpSimple_pos C i
    nlinarith
  exact ⟨fun i j => (hall i).trans (hall j).symm⟩
/-- Global FP dimension one gives the actual positive spherical structure. -/
theorem positive_spherical_of_globalFPDimension_eq_one (C : Ground.BraidedFusionCategory.{v,u})
    (h : Ground.globalFPDimension C = 1) :
    ∃ p : PivotalStructure (C := C.Obj), p.IsSpherical ∧ ∀ i,
      pivotalDimension C p (Ground.simples C i) = (Ground.fpSimple C i : ℂ) := by
  let : Subsingleton (Fin (Ground.rank C)) := rank_subsingleton_of_globalFPDimension_eq_one C h
  exact rankOne_positive_spherical C

end PropertyF.Ground.Dimensions
