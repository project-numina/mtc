module
public import PropertyF.Ground.Dimensions.RankOneCriterion
public import PropertyF.Ground.CentreInduction.RankOne

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped BigOperators
namespace PropertyF.Ground.Dimensions
universe v u
/-- The global FP dimension of a rank-one fusion category is one. -/
theorem rankOne_globalFPDimension_eq_one (C : Ground.BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (Ground.rank C))] : Ground.globalFPDimension C = 1 := by
  change (∑ i, Ground.fpSimple C i ^ 2) = 1
  have hs : (∑ i, Ground.fpSimple C i ^ 2) = Ground.fpSimple C (Ground.unitIndex C) ^ 2 := by
    apply Finset.sum_eq_single (Ground.unitIndex C)
    · intro i _ hi
      exact (hi (Subsingleton.elim i (Ground.unitIndex C))).elim
    · intro h
      exact (h (Finset.mem_univ _)).elim
  rw [hs, Ground.fpSimple_unit]
  norm_num

/-- Assuming rigidity of the actual centre, a rank-one braided fusion
category has a positive spherical actual centre. -/
theorem center_positive_spherical_of_rank_one (C : Ground.BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (Ground.rank C))] [RigidCategory (CategoryTheory.Center C.Obj)] :
    letI : Ground.IsFusionCategory (CategoryTheory.Center C.Obj) := Ground.CentreInduction.fusion_of_rank_one C
    ∃ p : PivotalStructure (C := (Ground.Integrate.bundledCenter C).Obj), p.IsSpherical ∧ ∀ i,
      pivotalDimension (Ground.Integrate.bundledCenter C) p
        (Ground.simples (Ground.Integrate.bundledCenter C) i) =
          (Ground.fpSimple (Ground.Integrate.bundledCenter C) i : ℂ) := by
  let : Ground.IsFusionCategory (CategoryTheory.Center C.Obj) := Ground.CentreInduction.fusion_of_rank_one C
  have h := Ground.CentreInduction.globalFPDimension_square_of_rank_one C
  rw [rankOne_globalFPDimension_eq_one C] at h
  have hZ : Ground.globalFPDimension (Ground.Integrate.bundledCenter C) = 1 := by simpa using h
  exact positive_spherical_of_globalFPDimension_eq_one (Ground.Integrate.bundledCenter C) hZ
/-- In rank one, centre rigidity also gives the required positive spherical
structure and the categorical global-dimension square. -/
theorem center_spherical_and_globalDimension_of_rank_one (C : Ground.BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (Ground.rank C))] [RigidCategory (CategoryTheory.Center C.Obj)] :
    letI : Ground.IsFusionCategory (CategoryTheory.Center C.Obj) := Ground.CentreInduction.fusion_of_rank_one C
    ∃ p : PivotalStructure (C := (Ground.Integrate.bundledCenter C).Obj), p.IsSpherical ∧
      (∀ i, pivotalDimension (Ground.Integrate.bundledCenter C) p
        (Ground.simples (Ground.Integrate.bundledCenter C) i) =
          (Ground.fpSimple (Ground.Integrate.bundledCenter C) i : ℂ)) ∧
      Ground.globalDimension (Ground.Integrate.bundledCenter C) = (Ground.globalFPDimension C : ℂ) ^ 2 := by
  let : Ground.IsFusionCategory (CategoryTheory.Center C.Obj) := Ground.CentreInduction.fusion_of_rank_one C
  let Z := Ground.Integrate.bundledCenter C
  obtain ⟨p, hp, hd⟩ := center_positive_spherical_of_rank_one C
  refine ⟨p, hp, hd, ?_⟩
  have hpu : Ground.PseudoUnitary Z := positive_spherical_isPseudoUnitary Z p hp
    (Ground.fpSimple Z) hd (Ground.fpSimple_pos Z)
  change Ground.globalDimension Z = (Ground.globalFPDimension Z : ℂ) at hpu
  rw [hpu, Ground.CentreInduction.globalFPDimension_square_of_rank_one]
  norm_cast
end PropertyF.Ground.Dimensions
