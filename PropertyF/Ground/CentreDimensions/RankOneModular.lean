module
public import PropertyF.Ground.CentreDimensions.RankOneRigid
public import PropertyF.Ground.Modular.UnitDimension

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
/-- In a rank-one braided fusion category, every pivotal S-matrix has determinant one. -/
theorem categoricalS_det_of_rank_one (C : Ground.BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (Ground.rank C))] (p : PivotalStructure (C := C.Obj)) :
    (Ground.Modular.categoricalS C p).det = 1 := by
  rw [Matrix.det_eq_elem_of_subsingleton _ (Ground.unitIndex C),
    Ground.Modular.categoricalS_unit, Ground.Modular.simpleDimension_unit]

/-- In rank one the actual centre is rigid, fusion, positive spherical, has
invertible S, and has the required categorical global dimension. -/
theorem rankOne_center_modular_and_globalDimension (C : Ground.BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (Ground.rank C))] :
    letI : RigidCategory (CategoryTheory.Center C.Obj) := rankOne_centerRigid C
    letI : Ground.IsFusionCategory (CategoryTheory.Center C.Obj) := Ground.CentreInduction.fusion_of_rank_one C
    ∃ p : PivotalStructure (C := (Ground.Integrate.bundledCenter C).Obj), p.IsSpherical ∧
      (∀ i, pivotalDimension (Ground.Integrate.bundledCenter C) p
        (Ground.simples (Ground.Integrate.bundledCenter C) i) =
          (Ground.fpSimple (Ground.Integrate.bundledCenter C) i : ℂ)) ∧
      (Ground.Modular.categoricalS (Ground.Integrate.bundledCenter C) p).det ≠ 0 ∧
      Ground.globalDimension (Ground.Integrate.bundledCenter C) = (Ground.globalFPDimension C : ℂ) ^ 2 := by
  let : RigidCategory (CategoryTheory.Center C.Obj) := rankOne_centerRigid C
  let : Ground.IsFusionCategory (CategoryTheory.Center C.Obj) := Ground.CentreInduction.fusion_of_rank_one C
  let Z := Ground.Integrate.bundledCenter C
  have h := Ground.CentreInduction.globalFPDimension_square_of_rank_one C
  rw [rankOne_globalFPDimension_eq_one C] at h
  have hZ : Ground.globalFPDimension Z = 1 := by simpa using h
  let : Subsingleton (Fin (Ground.rank Z)) := rank_subsingleton_of_globalFPDimension_eq_one Z hZ
  obtain ⟨p, hp, hd, hg⟩ := rankOne_center_spherical_and_globalDimension C
  refine ⟨p, hp, hd, ?_, hg⟩
  rw [categoricalS_det_of_rank_one]
  exact one_ne_zero
end PropertyF.Ground.Dimensions
