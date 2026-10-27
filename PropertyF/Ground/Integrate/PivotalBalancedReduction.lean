module
public import PropertyF.Ground.Integrate.TransparentCenterReduction
public import PropertyF.Ground.CentreInduction.Transparent

/-! Trivial centre transparency is constructed from actual induction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- The actual rigid fusion centre has no non-unit transparent simple. -/
theorem center_transparent_label_eq_unit
    (C : BraidedFusionCategory.{v,u})
    [RigidCategory (CategoryTheory.Center C.Obj)]
    [IsFusionCategory (CategoryTheory.Center C.Obj)]
    (k : Fin (rank (Integrate.bundledCenter C)))
    (hk : Transparent (simples (Integrate.bundledCenter C) k)) :
    k = unitIndex (Integrate.bundledCenter C) := by
  let D := Integrate.bundledCenter C
  let Y := simples D k
  letI : Simple Y := simples_simple D k
  obtain ⟨e⟩ := CentreInduction.center_transparent_simple_iso_unit C Y (by
    intro W
    exact hk W)
  obtain ⟨u⟩ := unitIndex_iso D
  exact simples_injective D k (unitIndex D) ⟨e ≪≫ u.symm⟩

/-- The frozen target follows from base pivotal existence and balancing of
its constructed centre twist. These two obligations remain explicit. -/
theorem target_of_pivotal_base_and_center_balancing
    (hCenter : ∀ (C : BraidedFusionCategory.{v,u}) (hpu : PseudoUnitary C),
      HasPropertyF C.Obj →
      ∃ (p : Dimensions.PivotalStructure (C := C.Obj)),
        letI := CentreRigid.rigidCenter (C := C.Obj)
        letI := centerFusionOfPivotalPseudoUnitary C p hpu
        let pZ := centerPivotalOfPivotalPseudoUnitary C p hpu
        let D := Integrate.bundledCenter C
        ∀ X Y : D.Obj, Modular.doubleBraiding X Y ≫
          ((Dimensions.pivotalBraidedTwist D pZ X).hom ⊗ₘ
            (Dimensions.pivotalBraidedTwist D pZ Y).hom) =
          (Dimensions.pivotalBraidedTwist D pZ (X ⊗ Y)).hom) : TargetStatement.{v,u} := by
  apply target_of_pivotal_balanced_center_trivial_transparency
  intro C hpu hF
  obtain ⟨p, hbalance⟩ := hCenter C hpu hF
  letI := CentreRigid.rigidCenter (C := C.Obj)
  letI := centerFusionOfPivotalPseudoUnitary C p hpu
  exact ⟨p, hbalance, center_transparent_label_eq_unit C⟩

end PropertyF.Ground
