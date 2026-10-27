module
public import PropertyF.Ground.CentreDimensions.BraidingTrace

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
/-- The pivotal/Drinfeld twist on an object. -/
def pivotalBraidedTwist (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) : X ≅ X :=
  p.iso X ≪≫ (Ground.doubleDualIso C X).symm

/-- The pivotal/Drinfeld twist is natural. -/
theorem pivotalBraidedTwist_natural (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) {X Y : C.Obj} (f : X ⟶ Y) :
    f ≫ (pivotalBraidedTwist C p Y).hom = (pivotalBraidedTwist C p X).hom ≫ f := by
  have hn : ((fᘁ)ᘁ) ≫ (Ground.doubleDualIso C Y).inv =
      (Ground.doubleDualIso C X).inv ≫ f := by
    apply (cancel_epi (Ground.doubleDualIso C X).hom).1
    simp only [Iso.hom_inv_id_assoc]
    rw [← doubleDualIso_natural_assoc]
    simp
  simp only [pivotalBraidedTwist, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← Category.assoc, p.naturality, Category.assoc, hn]
/-- The twist scalar of a simple object. -/
def pivotalBraidedTwistScalar (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] : ℂ :=
  simpleEndScalarEquiv C X (End.of (pivotalBraidedTwist C p X).hom)

/-- On a simple object the twist acts by its scalar. -/
theorem pivotalBraidedTwist_simple (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] :
    (pivotalBraidedTwist C p X).hom = pivotalBraidedTwistScalar C p X • 𝟙 X := by
  have h : End.of (pivotalBraidedTwist C p X).hom =
      pivotalBraidedTwistScalar C p X • (1 : End X) := by
    apply (simpleEndScalarEquiv C X).injective
    simp [pivotalBraidedTwistScalar]
  have hh := congrArg End.asHom h
  simpa using hh

/-- A simple twist scalar is nonzero. -/
theorem pivotalBraidedTwistScalar_ne_zero (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] :
    pivotalBraidedTwistScalar C p X ≠ 0 := by
  intro hz
  have ht := pivotalBraidedTwist_simple C p X
  rw [hz, zero_smul] at ht
  have hi := congrArg (fun f => f ≫ (pivotalBraidedTwist C p X).inv) ht
  simp at hi
  exact id_nonzero X hi

/-- The trace of a simple self-braiding is twist scalar times dimension. -/
theorem pivotalTrace_selfBraiding (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) [Simple X] :
    Ground.unitScalar C (p.rightTrace (β_ X X).hom) =
      pivotalBraidedTwistScalar C p X * pivotalDimension C p X := by
  have h := rightTrace_partialTrace p X X (End.of (β_ X X).hom)
  rw [rightPartialTrace_braiding] at h
  have ht : (p.iso X).hom ≫ (Ground.doubleDualIso C X).inv =
      pivotalBraidedTwistScalar C p X • 𝟙 X := pivotalBraidedTwist_simple C p X
  change p.rightTrace ((p.iso X).hom ≫ (Ground.doubleDualIso C X).inv) =
    p.rightTrace (β_ X X).hom at h
  rw [ht, PivotalStructure.rightTrace_smul] at h
  rw [← h]
  simp only [← groundUnitScalarEquiv_apply, map_smul, smul_eq_mul, pivotalDimension]

end PropertyF.Ground.Dimensions
