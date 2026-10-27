module
public import PropertyF.Ground.Dimensions.DefectSwappedCoevaluation

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The actual root tensor defect obeys the noncommutative tensor-cocycle law. -/
theorem rootTensorDefect_associativity (C : Ground.BraidedFusionCategory.{v,u}) (X Y Z : C.Obj) :
    (rootTensorDefect C X (Y ⊗ Z)).hom ≫ X ◁ (rootTensorDefect C Y Z).hom =
      (α_ X Y Z).inv ≫ (rootTensorDefect C (X ⊗ Y) Z).hom ≫
        (rootTensorDefect C X Y).hom ▷ Z ≫ (α_ X Y Z).hom := by
  letI : (doubleDualFunctor C.Obj).Monoidal := doubleDualMonoidal C.Obj
  letI : (doubleDualFunctor C.Obj).OplaxMonoidal := (doubleDualMonoidal C.Obj).toOplaxMonoidal
  letI : (𝟭 C.Obj).OplaxMonoidal :=
    (Functor.Monoidal.transport (fourthDualRootNaturalIso C).symm).toOplaxMonoidal
  have hd (A B : C.Obj) : Functor.OplaxMonoidal.δ (𝟭 C.Obj) A B = (rootTensorDefect C A B).hom := by
    have hF : Functor.OplaxMonoidal.δ (doubleDualFunctor C.Obj) A B = (doubleDualTensorIso A B).inv := rfl
    have h := Functor.Monoidal.transport_δ (fourthDualRootNaturalIso C).symm A B
    simpa [rootTensorDefect, rootTensorIso, hF] using h
  have h := Functor.OplaxMonoidal.δ_comp_whiskerLeft_δ (𝟭 C.Obj) X Y Z
  simp only [hd, Functor.id_obj, Functor.id_map] at h
  exact h
end PropertyF.Ground.Dimensions
