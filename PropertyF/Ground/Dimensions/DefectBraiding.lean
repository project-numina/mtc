module
public import PropertyF.Ground.Dimensions.DoubleDualBraiding
public import PropertyF.Ground.Dimensions.DefectAssociativity
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The natural root tensor defect commutes with the braiding. -/
theorem rootTensorDefect_braiding (C : Ground.BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    (rootTensorDefect C X Y).hom ≫ (β_ X Y).hom =
      (β_ X Y).hom ≫ (rootTensorDefect C Y X).hom := by
  let F := doubleDualFunctor C.Obj
  let a := (fourthDualRootNaturalIso C).symm
  letI : F.Braided := doubleDualBraided C.Obj
  letI : F.Monoidal := (doubleDualBraided C.Obj).toMonoidal
  letI : F.OplaxMonoidal := (doubleDualBraided C.Obj).toMonoidal.toOplaxMonoidal
  letI : (𝟭 C.Obj).Monoidal := Functor.Monoidal.transport a
  letI : (𝟭 C.Obj).LaxMonoidal := (Functor.Monoidal.transport a).toLaxMonoidal
  letI : (𝟭 C.Obj).OplaxMonoidal := (Functor.Monoidal.transport a).toOplaxMonoidal
  letI : a.hom.IsMonoidal := Functor.Monoidal.natTransIsMonoidal_of_transport a
  letI : (𝟭 C.Obj).LaxBraided := Functor.LaxBraided.ofNatIso a
  letI : (𝟭 C.Obj).Braided := { __ := Functor.Monoidal.transport a, __ := Functor.LaxBraided.ofNatIso a }
  have hd (A B : C.Obj) : Functor.OplaxMonoidal.δ (𝟭 C.Obj) A B = (rootTensorDefect C A B).hom := by
    have hF : Functor.OplaxMonoidal.δ F A B = (doubleDualTensorIso A B).inv := rfl
    have h := Functor.Monoidal.transport_δ a A B
    simpa [a, F, rootTensorDefect, rootTensorIso, hF] using h
  have h := Functor.map_braiding (𝟭 C.Obj) X Y
  simp only [Functor.id_obj, Functor.id_map, hd] at h
  have hinv : (rootTensorDefect C Y X).hom ≫ Functor.LaxMonoidal.μ (𝟭 C.Obj) Y X = 𝟙 _ := by
    rw [← hd]
    exact Functor.Monoidal.δ_μ (𝟭 C.Obj) Y X
  apply (cancel_mono (Functor.LaxMonoidal.μ (𝟭 C.Obj) Y X)).1
  rw [Category.assoc, ← h]
  simp only [Category.assoc, hinv, Category.comp_id]
end PropertyF.Ground.Dimensions
