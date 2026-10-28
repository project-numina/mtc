module
public import PropertyF.Ground.Calculus.PartialTrace
public import PropertyF.Ground.Centre.Basic
public import PropertyF.Ground.Modular.SMatrix
public import PropertyF.Ground.CentreInduction.SimpleDetection
public import PropertyF.Ground.Fusion.SemisimpleSplit
public import PropertyF.Ground.Centre.Cokernel
public import PropertyF.Ground.CentreRigid.Unit

/-! The unit-strand case of the centre intertwining equation. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreInduction
universe v u

/-- Every underlying map satisfies the centre intertwining equation on the
unit strand. -/
theorem comm_unit (C : BraidedFusionCategory.{v,u})
    (X Y : CategoryTheory.Center C.Obj) (f : X.1 ⟶ Y.1) :
    (f ▷ 𝟙_ C.Obj) ≫ (Y.2.β (𝟙_ C.Obj)).hom =
      (X.2.β (𝟙_ C.Obj)).hom ≫ ((𝟙_ C.Obj) ◁ f) :=
  CentreRigid.centrality_at_unit X Y f

/-- Every underlying map also intertwines a half-braiding on any object
isomorphic to the tensor unit. -/
theorem comm_of_iso_unit (C : BraidedFusionCategory.{v,u})
    (X Y : CategoryTheory.Center C.Obj) (f : X.1 ⟶ Y.1)
    (T : C.Obj) (e : T ≅ 𝟙_ C.Obj) :
    (f ▷ T) ≫ (Y.2.β T).hom = (X.2.β T).hom ≫ (T ◁ f) := by
  apply (cancel_mono (e.hom ▷ Y.1)).1
  have hx := X.2.naturality e.hom
  have hy := Y.2.naturality e.hom
  calc
    _ = (f ▷ T) ≫ (Y.1 ◁ e.hom) ≫ (Y.2.β (𝟙_ C.Obj)).hom := by
      simpa [Category.assoc] using congrArg (fun g => (f ▷ T) ≫ g) hy.symm
    _ = (X.1 ◁ e.hom) ≫ (f ▷ 𝟙_ C.Obj) ≫ (Y.2.β (𝟙_ C.Obj)).hom := by
      rw [whisker_exchange_assoc]
    _ = (X.1 ◁ e.hom) ≫ (X.2.β (𝟙_ C.Obj)).hom ≫ ((𝟙_ C.Obj) ◁ f) := by
      simpa only [Category.assoc] using congrArg (fun g => (X.1 ◁ e.hom) ≫ g) (comm_unit C X Y f)
    _ = (X.2.β T).hom ≫ (e.hom ▷ X.1) ≫ ((𝟙_ C.Obj) ◁ f) := by
      simpa only [Category.assoc] using congrArg (fun g => g ≫ ((𝟙_ C.Obj) ◁ f)) hx
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun g => (X.2.β T).hom ≫ g)
        (whisker_exchange e.hom f).symm



end PropertyF.Ground.CentreInduction

namespace PropertyF.Ground.CentreInduction
universe v u

/-- In rank one every underlying map between centre objects is central. -/
theorem all_maps_central_of_rank_one (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] (X Y : CategoryTheory.Center C.Obj)
    (f : X.1 ⟶ Y.1) : ∀ T, (f ▷ T) ≫ (Y.2.β T).hom =
      (X.2.β T).hom ≫ (T ◁ f) := by
  apply comm_of_simples C X Y f
  intro i
  have hi : i = unitIndex C := Subsingleton.elim _ _
  obtain ⟨e⟩ := unitIndex_iso C
  subst i
  exact comm_of_iso_unit C X Y f _ e

/-- In rank one, centre forget is full. -/
def centerForgetFullOfRankOne (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] : (CategoryTheory.Center.forget C.Obj).Full where
  map_surjective := by
    intro X Y f
    exact ⟨⟨f, all_maps_central_of_rank_one C X Y f⟩, rfl⟩

/-- In rank one, the actual centre is equivalent as a category to C via
forget. This does not construct its rigid or fusion structure. -/
def centerForgetEquivalenceOfRankOne (C : BraidedFusionCategory.{v,u})
    [Subsingleton (Fin (rank C))] : CategoryTheory.Center C.Obj ≌ C.Obj := by
  let F := CategoryTheory.Center.forget C.Obj
  letI : F.Full := centerForgetFullOfRankOne C
  letI : F.EssSurj := Functor.essSurj_of_surj (F := F) (by
    intro X
    exact ⟨(CategoryTheory.Center.ofBraided C.Obj).obj X, rfl⟩)
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

end PropertyF.Ground.CentreInduction
