module
public import PropertyF.Ground.CentreRigid.Lift
public import PropertyF.Ground.CentreInduction.SimpleDetection

/-! Centrality of the duality maps can be tested on simple objects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreRigid
universe v u

set_option backward.isDefEq.respectTransparency false in
/-- In a fusion category the coevaluation is central as soon as its
intertwining equation holds on each chosen simple object. -/
theorem coevaluation_central_of_simples (C : BraidedFusionCategory.{v,u})
    (Z : CategoryTheory.Center C.Obj)
    (hTensor : ∀ U V : C.Obj, ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
        (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫
          (α_ _ _ _).inv)
    (h : ∀ i, ((η_ Z.1 Z.1ᘁ) ▷ simples C i) ≫
      ((Z ⊗ dualObject Z hTensor).2.β (simples C i)).hom =
      ((𝟙_ (CategoryTheory.Center C.Obj)).2.β (simples C i)).hom ≫
        (simples C i ◁ η_ Z.1 Z.1ᘁ)) :
    ∀ U, ((η_ Z.1 Z.1ᘁ) ▷ U) ≫
      ((Z ⊗ dualObject Z hTensor).2.β U).hom =
      ((𝟙_ (CategoryTheory.Center C.Obj)).2.β U).hom ≫ (U ◁ η_ Z.1 Z.1ᘁ) :=
  CentreInduction.comm_of_simples C (𝟙_ (CategoryTheory.Center C.Obj))
    (Z ⊗ dualObject Z hTensor) (η_ Z.1 Z.1ᘁ) h

set_option backward.isDefEq.respectTransparency false in
/-- In a fusion category the evaluation is central as soon as its
intertwining equation holds on each chosen simple object. -/
theorem evaluation_central_of_simples (C : BraidedFusionCategory.{v,u})
    (Z : CategoryTheory.Center C.Obj)
    (hTensor : ∀ U V : C.Obj, ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
        (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫
          (α_ _ _ _).inv)
    (h : ∀ i, ((ε_ Z.1 Z.1ᘁ) ▷ simples C i) ≫
      ((𝟙_ (CategoryTheory.Center C.Obj)).2.β (simples C i)).hom =
      ((dualObject Z hTensor ⊗ Z).2.β (simples C i)).hom ≫
        (simples C i ◁ ε_ Z.1 Z.1ᘁ)) :
    ∀ U, ((ε_ Z.1 Z.1ᘁ) ▷ U) ≫
      ((𝟙_ (CategoryTheory.Center C.Obj)).2.β U).hom =
      ((dualObject Z hTensor ⊗ Z).2.β U).hom ≫ (U ◁ ε_ Z.1 Z.1ᘁ) :=
  CentreInduction.comm_of_simples C (dualObject Z hTensor ⊗ Z)
    (𝟙_ (CategoryTheory.Center C.Obj)) (ε_ Z.1 Z.1ᘁ) h

end PropertyF.Ground.CentreRigid
