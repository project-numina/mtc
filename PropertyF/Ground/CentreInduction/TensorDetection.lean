module
public import PropertyF.Ground.CentreInduction.CrossingNaturality
public import PropertyF.Ground.CentreInduction.SimpleDetection

/-! The induction crossing tensor law is detected on pairs of simple objects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreInduction
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

variable (C : BraidedFusionCategory.{v,u}) (X : C.Obj)
local notation "A" => underlying C X
local notation "b" => crossingCandidate C X

/-- The composite of two crossings, with the associators inserted. -/
def crossingTensorComposite (T U : C.Obj) : A ⊗ (T ⊗ U) ⟶ (T ⊗ U) ⊗ A :=
  (α_ _ _ _).inv ≫ (b T ▷ U) ≫ (α_ _ _ _).hom ≫
    (T ◁ b U) ≫ (α_ _ _ _).inv














end PropertyF.Ground.CentreInduction
