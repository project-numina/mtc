module
public import PropertyF.Ground.CentreRigid.SimpleCentrality

/-! Detect the dual-crossing tensor law on pairs of simple objects. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.CentreRigid
universe v u
variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false in
def leftNat (Z : Center C.Obj) (U : C.Obj) :
    (tensorLeft U ⋙ tensorLeft Z.1ᘁ) ⟶ (tensorLeft U ⋙ tensorRight Z.1ᘁ) where
  app V := ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom
  naturality {V W} f := by simpa using Integrate.dualCrossing_natural Z (U ◁ f)

set_option backward.isDefEq.respectTransparency false in
def rightNat (Z : Center C.Obj) (U : C.Obj) :
    (tensorLeft U ⋙ tensorLeft Z.1ᘁ) ⟶ (tensorLeft U ⋙ tensorRight Z.1ᘁ) where
  app V := (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
    (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫ (α_ _ _ _).inv
  naturality {V W} f := by
    let b (T : C.Obj) : Z.1ᘁ ⊗ T ⟶ T ⊗ Z.1ᘁ := ((Integrate.dualCrossingIso Z).app T).hom
    have h : (Z.1ᘁ ◁ f) ≫ b W = b V ≫ (f ▷ Z.1ᘁ) := Integrate.dualCrossing_natural Z f
    change (Z.1ᘁ ◁ (U ◁ f)) ≫ ((α_ _ _ _).inv ≫ (b U ▷ W) ≫ (α_ _ _ _).hom ≫ (U ◁ b W) ≫ (α_ _ _ _).inv) = ((α_ _ _ _).inv ≫ (b U ▷ V) ≫ (α_ _ _ _).hom ≫ (U ◁ b V) ≫ (α_ _ _ _).inv) ≫ ((U ◁ f) ▷ Z.1ᘁ)
    calc
      _ = 𝟙 _ ⊗≫ ((((Z.1ᘁ : C.Obj) ⊗ U) ◁ f) ≫ (b U ▷ W)) ⊗≫ (U ◁ b W) ⊗≫ 𝟙 _ := by monoidal
      _ = 𝟙 _ ⊗≫ ((b U ▷ V) ≫ ((U ⊗ (Z.1ᘁ : C.Obj)) ◁ f)) ⊗≫ (U ◁ b W) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
      _ = 𝟙 _ ⊗≫ (b U ▷ V) ⊗≫ (U ◁ ((Z.1ᘁ ◁ f) ≫ b W)) ⊗≫ 𝟙 _ := by monoidal
      _ = 𝟙 _ ⊗≫ (b U ▷ V) ⊗≫ (U ◁ (b V ≫ (f ▷ Z.1ᘁ))) ⊗≫ 𝟙 _ := by rw [h]
      _ = _ := by monoidal

set_option backward.isDefEq.respectTransparency false in
def leftNatU (Z : Center C.Obj) (V : C.Obj) :
    (tensorRight V ⋙ tensorLeft Z.1ᘁ) ⟶ (tensorRight V ⋙ tensorRight Z.1ᘁ) where
  app U := ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom
  naturality {U W} f := by simpa using Integrate.dualCrossing_natural Z (f ▷ V)

set_option backward.isDefEq.respectTransparency false in
def rightNatU (Z : Center C.Obj) (V : C.Obj) :
    (tensorRight V ⋙ tensorLeft Z.1ᘁ) ⟶ (tensorRight V ⋙ tensorRight Z.1ᘁ) where
  app U := (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
    (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫ (α_ _ _ _).inv
  naturality {U W} f := by
    let b (T : C.Obj) : Z.1ᘁ ⊗ T ⟶ T ⊗ Z.1ᘁ := ((Integrate.dualCrossingIso Z).app T).hom
    have h : (Z.1ᘁ ◁ f) ≫ b W = b U ≫ (f ▷ Z.1ᘁ) := Integrate.dualCrossing_natural Z f
    change (Z.1ᘁ ◁ (f ▷ V)) ≫ ((α_ _ _ _).inv ≫ (b W ▷ V) ≫ (α_ _ _ _).hom ≫ (W ◁ b V) ≫ (α_ _ _ _).inv) = ((α_ _ _ _).inv ≫ (b U ▷ V) ≫ (α_ _ _ _).hom ≫ (U ◁ b V) ≫ (α_ _ _ _).inv) ≫ ((f ▷ V) ▷ Z.1ᘁ)
    calc
      _ = 𝟙 _ ⊗≫ ((((Z.1ᘁ : C.Obj) ◁ f) ≫ b W) ▷ V) ⊗≫ (W ◁ b V) ⊗≫ 𝟙 _ := by monoidal
      _ = 𝟙 _ ⊗≫ ((b U ≫ (f ▷ Z.1ᘁ)) ▷ V) ⊗≫ (W ◁ b V) ⊗≫ 𝟙 _ := by rw [h]
      _ = 𝟙 _ ⊗≫ (b U ▷ V) ⊗≫ ((f ▷ ((Z.1ᘁ : C.Obj) ⊗ V)) ≫ (W ◁ b V)) ⊗≫ 𝟙 _ := by monoidal
      _ = 𝟙 _ ⊗≫ (b U ▷ V) ⊗≫ ((U ◁ b V) ≫ (f ▷ (V ⊗ (Z.1ᘁ : C.Obj)))) ⊗≫ 𝟙 _ := by rw [whisker_exchange]
      _ = _ := by monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The full tensor law follows from its cases on pairs of simple representatives. -/
theorem dualCrossing_tensor_of_simples (Z : Center C.Obj)
  (h : ∀ i j, ((Integrate.dualCrossingIso Z).app (simples C i ⊗ simples C j)).hom =
    (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app (simples C i)).hom ▷ simples C j) ≫
      (α_ _ _ _).hom ≫ (simples C i ◁ ((Integrate.dualCrossingIso Z).app (simples C j)).hom) ≫
        (α_ _ _ _).inv) :
  ∀ U V, ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom =
    (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
      (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫
        (α_ _ _ _).inv := by
  intro U V
  change (leftNat C Z U).app V = (rightNat C Z U).app V
  have hk : leftNatU C Z V = rightNatU C Z V := by
    apply CentreInduction.natTrans_ext_on_simples C
    intro i
    have hm : leftNat C Z (simples C i) = rightNat C Z (simples C i) := by
      apply CentreInduction.natTrans_ext_on_simples C
      intro j
      exact h i j
    exact congrArg (fun t => t.app V) hm
  exact congrArg (fun t => t.app U) hk

end PropertyF.Ground.CentreRigid
