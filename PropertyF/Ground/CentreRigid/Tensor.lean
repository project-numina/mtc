module
public import PropertyF.Ground.CentreRigid.Coevaluation

/-! Tensor coherence of the normalized dual half-braiding. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreRigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- The normalized dual crossing satisfies the half-braiding tensor law. -/
theorem dualCrossing_tensor (Z : Center C) (U V : C) :
    ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
        (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫ (α_ _ _ _).inv := by
  let X := Z.1
  let D : C := Z.1ᘁ
  let c (T : C) : X ⊗ T ⟶ T ⊗ X := (Z.2.β T).hom
  let d (T : C) : D ⊗ T ⟶ T ⊗ D := ((Integrate.dualCrossingIso Z).app T).hom
  let p : D ⊗ (U ⊗ V) ⟶ (U ⊗ V) ⊗ D :=
    (α_ D U V).inv ≫ (d U ▷ V) ≫ (α_ U D V).hom ≫ (U ◁ d V) ≫ (α_ U V D).inv
  have hs (T : C) :
      𝟙 T ⊗≫ (η_ X D ▷ T) ⊗≫ (X ◁ d T) ⊗≫ (c T ▷ D) ⊗≫ 𝟙 (T ⊗ (X ⊗ D)) =
        𝟙 T ⊗≫ (T ◁ η_ X D) ⊗≫ 𝟙 (T ⊗ (X ⊗ D)) := CentreRigid.coevaluation_sliding Z T
  have ht : c (U ⊗ V) = (α_ X U V).inv ≫ (c U ▷ V) ≫ (α_ U X V).hom ≫ (U ◁ c V) ≫ (α_ U V X).inv := Z.2.monoidal U V
  have hp :
      𝟙 (U ⊗ V) ⊗≫ (η_ X D ▷ (U ⊗ V)) ⊗≫ (X ◁ p) ⊗≫ (c (U ⊗ V) ▷ D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) =
        𝟙 (U ⊗ V) ⊗≫ ((U ⊗ V) ◁ η_ X D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by
    rw [ht]
    dsimp [p]
    calc
      _ = 𝟙 (U ⊗ V) ⊗≫ ((η_ X D ▷ U) ▷ V) ⊗≫ ((X ◁ d U) ▷ V) ⊗≫
        (((X ⊗ U) ◁ d V) ≫ (c U ▷ (V ⊗ D))) ⊗≫ (U ◁ (c V ▷ D)) ⊗≫
          𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by monoidal
      _ = 𝟙 (U ⊗ V) ⊗≫ ((η_ X D ▷ U) ▷ V) ⊗≫ ((X ◁ d U) ▷ V) ⊗≫
        ((c U ▷ (D ⊗ V)) ≫ ((U ⊗ X) ◁ d V)) ⊗≫ (U ◁ (c V ▷ D)) ⊗≫
          𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by rw [whisker_exchange]
      _ = 𝟙 (U ⊗ V) ⊗≫
        ((𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ d U) ⊗≫ (c U ▷ D) ⊗≫ 𝟙 (U ⊗ (X ⊗ D))) ▷ V) ⊗≫
        (U ◁ (X ◁ d V)) ⊗≫ (U ◁ (c V ▷ D)) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by monoidal
      _ = 𝟙 (U ⊗ V) ⊗≫
        ((𝟙 U ⊗≫ (U ◁ η_ X D) ⊗≫ 𝟙 (U ⊗ (X ⊗ D))) ▷ V) ⊗≫
        (U ◁ (X ◁ d V)) ⊗≫ (U ◁ (c V ▷ D)) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by rw [hs U]
      _ = 𝟙 (U ⊗ V) ⊗≫ (U ◁ (𝟙 V ⊗≫ (η_ X D ▷ V) ⊗≫ (X ◁ d V) ⊗≫ (c V ▷ D) ⊗≫ 𝟙 (V ⊗ (X ⊗ D)))) ⊗≫
        𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by monoidal
      _ = 𝟙 (U ⊗ V) ⊗≫ (U ◁ (𝟙 V ⊗≫ (V ◁ η_ X D) ⊗≫ 𝟙 (V ⊗ (X ⊗ D)))) ⊗≫
        𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by rw [hs V]
      _ = _ := by monoidal
  apply (tensorLeftHomEquiv (U ⊗ V) X D ((U ⊗ V) ⊗ D)).injective
  have eq1 : 𝟙 (U ⊗ V) ⊗≫ (η_ X D ▷ (U ⊗ V)) ⊗≫ (X ◁ d (U ⊗ V)) ⊗≫ (c (U ⊗ V) ▷ D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) =
      𝟙 (U ⊗ V) ⊗≫ (η_ X D ▷ (U ⊗ V)) ⊗≫ (X ◁ p) ⊗≫ (c (U ⊗ V) ▷ D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by
    calc
      _ = 𝟙 (U ⊗ V) ⊗≫ ((U ⊗ V) ◁ η_ X D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by
        convert hs (U ⊗ V) using 1 <;> monoidal
      _ = _ := hp.symm
  change (λ_ (U ⊗ V)).inv ≫ (η_ X D ▷ (U ⊗ V)) ≫ (α_ X D (U ⊗ V)).hom ≫ (X ◁ d (U ⊗ V)) =
    (λ_ (U ⊗ V)).inv ≫ (η_ X D ▷ (U ⊗ V)) ≫ (α_ X D (U ⊗ V)).hom ≫ (X ◁ p)
  apply (cancel_mono ((α_ X (U ⊗ V) D).inv ≫ (c (U ⊗ V) ▷ D) ≫ (α_ (U ⊗ V) X D).hom)).1
  calc
    _ = 𝟙 (U ⊗ V) ⊗≫ (η_ X D ▷ (U ⊗ V)) ⊗≫ (X ◁ d (U ⊗ V)) ⊗≫ (c (U ⊗ V) ▷ D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := by monoidal
    _ = 𝟙 (U ⊗ V) ⊗≫ (η_ X D ▷ (U ⊗ V)) ⊗≫ (X ◁ p) ⊗≫ (c (U ⊗ V) ▷ D) ⊗≫ 𝟙 ((U ⊗ V) ⊗ (X ⊗ D)) := eq1
    _ = _ := by monoidal

end PropertyF.Ground.CentreRigid
