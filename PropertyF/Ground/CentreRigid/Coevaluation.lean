module
public import PropertyF.Ground.CentreRigid.MateExplicit
public import PropertyF.Ground.CentreRigid.Lift

/-! Coevaluation centrality for the normalized dual crossing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreRigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- The normalized dual crossing intertwines the coevaluation. -/
theorem coevaluation_sliding (Z : Center C) (U : C) :
    𝟙 U ⊗≫ (η_ Z.1 Z.1ᘁ ▷ U) ⊗≫
      (Z.1 ◁ (show Z.1ᘁ ⊗ U ⟶ U ⊗ Z.1ᘁ from ((Integrate.dualCrossingIso Z).app U).hom)) ⊗≫
      ((Z.2.β U).hom ▷ Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ (Z.1 ⊗ Z.1ᘁ)) =
    𝟙 U ⊗≫ (U ◁ η_ Z.1 Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ (Z.1 ⊗ Z.1ᘁ)) := by
  let X := Z.1
  let D : C := Z.1ᘁ
  let L : C := ᘁZ.1
  let f : L ⟶ D := (Integrate.dualMateUnit Z).inv
  let m : D ⊗ U ⟶ U ⊗ L := (Integrate.dualMateIso Z).hom.app U
  let n : U ⊗ L ⟶ D ⊗ U := (Integrate.dualMateIso Z).inv.app U
  let c (T : C) : X ⊗ T ⟶ T ⊗ X := (Z.2.β T).hom
  have hm : n ≫ m = 𝟙 _ := by simp [n, m, L]
  have hf : (X ◁ f) ≫ c D = c L ≫ (f ▷ X) := Z.2.naturality f
  have hn : (X ◁ m) ≫ c (U ⊗ L) = c (D ⊗ U) ≫ (m ▷ X) := Z.2.naturality m
  have ht1 := Z.2.monoidal D U
  have ht2 := Z.2.monoidal U L
  change c (U ⊗ L) = (α_ X U L).inv ≫ (c U ▷ L) ≫ (α_ U X L).hom ≫ (U ◁ c L) ≫ (α_ U L X).inv at ht2
  have hu := CentreRigid.dualMate_unit_explicit Z U
  change (λ_ U).inv ≫ (η_ X D ▷ U) ≫ (α_ X D U).hom ≫ c (D ⊗ U) = (ρ_ U).inv ≫ (U ◁ η_ L X) ≫ (α_ U L X).inv ≫ (n ▷ X) at hu
  have hc : η_ X D ≫ c D = η_ L X ≫ (f ▷ X) := CentreRigid.dualMateUnit_crossed_coevaluation Z
  have hx : (show D ⊗ U ⟶ U ⊗ D from ((Integrate.dualCrossingIso Z).app U).hom) = m ≫ (U ◁ f) := by
    rfl
  rw [hx]
  apply (cancel_mono (U ◁ c D)).1
  calc
    _ = 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ m) ⊗≫
      ((((X ⊗ U) ◁ f) ≫ (c U ▷ D))) ⊗≫ (U ◁ c D) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by monoidal
    _ = 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ m) ⊗≫
      (((c U ▷ L) ≫ ((U ⊗ X) ◁ f))) ⊗≫ (U ◁ c D) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by rw [whisker_exchange]
    _ = 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ m) ⊗≫ (c U ▷ L) ⊗≫
      (U ◁ ((X ◁ f) ≫ c D)) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by monoidal
    _ = 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ m) ⊗≫ (c U ▷ L) ⊗≫
      (U ◁ (c L ≫ (f ▷ X))) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by rw [hf]
    _ = 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ ((X ◁ m) ≫ c (U ⊗ L)) ⊗≫
      (U ◁ (f ▷ X)) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by rw [ht2]; monoidal
    _ = 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ ((c (D ⊗ U)) ≫ (m ▷ X)) ⊗≫
      (U ◁ (f ▷ X)) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by rw [hn]
    _ = ((λ_ U).inv ≫ (η_ X D ▷ U) ≫ (α_ X D U).hom ≫ c (D ⊗ U)) ≫
      (m ▷ X) ≫ (α_ U L X).hom ≫ (U ◁ (f ▷ X)) := by monoidal
    _ = ((ρ_ U).inv ≫ (U ◁ η_ L X) ≫ (α_ U L X).inv ≫ (n ▷ X)) ≫
      (m ▷ X) ≫ (α_ U L X).hom ≫ (U ◁ (f ▷ X)) := by rw [hu]
    _ = 𝟙 U ⊗≫ (U ◁ η_ L X) ⊗≫ ((n ≫ m) ▷ X) ⊗≫ (U ◁ (f ▷ X)) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by monoidal
    _ = 𝟙 U ⊗≫ (U ◁ (η_ L X ≫ (f ▷ X))) ⊗≫ 𝟙 (U ⊗ (D ⊗ X)) := by rw [hm]; monoidal
    _ = _ := by rw [← hc]; monoidal

set_option backward.isDefEq.respectTransparency false in
/-- If the normalized crossing is monoidal, the chosen coevaluation is a
morphism in the actual centre, without further hypotheses. -/
theorem coevaluation_central (Z : Center C)
    (hTensor : ∀ U V : C, ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
        (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫
          (α_ _ _ _).inv) (U : C) :
    ((η_ Z.1 Z.1ᘁ) ▷ U) ≫ ((Z ⊗ dualObject Z hTensor).2.β U).hom =
      ((𝟙_ (Center C)).2.β U).hom ≫ (U ◁ η_ Z.1 Z.1ᘁ) := by
  have h := coevaluation_sliding Z U
  change (η_ Z.1 Z.1ᘁ ▷ U) ≫
    ((α_ Z.1 Z.1ᘁ U).hom ≫ (Z.1 ◁ ((Integrate.dualCrossingIso Z).app U).hom) ≫
      (α_ Z.1 U Z.1ᘁ).inv ≫ ((Z.2.β U).hom ▷ Z.1ᘁ) ≫ (α_ U Z.1 Z.1ᘁ).hom) =
    ((λ_ U).hom ≫ (ρ_ U).inv) ≫ (U ◁ η_ Z.1 Z.1ᘁ)
  calc
    _ = (λ_ U).hom ≫ (𝟙 U ⊗≫ (η_ Z.1 Z.1ᘁ ▷ U) ⊗≫
      (Z.1 ◁ (show Z.1ᘁ ⊗ U ⟶ U ⊗ Z.1ᘁ from ((Integrate.dualCrossingIso Z).app U).hom)) ⊗≫
      ((Z.2.β U).hom ▷ Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ (Z.1 ⊗ Z.1ᘁ))) := by monoidal
    _ = (λ_ U).hom ≫ (𝟙 U ⊗≫ (U ◁ η_ Z.1 Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ (Z.1 ⊗ Z.1ᘁ))) := by rw [h]
    _ = _ := by monoidal

end PropertyF.Ground.CentreRigid
