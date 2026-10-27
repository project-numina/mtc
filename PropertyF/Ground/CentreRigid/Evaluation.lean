module
public import PropertyF.Ground.CentreRigid.Tensor

/-! Evaluation centrality and rigidity of the Drinfeld centre. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ExactPairing
namespace PropertyF.Ground.CentreRigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- The normalized dual crossing intertwines the evaluation. -/
theorem evaluation_sliding (Z : Center C) (U : C) :
    𝟙 ((Z.1ᘁ ⊗ Z.1) ⊗ U) ⊗≫ (ε_ Z.1 Z.1ᘁ ▷ U) ⊗≫ 𝟙 (U ⊗ (𝟙_ C)) =
    𝟙 ((Z.1ᘁ ⊗ Z.1) ⊗ U) ⊗≫ (Z.1ᘁ ◁ (Z.2.β U).hom) ⊗≫
      (show Z.1ᘁ ⊗ U ⟶ U ⊗ Z.1ᘁ from ((Integrate.dualCrossingIso Z).app U).hom) ▷ Z.1 ⊗≫
      (U ◁ ε_ Z.1 Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ (𝟙_ C)) := by
  let X := Z.1
  let D : C := Z.1ᘁ
  let c : X ⊗ U ⟶ U ⊗ X := (Z.2.β U).hom
  let cInv : U ⊗ X ⟶ X ⊗ U := (Z.2.β U).inv
  let d : D ⊗ U ⟶ U ⊗ D := ((Integrate.dualCrossingIso Z).app U).hom
  have hslide := CentreRigid.coevaluation_sliding Z U
  apply (cancel_epi (α_ D X U).inv).1
  apply (tensorLeftHomEquiv (X ⊗ U) X D (U ⊗ (𝟙_ C))).injective
  apply (cancel_epi cInv).1
  apply (cancel_mono ((X ◁ (ρ_ U).hom) ≫ c)).1
  simp only [tensorLeftHomEquiv, Equiv.coe_fn_mk]
  calc
    _ = 𝟙 (U ⊗ X) := by
      calc
        _ = 𝟙 (U ⊗ X) ⊗≫ cInv ⊗≫
          ((η_ X D ▷ X ⊗≫ X ◁ ε_ X D) ▷ U) ⊗≫ c ⊗≫ 𝟙 (U ⊗ X) := by monoidal
        _ = 𝟙 (U ⊗ X) ⊗≫ (cInv ≫ c) ⊗≫ 𝟙 (U ⊗ X) := by rw [evaluation_coevaluation'']; monoidal
        _ = _ := by dsimp [cInv, c]; simp [monoidalComp]
    _ = _ := by
      symm
      have hc : cInv ≫ c = 𝟙 (U ⊗ X) := by simp [cInv, c, X]
      change 𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ d) ⊗≫ (c ▷ D) ⊗≫ 𝟙 (U ⊗ (X ⊗ D)) =
        𝟙 U ⊗≫ (U ◁ η_ X D) ⊗≫ 𝟙 (U ⊗ (X ⊗ D)) at hslide
      calc
        _ = 𝟙 (U ⊗ X) ⊗≫ (((𝟙_ C) ◁ cInv) ≫ (η_ X D ▷ (X ⊗ U))) ⊗≫
          (X ◁ (D ◁ c)) ⊗≫ (X ◁ (d ▷ X)) ⊗≫ (X ◁ (U ◁ ε_ X D)) ⊗≫ c ⊗≫ 𝟙 (U ⊗ X) := by monoidal
        _ = 𝟙 (U ⊗ X) ⊗≫ ((η_ X D ▷ (U ⊗ X)) ≫ ((X ⊗ D) ◁ cInv)) ⊗≫
          (X ◁ (D ◁ c)) ⊗≫ (X ◁ (d ▷ X)) ⊗≫ (X ◁ (U ◁ ε_ X D)) ⊗≫ c ⊗≫ 𝟙 (U ⊗ X) := by rw [whisker_exchange]
        _ = 𝟙 (U ⊗ X) ⊗≫ (η_ X D ▷ (U ⊗ X)) ⊗≫
          (X ◁ (D ◁ (cInv ≫ c))) ⊗≫ (X ◁ (d ▷ X)) ⊗≫ (X ◁ (U ◁ ε_ X D)) ⊗≫ c ⊗≫ 𝟙 (U ⊗ X) := by monoidal
        _ = 𝟙 (U ⊗ X) ⊗≫ (η_ X D ▷ (U ⊗ X)) ⊗≫
          (X ◁ (d ▷ X)) ⊗≫ (X ◁ (U ◁ ε_ X D)) ⊗≫ c ⊗≫ 𝟙 (U ⊗ X) := by rw [hc]; monoidal
        _ = 𝟙 (U ⊗ X) ⊗≫ ((η_ X D ▷ U) ▷ X) ⊗≫ ((X ◁ d) ▷ X) ⊗≫
          (((X ⊗ U) ◁ ε_ X D) ≫ (c ▷ (𝟙_ C))) ⊗≫ 𝟙 (U ⊗ X) := by monoidal
        _ = 𝟙 (U ⊗ X) ⊗≫ ((η_ X D ▷ U) ▷ X) ⊗≫ ((X ◁ d) ▷ X) ⊗≫
          ((c ▷ (D ⊗ X)) ≫ ((U ⊗ X) ◁ ε_ X D)) ⊗≫ 𝟙 (U ⊗ X) := by rw [whisker_exchange]
        _ = 𝟙 (U ⊗ X) ⊗≫ ((𝟙 U ⊗≫ (η_ X D ▷ U) ⊗≫ (X ◁ d) ⊗≫ (c ▷ D) ⊗≫ 𝟙 (U ⊗ (X ⊗ D))) ▷ X) ⊗≫
          (U ◁ (X ◁ ε_ X D)) ⊗≫ 𝟙 (U ⊗ X) := by monoidal
        _ = 𝟙 (U ⊗ X) ⊗≫ ((𝟙 U ⊗≫ (U ◁ η_ X D) ⊗≫ 𝟙 (U ⊗ (X ⊗ D))) ▷ X) ⊗≫
          (U ◁ (X ◁ ε_ X D)) ⊗≫ 𝟙 (U ⊗ X) := by rw [hslide]
        _ = 𝟙 (U ⊗ X) ⊗≫ (U ◁ (η_ X D ▷ X ⊗≫ X ◁ ε_ X D)) ⊗≫ 𝟙 (U ⊗ X) := by monoidal
        _ = _ := by rw [evaluation_coevaluation'']; monoidal

set_option backward.isDefEq.respectTransparency false in
/-- The chosen base evaluation is a morphism of actual centre objects. -/
theorem evaluation_central (Z : Center C)
    (hTensor : ∀ U V : C, ((Integrate.dualCrossingIso Z).app (U ⊗ V)).hom =
      (α_ _ _ _).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ V) ≫
        (α_ _ _ _).hom ≫ (U ◁ ((Integrate.dualCrossingIso Z).app V).hom) ≫
          (α_ _ _ _).inv) (U : C) :
    ((ε_ Z.1 Z.1ᘁ) ▷ U) ≫ ((𝟙_ (Center C)).2.β U).hom =
      ((dualObject Z hTensor ⊗ Z).2.β U).hom ≫ (U ◁ ε_ Z.1 Z.1ᘁ) := by
  have h := evaluation_sliding Z U
  change (ε_ Z.1 Z.1ᘁ ▷ U) ≫ ((λ_ U).hom ≫ (ρ_ U).inv) =
    ((α_ Z.1ᘁ Z.1 U).hom ≫ (Z.1ᘁ ◁ (Z.2.β U).hom) ≫
      (α_ Z.1ᘁ U Z.1).inv ≫ (((Integrate.dualCrossingIso Z).app U).hom ▷ Z.1) ≫
      (α_ U Z.1ᘁ Z.1).hom) ≫ (U ◁ ε_ Z.1 Z.1ᘁ)
  calc
    _ = (𝟙 ((Z.1ᘁ ⊗ Z.1) ⊗ U) ⊗≫ (ε_ Z.1 Z.1ᘁ ▷ U) ⊗≫ 𝟙 (U ⊗ (𝟙_ C))) := by monoidal
    _ = (𝟙 ((Z.1ᘁ ⊗ Z.1) ⊗ U) ⊗≫ (Z.1ᘁ ◁ (Z.2.β U).hom) ⊗≫
      (show Z.1ᘁ ⊗ U ⟶ U ⊗ Z.1ᘁ from ((Integrate.dualCrossingIso Z).app U).hom) ▷ Z.1 ⊗≫
      (U ◁ ε_ Z.1 Z.1ᘁ) ⊗≫ 𝟙 (U ⊗ (𝟙_ C))) := h
    _ = _ := by monoidal

/-- The actual Drinfeld centre of a rigid monoidal category is rigid. -/
@[instance_reducible] def rigidCenter : RigidCategory (Center C) := by
  apply rigidOfMateCoherence
  intro Z
  refine ⟨dualCrossing_tensor Z, coevaluation_central Z (dualCrossing_tensor Z),
    evaluation_central Z (dualCrossing_tensor Z)⟩

set_option backward.isDefEq.respectTransparency false in
/-- The right dual chosen in the centre forgets to the chosen base dual. -/
theorem rigidCenter_forget_dual (Z : Center C) :
    letI := rigidCenter (C := C)
    (Zᘁ).1 = Z.1ᘁ := by rfl

set_option backward.isDefEq.respectTransparency false in
/-- The centre coevaluation forgets to the base coevaluation. -/
theorem rigidCenter_forget_coevaluation (Z : Center C) :
    letI := rigidCenter (C := C)
    (η_ Z (Zᘁ)).f = η_ Z.1 Z.1ᘁ := by rfl

set_option backward.isDefEq.respectTransparency false in
/-- The centre evaluation forgets to the base evaluation. -/
theorem rigidCenter_forget_evaluation (Z : Center C) :
    letI := rigidCenter (C := C)
    (ε_ Z (Zᘁ)).f = ε_ Z.1 Z.1ᘁ := by rfl

end PropertyF.Ground.CentreRigid
