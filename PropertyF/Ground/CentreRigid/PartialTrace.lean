module
public import PropertyF.Ground.CentreInduction.PartialTrace

/-! Dinaturality of the pivotal partial trace in the closed strand. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.ExactPairing
namespace PropertyF.Ground.CentreRigid
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
set_option backward.isDefEq.respectTransparency false in
/-- The pivotal cap is dinatural in its strand. -/
theorem cap_natural (p : Dimensions.PivotalStructure (C := C)) {T S : C} (f : T ⟶ S) :
  (f ▷ Sᘁ) ≫ ((p.iso S).hom ▷ Sᘁ) ≫ ε_ (Sᘁ) ((Sᘁ)ᘁ) =
    (T ◁ fᘁ) ≫ ((p.iso T).hom ▷ Tᘁ) ≫ ε_ (Tᘁ) ((Tᘁ)ᘁ) := by
  have hp := p.naturality f
  have hm := rightAdjointMate_comp_evaluation (fᘁ)
  rw [← comp_whiskerRight_assoc, hp, comp_whiskerRight_assoc, hm]
  rw [whisker_exchange_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Moving a morphism around the closed tensor factor leaves partial trace unchanged. -/
theorem partialTraceHom_dinatural (p : Dimensions.PivotalStructure (C := C)) (X Y : C) {T S : C}
    (f : T ⟶ S) (g : X ⊗ S ⟶ Y ⊗ T) :
    CentreInduction.partialTraceHom p X Y T ((X ◁ f) ≫ g) =
      CentreInduction.partialTraceHom p X Y S (g ≫ (Y ◁ f)) := by
  have hc := coevaluation_comp_rightAdjointMate f
  have he := cap_natural p f
  let capT : T ⊗ Tᘁ ⟶ 𝟙_ C := ((p.iso T).hom ▷ Tᘁ) ≫ ε_ (Tᘁ) ((Tᘁ)ᘁ)
  let capS : S ⊗ Sᘁ ⟶ 𝟙_ C := ((p.iso S).hom ▷ Sᘁ) ≫ ε_ (Sᘁ) ((Sᘁ)ᘁ)
  change (f ▷ Sᘁ) ≫ capS = (T ◁ fᘁ) ≫ capT at he
  simp only [CentreInduction.partialTraceHom, LinearMap.coe_mk, AddHom.coe_mk]
  have hh : (ρ_ X).inv ≫ (X ◁ η_ T (Tᘁ)) ≫ (α_ X T (Tᘁ)).inv ≫
    (((X ◁ f) ≫ g) ▷ Tᘁ) ≫ (α_ Y T (Tᘁ)).hom ≫ (Y ◁ capT) ≫ (ρ_ Y).hom =
    (ρ_ X).inv ≫ (X ◁ η_ S (Sᘁ)) ≫ (α_ X S (Sᘁ)).inv ≫
    ((g ≫ (Y ◁ f)) ▷ Sᘁ) ≫ (α_ Y S (Sᘁ)).hom ≫ (Y ◁ capS) ≫ (ρ_ Y).hom := by
    calc
      _ = 𝟙 X ⊗≫ (X ◁ (η_ T (Tᘁ) ≫ (f ▷ Tᘁ))) ⊗≫ (g ▷ Tᘁ) ⊗≫ (Y ◁ capT) ⊗≫ 𝟙 Y := by monoidal
      _ = 𝟙 X ⊗≫ (X ◁ (η_ S (Sᘁ) ≫ (S ◁ fᘁ))) ⊗≫ (g ▷ Tᘁ) ⊗≫ (Y ◁ capT) ⊗≫ 𝟙 Y := by rw [hc]
      _ = 𝟙 X ⊗≫ (X ◁ η_ S (Sᘁ)) ⊗≫ (((X ⊗ S) ◁ fᘁ) ≫ (g ▷ Tᘁ)) ⊗≫ (Y ◁ capT) ⊗≫ 𝟙 Y := by monoidal
      _ = 𝟙 X ⊗≫ (X ◁ η_ S (Sᘁ)) ⊗≫ ((g ▷ Sᘁ) ≫ ((Y ⊗ T) ◁ fᘁ)) ⊗≫ (Y ◁ capT) ⊗≫ 𝟙 Y := by rw [whisker_exchange]
      _ = 𝟙 X ⊗≫ (X ◁ η_ S (Sᘁ)) ⊗≫ (g ▷ Sᘁ) ⊗≫ (Y ◁ ((T ◁ fᘁ) ≫ capT)) ⊗≫ 𝟙 Y := by monoidal
      _ = 𝟙 X ⊗≫ (X ◁ η_ S (Sᘁ)) ⊗≫ (g ▷ Sᘁ) ⊗≫ (Y ◁ ((f ▷ Sᘁ) ≫ capS)) ⊗≫ 𝟙 Y := by rw [he]
      _ = _ := by monoidal

  simpa only [capT, capS, whiskerLeft_comp, Category.assoc] using hh

set_option backward.isDefEq.respectTransparency false in
/-- Partial trace is invariant under replacing the closed object by an isomorphic one. -/
theorem partialTraceHom_conjugate (p : Dimensions.PivotalStructure (C := C)) (X Y : C) {T S : C}
    (e : T ≅ S) (g : X ⊗ T ⟶ Y ⊗ T) :
    CentreInduction.partialTraceHom p X Y S ((X ◁ e.inv) ≫ g ≫ (Y ◁ e.hom)) =
      CentreInduction.partialTraceHom p X Y T g := by
  have h := partialTraceHom_dinatural p X Y e.hom ((X ◁ e.inv) ≫ g)
  simpa [Category.assoc, ← whiskerLeft_comp] using h.symm

end PropertyF.Ground.CentreRigid
