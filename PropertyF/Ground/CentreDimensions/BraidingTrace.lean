module
public import PropertyF.Ground.Dimensions.FourthDualUnit
public import PropertyF.Ground.Calculus.PartialTrace

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- Closing one strand of the self-braiding gives the pivotal/Drinfeld twist. -/
theorem rightPartialTrace_braiding (C : Ground.BraidedFusionCategory.{v,u})
    (p : PivotalStructure (C := C.Obj)) (X : C.Obj) :
    Calculus.rightPartialTrace p X X (End.of (β_ X X).hom) =
      End.of ((p.iso X).hom ≫ (Ground.doubleDualIso C X).inv) := by
  apply End.ext
  simp only [Calculus.rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk]
  let t : X ⟶ X := (p.iso X).hom ≫ (Ground.doubleDualIso C X).inv
  have hclose : (p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
      t ▷ (Xᘁ) ≫ (β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ) := by
    dsimp [t]
    simp only [comp_whiskerRight_assoc]
    rw [← drinfeld_eval, ← Category.assoc, ← comp_whiskerRight]
    simp
  have hg : (ρ_ X).inv ≫ X ◁ η_ X (Xᘁ) ≫ (α_ X X (Xᘁ)).inv ≫
      (β_ X X).hom ▷ (Xᘁ) ≫ (α_ X X (Xᘁ)).hom ≫
      X ◁ ((p.iso X).hom ▷ (Xᘁ) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ)) ≫ (ρ_ X).hom = t := by
    rw [hclose]
    simp only [whiskerLeft_comp]
    have hs : (α_ X X (Xᘁ)).inv ≫ (β_ X X).hom ▷ (Xᘁ) ≫ (α_ X X (Xᘁ)).hom ≫
        X ◁ (t ▷ (Xᘁ)) = (t ▷ (X ⊗ (Xᘁ))) ≫ (α_ X X (Xᘁ)).inv ≫
          (β_ X X).hom ▷ (Xᘁ) ≫ (α_ X X (Xᘁ)).hom := by
      have hb := braiding_naturality_left t X
      calc
        _ = (α_ X X (Xᘁ)).inv ≫ (((β_ X X).hom ≫ X ◁ t) ▷ (Xᘁ)) ≫
            (α_ X X (Xᘁ)).hom := by simp only [comp_whiskerRight]; monoidal
        _ = (α_ X X (Xᘁ)).inv ≫ ((t ▷ X ≫ (β_ X X).hom) ▷ (Xᘁ)) ≫
            (α_ X X (Xᘁ)).hom := by rw [← hb]
        _ = _ := by simp only [comp_whiskerRight]; monoidal
    simp only [Category.assoc]
    slice_lhs 3 6 => rw [hs]
    simp only [Category.assoc]
    rw [whisker_exchange_assoc]
    rw [← rightUnitor_inv_naturality_assoc]
    have hc : (ρ_ X).inv ≫ X ◁ η_ X (Xᘁ) ≫ (α_ X X (Xᘁ)).inv ≫
        (β_ X X).hom ▷ (Xᘁ) ≫ (α_ X X (Xᘁ)).hom ≫
        X ◁ (β_ X (Xᘁ)).hom ≫ X ◁ ε_ X (Xᘁ) ≫ (ρ_ X).hom = 𝟙 X := by
      slice_lhs 4 6 => rw [← hexagon_forward]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [braiding_naturality_right_assoc]
      rw [rightUnitor_inv_braiding_assoc, ExactPairing.evaluation_coevaluation_assoc]
      simp
    rw [hc, Category.comp_id]
  simpa only [whiskerLeft_comp, Category.assoc, t] using hg
end PropertyF.Ground.Dimensions
