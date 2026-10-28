module
public import PropertyF.Ground.Dimensions.FourthDualUnit
public import PropertyF.Ground.Dimensions.DualCoherence

/-! # Duality pairing for roots

Components of the fourth-dual root interact with the duality coevaluation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- On a simple and its right dual the root carries the ordinary duality cup
to the double-dual cup, with the ENO sign. -/
theorem root_components_coevaluation
    (i : Fin (rank C)) :
    let X := simples C i
    η_ X (Xᘁ) ≫ (((fourthDualRootNaturalIso C).app X).hom ⊗ₘ
      ((fourthDualRootNaturalIso C).app (Xᘁ)).hom) =
      rootDualSign C i • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) := by
  let X := simples C i
  let a : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  let e := rootDualSign C i
  have ha : ((fourthDualRootNaturalIso C).app (Xᘁ)).hom = e • ((a.invᘁ)) := by
    exact rootDualSign_component C i
  change η_ X (Xᘁ) ≫ (a.hom ⊗ₘ ((fourthDualRootNaturalIso C).app (Xᘁ)).hom) =
    e • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)
  rw [ha]
  simp only [tensorHom_def, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]
  congr 1
  simpa only [tensorHom_def, Category.assoc, doubleDualFunctor, Functor.id_obj] using
    coevaluation_iso_map a

end PropertyF.Ground.Dimensions

end
