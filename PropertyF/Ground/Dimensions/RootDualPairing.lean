module
public import PropertyF.Ground.Dimensions.RootUnitComponent

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- On a simple and its right dual the root carries the ordinary duality cup
to the double-dual cup, with the ENO sign. -/
theorem root_components_coevaluation (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) :
    let X := Ground.simples C i
    η_ X (Xᘁ) ≫ (((fourthDualRootNaturalIso C).app X).hom ⊗ₘ
      ((fourthDualRootNaturalIso C).app (Xᘁ)).hom) =
      rootDualSign C i • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) := by
  let X := Ground.simples C i
  let a : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  let e := rootDualSign C i
  have ha : ((fourthDualRootNaturalIso C).app (Xᘁ)).hom = e • ((a.invᘁ)) := by
    exact rootDualSign_component C i
  change η_ X (Xᘁ) ≫ (a.hom ⊗ₘ ((fourthDualRootNaturalIso C).app (Xᘁ)).hom) =
    e • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)
  rw [ha]
  simp only [tensorHom_def, MonoidalLinear.whiskerLeft_smul, Linear.comp_smul]
  congr 1
  have h := coevaluation_comp_rightAdjointMate a.inv
  calc
    _ = η_ X (Xᘁ) ≫ X ◁ (a.invᘁ) ≫ a.hom ▷ (((Xᘁ)ᘁ)ᘁ) := by
      simpa only [doubleDualFunctor, Functor.id_obj, Category.assoc] using
        congrArg (fun z => η_ X (Xᘁ) ≫ z) (whisker_exchange a.hom (a.invᘁ)).symm
    _ = η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) ≫ a.inv ▷ (((Xᘁ)ᘁ)ᘁ) ≫
        a.hom ▷ (((Xᘁ)ᘁ)ᘁ) := by
      simpa only [doubleDualFunctor, Functor.id_obj, Category.assoc] using
        congrArg (fun z => z ≫ a.hom ▷ (((Xᘁ)ᘁ)ᘁ)) h
    _ = _ := by
      have hi : (a.inv ▷ (((Xᘁ)ᘁ)ᘁ)) ≫ a.hom ▷ (((Xᘁ)ᘁ)ᘁ) = 𝟙 _ := by
        rw [← comp_whiskerRight, Iso.inv_hom_id, id_whiskerRight]
      simp only [hi, Category.comp_id]
/-- The corresponding evaluation is transported by the same ENO sign. -/
theorem root_components_evaluation (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) :
    let X := Ground.simples C i
    (((fourthDualRootNaturalIso C).app (Xᘁ)).hom ⊗ₘ
      ((fourthDualRootNaturalIso C).app X).hom) ≫
        ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) = rootDualSign C i • ε_ X (Xᘁ) := by
  let X := Ground.simples C i
  let a : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  let e := rootDualSign C i
  have ha : ((fourthDualRootNaturalIso C).app (Xᘁ)).hom = e • ((a.invᘁ)) := by
    exact rootDualSign_component C i
  change (((fourthDualRootNaturalIso C).app (Xᘁ)).hom ⊗ₘ a.hom) ≫
    ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) = e • ε_ X (Xᘁ)
  rw [ha]
  change ((e • (a.invᘁ)) ⊗ₘ a.hom) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) = e • ε_ X (Xᘁ)
  simp only [tensorHom_def, MonoidalLinear.smul_whiskerRight, Linear.smul_comp]
  congr 1
  have h := rightAdjointMate_comp_evaluation a.inv
  calc
    _ = (Xᘁ) ◁ a.hom ≫ ((a.invᘁ) ▷ ((Xᘁ)ᘁ) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)) := by
      simpa only [doubleDualFunctor, Functor.id_obj, Category.assoc] using
        congrArg (fun z => z ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)) (whisker_exchange (a.invᘁ) a.hom).symm
    _ = (Xᘁ) ◁ a.hom ≫ ((Xᘁ) ◁ a.inv ≫ ε_ X (Xᘁ)) := by rw [h]
    _ = _ := by simp only [← Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id,
      whiskerLeft_id, Category.id_comp]

/-- The ENO root carries the braided-swapped duality cup to the corresponding
double-dual cup with the same sign. -/
theorem root_components_swapped_coevaluation (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) :
    let X := Ground.simples C i
    letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
    letI : ExactPairing (((Xᘁ)ᘁ)ᘁ) ((Xᘁ)ᘁ) :=
      BraidedCategory.exactPairing_swap ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)
    η_ (Xᘁ) X ≫ (((fourthDualRootNaturalIso C).app (Xᘁ)).hom ⊗ₘ
      ((fourthDualRootNaturalIso C).app X).hom) =
      rootDualSign C i • η_ (((Xᘁ)ᘁ)ᘁ) ((Xᘁ)ᘁ) := by
  let X := Ground.simples C i
  let a := (fourthDualRootNaturalIso C).app X
  let b := (fourthDualRootNaturalIso C).app (Xᘁ)
  let : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  let : ExactPairing (((Xᘁ)ᘁ)ᘁ) ((Xᘁ)ᘁ) :=
    BraidedCategory.exactPairing_swap ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)
  change (η_ X (Xᘁ) ≫ (β_ (Xᘁ) X).inv) ≫ (b.hom ⊗ₘ a.hom) =
    rootDualSign C i • (η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) ≫
      (β_ (((Xᘁ)ᘁ)ᘁ) ((Xᘁ)ᘁ)).inv)
  have hn := braiding_inv_naturality a.hom b.hom
  have hc := root_components_coevaluation C i
  change η_ X (Xᘁ) ≫ (a.hom ⊗ₘ b.hom) =
    rootDualSign C i • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) at hc
  calc
    _ = η_ X (Xᘁ) ≫ ((a.hom ⊗ₘ b.hom) ≫
        (β_ (((Xᘁ)ᘁ)ᘁ) ((Xᘁ)ᘁ)).inv) := by
      simpa only [doubleDualFunctor, Functor.id_obj, Category.assoc] using
        (congrArg (fun f => η_ X (Xᘁ) ≫ f) hn).symm
    _ = _ := by
      simpa only [doubleDualFunctor, Category.assoc, Linear.smul_comp] using
        congrArg (fun f => f ≫ (β_ (((Xᘁ)ᘁ)ᘁ) ((Xᘁ)ᘁ)).inv) hc

/-- The ENO root also transports the braided-swapped evaluation with its sign. -/
theorem root_components_swapped_evaluation (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) :
    let X := Ground.simples C i
    letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
    letI : ExactPairing (((Xᘁ)ᘁ)ᘁ) ((Xᘁ)ᘁ) :=
      BraidedCategory.exactPairing_swap ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)
    (((fourthDualRootNaturalIso C).app X).hom ⊗ₘ
      ((fourthDualRootNaturalIso C).app (Xᘁ)).hom) ≫
        ε_ (((Xᘁ)ᘁ)ᘁ) ((Xᘁ)ᘁ) = rootDualSign C i • ε_ (Xᘁ) X := by
  let X := Ground.simples C i
  let a := (fourthDualRootNaturalIso C).app X
  let b := (fourthDualRootNaturalIso C).app (Xᘁ)
  let : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  let : ExactPairing (((Xᘁ)ᘁ)ᘁ) ((Xᘁ)ᘁ) :=
    BraidedCategory.exactPairing_swap ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)
  change (a.hom ⊗ₘ b.hom) ≫
      ((β_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)).hom ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)) =
    rootDualSign C i • ((β_ X (Xᘁ)).hom ≫ ε_ X (Xᘁ))
  have hn := braiding_naturality a.hom b.hom
  have hc := root_components_evaluation C i
  change (b.hom ⊗ₘ a.hom) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) =
    rootDualSign C i • ε_ X (Xᘁ) at hc
  calc
    _ = (β_ X (Xᘁ)).hom ≫ ((b.hom ⊗ₘ a.hom) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)) := by
      simpa only [doubleDualFunctor, Functor.id_obj, Category.assoc] using
        congrArg (fun f => f ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)) hn
    _ = _ := by rw [hc, Linear.comp_smul]

end PropertyF.Ground.Dimensions
