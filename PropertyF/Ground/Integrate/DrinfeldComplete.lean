module
public import PropertyF.Ground.CentreCabling.ImageCore
public import PropertyF.Ground.Integrate.ActualCenterReduction
public import PropertyF.Ground.CentreInduction.ActualFusion
public import PropertyF.Ground.CentreInduction.PositivePivotal
public import PropertyF.Ground.Centre.Rigid
public import PropertyF.Ground.CentreInduction.ForgetDual
public import PropertyF.Ground.CentreInduction.PivotalCentrality
public import PropertyF.Ground.Centre.Modular.Vafa
public import PropertyF.Ground.CentreModular.TransparencyCriterion
public import PropertyF.Ground.CentreIntegrate.TwistBalancing
public import PropertyF.Ground.Dimensions.MonodromyTensorCap

section
/-! The constructed induction adjunction removes the centre square premise. -/

@[expose] public noncomputable section
open CategoryTheory
namespace PropertyF.Ground
universe v u

variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)] [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵ᶠ" => Integrate.bundledCenter C

/-- The centre square follows from its actual induction adjunction as soon as
its genuine fusion structure and FP-valued spherical structure are available. -/
theorem center_globalDimension_square_of_actual_induction
    {p : Dimensions.PivotalStructure (C := 𝒵ᶠ.Obj)}
    (hp : p.IsSpherical)
    (hdim : Modular.HasFPSimpleDimensions 𝒵ᶠ p) :
    globalDimension 𝒵ᶠ = (globalFPDimension C : ℂ) ^ 2 :=
  (Modular.categorical_global_eq_sum_squares 𝒵ᶠ p hp).trans <| by
    simpa [globalFPDimension, hdim, Complex.ofReal_sum, Complex.ofReal_pow] using
      congrArg (fun x : ℝ ↦ (x : ℂ)) (CentreInduction.globalFPDimension_square_of_actual_induction C)

end PropertyF.Ground
end
end

/-! # Pivotal and balancing reductions

The pivotal, balancing and transparency arguments supply the final reduction. -/

section

/-! Trivial centre transparency is constructed from actual induction. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

variable (C : BraidedFusionCategory.{v,u})
variable [RigidCategory (CategoryTheory.Center C.Obj)] [IsFusionCategory (CategoryTheory.Center C.Obj)]
local notation "𝒵ᶠ" => Integrate.bundledCenter C

/-- The actual rigid fusion centre has no non-unit transparent simple. -/
theorem center_transparent_label_eq_unit
    (k : Fin (rank 𝒵ᶠ))
    (hk : Transparent (simples 𝒵ᶠ k)) :
    k = unitIndex 𝒵ᶠ :=
  let : Simple (simples 𝒵ᶠ k) := simples_simple _ k
  simples_injective _ ⟨(CentreInduction.center_transparent_simple_iso_unit (C := C) hk).some ≪≫
    (unitIndex_iso 𝒵ᶠ).some.symm⟩

end PropertyF.Ground
end
end

section
/-! The proved cap diagram supplies Drinfeld tensor coherence and balancing. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground
universe v u
set_option linter.style.haveILetI false

/-- The actual Drinfeld map has the tensor coherence law in any braided
fusion category. -/
theorem drinfeld_tensor (C : BraidedFusionCategory.{v,u}) (X Y : C.Obj) :
    Modular.doubleBraiding X Y ≫ (doubleDualIso C (X ⊗ Y)).hom =
      ((doubleDualIso C X).hom ⊗ₘ (doubleDualIso C Y).hom) ≫
        (Dimensions.doubleDualTensorIso X Y).hom :=
  CentreIntegrate.drinfeld_tensor_of_pairing_cap (doubleDualIso C)
    (Dimensions.drinfeld_eval C (X ⊗ Y)) (Dimensions.drinfeld_tensor_pairing_cap C X Y)

/-- The twist of any pivotal braided fusion category is balanced. -/
theorem pivotal_twist_balanced (C : BraidedFusionCategory.{v,u})
    (p : Dimensions.PivotalStructure (C := C.Obj)) (X Y : C.Obj) :
    Modular.doubleBraiding X Y ≫
      ((Dimensions.pivotalBraidedTwist C p X).hom ⊗ₘ
        (Dimensions.pivotalBraidedTwist C p Y).hom) =
      (Dimensions.pivotalBraidedTwist C p (X ⊗ Y)).hom :=
  CentreIntegrate.pivotal_balance_of_drinfeld_tensor p (doubleDualIso C) (drinfeld_tensor C X Y)

end PropertyF.Ground
end
end
