module
public import PropertyF.Ground.CentreCalculus.LeftTensorTrace

/-!
# Twist signs and integral dimensions

The inverse-braiding trace identifies the inverse pivotal twist. On a
self-transparent simple object the twist is a sign, giving integral dimension.
We write `θ C p X` for the pivotal twist scalar.
-/
@[expose] public noncomputable section
local notation "θ" => PropertyF.Ground.Dimensions.pivotalBraidedTwistScalar
open PropertyF.Ground.Modular (HasFPSimpleDimensions IsFPSpherical)
open PropertyF.Ground.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := C.Obj)}
  (hp : p.IsSpherical) (hdim : HasFPSimpleDimensions C p)

section
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [BraidedCategory D] [RightRigidCategory D]
variable {p : PivotalStructure (C := D)}

/-- The braided comparison from an object to its double right dual. -/
abbrev braidedDoubleDualIso (X : D) : X ≅ (Xᘁ)ᘁ :=
  rightDualIso (BraidedCategory.exactPairing_swap X (Xᘁ)) inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The coevaluation characterizing the braided double-dual map. -/
theorem drinfeld_coevaluation (X : D) :
    η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (braidedDoubleDualIso X).inv =
      η_ X (Xᘁ) ≫ (β_ (Xᘁ) X).inv := by
  let q : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  let h : ExactPairing (Xᘁ) ((Xᘁ)ᘁ) := HasRightDual.exact
  have hc := Dimensions.coevaluation_rightDualIso q h
  change (η_ X (Xᘁ) ≫ (β_ (Xᘁ) X).inv) ≫
    (Xᘁ) ◁ (braidedDoubleDualIso X).hom = η_ (Xᘁ) ((Xᘁ)ᘁ) at hc
  rw [← hc, Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.comp_id]

/-- Pivotal coevaluation factors through the braided double-dual comparison. -/
theorem pivotal_coevaluation_factor (X : D) :
    η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv =
      (η_ X (Xᘁ) ≫ (β_ (Xᘁ) X).inv) ≫
        (Xᘁ) ◁ ((braidedDoubleDualIso X).hom ≫ (p.iso X).inv) := by
  rw [← drinfeld_coevaluation X, Category.assoc, ← whiskerLeft_comp,
    Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse braiding cancels along the duality snake. -/
theorem inverse_crossing_snake (X : D) :
    (λ_ X).inv ≫ (η_ X (Xᘁ) ▷ X) ≫ ((β_ (Xᘁ) X).inv ▷ X) ≫
      (α_ (Xᘁ) X X).hom ≫ (Xᘁ ◁ (β_ X X).inv) ≫ (α_ (Xᘁ) X X).inv ≫
      (ε_ X (Xᘁ) ▷ X) ≫ (λ_ X).hom = 𝟙 X := by
  calc
    _ = (λ_ X).inv ≫ (η_ X (Xᘁ) ▷ X) ≫ (α_ X (Xᘁ) X).hom ≫
        ((β_ (Xᘁ ⊗ X) X).inv ≫ ε_ X (Xᘁ) ▷ X) ≫ (λ_ X).hom := by
          simp [braiding_tensor_left_inv, Category.assoc]
    _ = (λ_ X).inv ≫ (η_ X (Xᘁ) ▷ X) ≫ (α_ X (Xᘁ) X).hom ≫
        X ◁ ε_ X (Xᘁ) ≫ (β_ (𝟙_ D) X).inv ≫ (λ_ X).hom := by
          rw [← braiding_inv_naturality_right]
          simp [Category.assoc]
    _ = 𝟙 X := by
      rw [ExactPairing.evaluation_coevaluation_assoc]
      simp

variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

set_option backward.isDefEq.respectTransparency false in
/-- Closing the first strand of the inverse braiding gives the inverse
pivotal/Drinfeld twist. -/
theorem leftPartialTrace_inverse_braiding (X : D) :
    leftPartialTrace p (End.of (β_ X X).inv) =
      End.of ((braidedDoubleDualIso X).hom ≫ (p.iso X).inv) := by
  apply End.ext
  simp only [leftPartialTrace, LinearMap.coe_mk, AddHom.coe_mk]
  let t : X ⟶ X := (braidedDoubleDualIso X).hom ≫ (p.iso X).inv
  rw [pivotal_coevaluation_factor (p := p) X]
  simp only [comp_whiskerRight, Category.assoc]
  -- The inverse crossings cancel after applying the inverse hexagon.
  have hmove : (Xᘁ ◁ t) ▷ X ≫ (α_ (Xᘁ) X X).hom ≫ (Xᘁ ◁ (β_ X X).inv) =
      (α_ (Xᘁ) X X).hom ≫ (Xᘁ ◁ (β_ X X).inv) ≫ (Xᘁ ◁ (X ◁ t)) := by
    rw [associator_naturality_middle_assoc]
    simp only [← whiskerLeft_comp, braiding_inv_naturality_left]
  slice_lhs 4 6 => rw [hmove]
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc (ε_ X (Xᘁ)) t,
    leftUnitor_naturality]
  change _ = t
  simpa only [Category.assoc, Category.id_comp] using congrArg (fun f => f ≫ t) (inverse_crossing_snake X)

end

include hp in
/-- On a self-transparent simple, the inverse twist is its twist scalar. -/
theorem inverse_twist_eq_scalar_of_selfTransparent {X : C.Obj} [Simple X]
    (hX : SelfTransparent X) :
    (doubleDualIso C X).hom ≫ (p.iso X).inv =
      θ C p X • 𝟙 X :=
  (congrArg End.asHom (show θ C p X • (1 : End X) = _ from by
    simpa only [← ((β_ X X).inv_ext' hX), leftPartialTrace_braiding_of_trace_compatibility
      (spherical_rightTrace_leftPartialTrace p hp (End.of (β_ X X).hom)),
      braidedDoubleDualIso, doubleDualIso] using
      leftPartialTrace_inverse_braiding (p := p) X)).symm

include hp in
/-- In a spherical category, the twist of a self-transparent simple is a sign. -/
theorem pivotalTwist_sign_of_selfTransparent {X : C.Obj} [Simple X]
    (hX : SelfTransparent X) :
    θ C p X = 1 ∨
      θ C p X = -1 := by
  have ht : ((doubleDualIso C X).hom ≫ (p.iso X).inv) ≫
      (Dimensions.pivotalBraidedTwist C p X).hom = 𝟙 X := by
    simp [Dimensions.pivotalBraidedTwist, Category.assoc]
  rw [inverse_twist_eq_scalar_of_selfTransparent (C := C) hp hX,
    Dimensions.pivotalBraidedTwist_simple] at ht
  apply mul_self_eq_one_iff.mp
  apply smul_left_injective ℂ (id_nonzero X)
  simpa only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, one_smul] using ht

/-- Every self-transparent simple has integral FP dimension in an FP-valued
spherical braided fusion category. -/
theorem selfTransparent_simple_integral (hfp : IsFPSpherical C p) {X : C.Obj} [Simple X]
    (hX : SelfTransparent X) :
    ∃ m : ℕ, fpDimension C X = m :=
  integral_of_spherical_and_twist_sign hfp hX
    (pivotalTwist_sign_of_selfTransparent (C := C) hfp.1 hX)

/-- The complex categorical dimension of a self-transparent simple label is
an integer. -/
theorem selfTransparent_simpleDimension_integer (hfp : IsFPSpherical C p) {i : Fin (rank C)}
    (hX : SelfTransparent (simples C i)) :
    ∃ z : ℤ, Modular.simpleDimension C p i = z :=
  let : Simple (simples C i) := simples_simple C i
  let ⟨m, hm⟩ := selfTransparent_simple_integral hfp hX
  ⟨m, by simp [hfp.2 i, ← fpDimension_simple C i, hm]⟩

end PropertyF.Ground.CentreCalculus
