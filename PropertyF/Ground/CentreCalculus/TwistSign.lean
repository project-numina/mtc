module
public import PropertyF.Ground.CentreCalculus.LeftTensorTrace

/-! The twist sign and integral dimensions of self-transparent simples. -/
@[expose] public noncomputable section
open PropertyF.Ground.Modular (HasFPSimpleDimensions)
open PropertyF.Ground.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := C.Obj)}
  (hp : p.IsSpherical) (hdim : HasFPSimpleDimensions C p)

set_option backward.isDefEq.respectTransparency false in
/-- The coevaluation characterizing the braided double-dual map. -/
theorem drinfeld_coevaluation (X : C.Obj) :
    η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (doubleDualIso C X).inv =
      η_ X (Xᘁ) ≫ (β_ (Xᘁ) X).inv := by
  let q : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
  let h : ExactPairing (Xᘁ) ((Xᘁ)ᘁ) := HasRightDual.exact
  have hc := Dimensions.coevaluation_rightDualIso q h
  change (η_ X (Xᘁ) ≫ (β_ (Xᘁ) X).inv) ≫
    (Xᘁ) ◁ (doubleDualIso C X).hom = η_ (Xᘁ) ((Xᘁ)ᘁ) at hc
  rw [← hc, Category.assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse braiding cancels along the duality snake. -/
theorem inverse_crossing_snake {D : Type u} [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] [RightRigidCategory D] (X : D) :
    (λ_ X).inv ≫ (η_ X (Xᘁ) ▷ X) ≫ ((β_ (Xᘁ) X).inv ▷ X) ≫
      (α_ (Xᘁ) X X).hom ≫ (Xᘁ ◁ (β_ X X).inv) ≫ (α_ (Xᘁ) X X).inv ≫
      (ε_ X (Xᘁ) ▷ X) ≫ (λ_ X).hom = 𝟙 X := by
  calc
    _ = (λ_ X).inv ≫ (η_ X (Xᘁ) ▷ X) ≫ (α_ X (Xᘁ) X).hom ≫
        ((β_ (Xᘁ ⊗ X) X).inv ≫ ε_ X (Xᘁ) ▷ X) ≫ (λ_ X).hom := by
          rw [braiding_tensor_left_inv]
          simp [Category.assoc]
    _ = (λ_ X).inv ≫ (η_ X (Xᘁ) ▷ X) ≫ (α_ X (Xᘁ) X).hom ≫
        X ◁ ε_ X (Xᘁ) ≫ (β_ (𝟙_ D) X).inv ≫ (λ_ X).hom := by
          rw [← braiding_inv_naturality_right]
          simp [Category.assoc]
    _ = 𝟙 X := by
      rw [ExactPairing.evaluation_coevaluation_assoc]
      simp

set_option backward.isDefEq.respectTransparency false in
/-- Closing the first strand of the inverse braiding gives the inverse
pivotal/Drinfeld twist. -/
theorem leftPartialTrace_inverse_braiding (X : C.Obj) :
    leftPartialTrace p (End.of (β_ X X).inv) =
      End.of ((doubleDualIso C X).hom ≫ (p.iso X).inv) := by
  apply End.ext
  simp only [leftPartialTrace, LinearMap.coe_mk, AddHom.coe_mk]
  let t : X ⟶ X := (doubleDualIso C X).hom ≫ (p.iso X).inv
  have hcup : η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (Xᘁ) ◁ (p.iso X).inv =
      (η_ X (Xᘁ) ≫ (β_ (Xᘁ) X).inv) ≫ (Xᘁ) ◁ t := by
    dsimp [t]
    rw [← drinfeld_coevaluation (C := C) X, Category.assoc, ← whiskerLeft_comp,
      Iso.inv_hom_id_assoc]
  rw [hcup]
  simp only [comp_whiskerRight, Category.assoc]
  -- The inverse crossings cancel after applying the inverse hexagon.
  have hmove : (Xᘁ ◁ t) ▷ X ≫ (α_ (Xᘁ) X X).hom ≫ (Xᘁ ◁ (β_ X X).inv) =
      (α_ (Xᘁ) X X).hom ≫ (Xᘁ ◁ (β_ X X).inv) ≫ (Xᘁ ◁ (X ◁ t)) := by
    rw [associator_naturality_middle_assoc]
    simp only [← whiskerLeft_comp, braiding_inv_naturality_left]
  slice_lhs 4 6 => rw [hmove]
  simp only [Category.assoc]
  rw [associator_inv_naturality_right_assoc]
  rw [whisker_exchange_assoc (ε_ X (Xᘁ)) t]
  rw [leftUnitor_naturality]
  change _ = t
  simpa only [Category.assoc, Category.id_comp] using congrArg (fun f => f ≫ t) (inverse_crossing_snake X)

include hp in
/-- On a self-transparent simple, the inverse twist is its twist scalar. -/
theorem inverse_twist_eq_scalar_of_selfTransparent {X : C.Obj} [Simple X]
    (hX : SelfTransparent X) :
    (doubleDualIso C X).hom ≫ (p.iso X).inv =
      pivotalBraidedTwistScalar C p X • 𝟙 X := by
  have h := leftPartialTrace_inverse_braiding (C := C) (p := p) X
  rw [← ((β_ X X).inv_ext' hX), leftPartialTrace_braiding_of_trace_compatibility (C := C)
    (spherical_rightTrace_leftPartialTrace p hp (End.of (β_ X X).hom))] at h
  exact (congrArg End.asHom h).symm

include hp in
/-- In a spherical category, the twist of a self-transparent simple is a sign. -/
theorem pivotalTwist_sign_of_selfTransparent {X : C.Obj} [Simple X]
    (hX : SelfTransparent X) :
    pivotalBraidedTwistScalar C p X = 1 ∨
      pivotalBraidedTwistScalar C p X = -1 := by
  have ht : ((doubleDualIso C X).hom ≫ (p.iso X).inv) ≫
      (Dimensions.pivotalBraidedTwist C p X).hom = 𝟙 X := by
    simp [Dimensions.pivotalBraidedTwist, Category.assoc]
  rw [inverse_twist_eq_scalar_of_selfTransparent (C := C) hp hX,
    Dimensions.pivotalBraidedTwist_simple] at ht
  simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul] at ht
  apply mul_self_eq_one_iff.mp
  apply smul_left_injective ℂ (id_nonzero X)
  simpa using ht

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
  ⟨m, by
    rw [hfp.2 i, ← fpDimension_simple C i, hm]
    norm_cast⟩

end PropertyF.Ground.CentreCalculus
