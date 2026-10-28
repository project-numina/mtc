module
public import PropertyF.Ground.CentreCalculus.ParityDeletion
public import PropertyF.Ground.CentreDimensions.PivotalTwist
public import PropertyF.Ground.Calculus.ThreeTrace
public import PropertyF.Ground.Dimensions.TensorMultiplicativity
public import PropertyF.Ground.Dimensions.PivotalPseudoUnitary
public import PropertyF.Ground.Dimensions.DualCoherence

/-!
# Left traces of braid crossings

Two-strand and adjacent-crossing traces reduce to pivotal twists and left
partial-trace compatibility. Tensor-duality identities establish that
compatibility in spherical categories.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- Close the first factor using the pivotal left dual. -/
def leftPartialTrace (p : Dimensions.PivotalStructure (C := C)) {X Y : C} :
    End (X ⊗ Y) →ₗ[ℂ] End Y where
  toFun f := End.of ((λ_ Y).inv ≫
    ((η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ ((Xᘁ) ◁ (p.iso X).inv)) ▷ Y) ≫
    (α_ (Xᘁ) X Y).hom ≫ ((Xᘁ) ◁ f.asHom) ≫
    (α_ (Xᘁ) X Y).inv ≫ (ε_ X (Xᘁ) ▷ Y) ≫ (λ_ Y).hom)
  map_add' f g := by
    apply End.ext
    simp
  map_smul' z f := by
    apply End.ext
    simp

/-- Closing the left factor and then tracing agrees with the total trace. -/
abbrev IsLeftTraceCompatible (p : Dimensions.PivotalStructure (C := C)) (X : C) : Prop :=
  ∀ Y (f : End (X ⊗ Y)),
    p.rightTrace (leftPartialTrace p f).asHom = p.rightTrace f.asHom

/-- Inserting a map on the untraced right factor. -/
def insertLeftIdentity (X : C) {Y : C} (a : End Y) : End (X ⊗ Y) :=
  End.of (X ◁ a.asHom)

theorem leftPartialTrace_right (p : Dimensions.PivotalStructure (C := C))
    {X Y : C} (a : End Y) (f : End (X ⊗ Y)) :
    leftPartialTrace p (f * insertLeftIdentity X a) =
      leftPartialTrace p f * a := by
  apply End.ext
  simp only [leftPartialTrace, insertLeftIdentity, LinearMap.coe_mk, AddHom.coe_mk,
    End.mul_asHom, whiskerLeft_comp, Category.assoc]
  rw [← associator_naturality_right_assoc]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]

/-- Closing the first factor commutes with a spectator factor on the right. -/
theorem leftPartialTrace_whiskerRight (p : Dimensions.PivotalStructure (C := C))
    {X Y : C} (Z : C) (f : End (X ⊗ Y)) :
    leftPartialTrace p (End.of
      ((α_ X Y Z).inv ≫ (f.asHom ▷ Z) ≫ (α_ X Y Z).hom)) =
      End.of ((leftPartialTrace p f).asHom ▷ Z) := by
  apply End.ext
  simp only [leftPartialTrace, LinearMap.coe_mk, AddHom.coe_mk,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

/-- Schur's lemma identifies the partial trace on a simple surviving strand
once compatibility with total trace is known. -/
theorem leftPartialTrace_simple_of_trace_compatibility [CategoryTheory.Limits.HasKernels C]
    {X Y : C} [Simple Y] [FiniteDimensional ℂ (Y ⟶ Y)]
    (p : Dimensions.PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ) (f : End (X ⊗ Y))
    (hd : scalar (p.rightTrace (𝟙 Y)) ≠ 0)
    (htrace : p.rightTrace (leftPartialTrace p f).asHom = p.rightTrace f.asHom) :
    leftPartialTrace p f =
      (scalar (p.rightTrace f.asHom) / scalar (p.rightTrace (𝟙 Y))) • (1 : End Y) :=
  (Calculus.simple_end_eq_trace_smul p scalar (leftPartialTrace p f) hd).trans <|
    congrArg (fun t ↦ (scalar t / scalar (p.rightTrace (𝟙 Y))) • (1 : End Y)) htrace

end PropertyF.Ground.CentreCalculus

open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : BraidedFusionCategory.{v,u}} {p : Dimensions.PivotalStructure (C := C.Obj)}
  (hdim : Modular.HasFPSimpleDimensions C p) {X : C.Obj} [Simple X]

/-- Once left partial trace composes with total trace, Schur's lemma computes
the closed crossing as the pivotal twist scalar. -/
theorem leftPartialTrace_braiding_of_trace_compatibility
    (ht : p.rightTrace (leftPartialTrace p (End.of (β_ X X).hom)).asHom =
      p.rightTrace (β_ X X).hom) :
    leftPartialTrace p (End.of (β_ X X).hom) =
      Dimensions.pivotalBraidedTwistScalar C p X • (1 : End X) := by
  let : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  have hd : unitScalarEquiv C (p.rightTrace (𝟙 X)) ≠ 0 := by
    exact Modular.unitScalar_rightTrace_ne_zero C p X
  have hd' : unitScalar C (p.rightTrace (𝟙 X)) ≠ 0 := by
    simpa [unitScalar_eq_equiv] using hd
  have hh := leftPartialTrace_simple_of_trace_compatibility p (unitScalarEquiv C)
    (End.of (β_ X X).hom) hd ht
  simpa only [← unitScalar_eq_equiv, Dimensions.pivotalTrace_selfBraiding,
    Dimensions.pivotalDimension, mul_div_cancel_right₀ _ hd'] using hh

set_option backward.isDefEq.respectTransparency false in
/-- The closed first crossing with any spectator tensor factor is the same
scalar on the entire untraced factor. -/
theorem leftPartialTrace_firstGenerator_of_trace_compatibility
    (n : ℕ)
    (ht : p.rightTrace (leftPartialTrace p (End.of (β_ X X).hom)).asHom =
      p.rightTrace (β_ X X).hom) :
    leftPartialTrace p (Aut.toEnd (braidGenerator X n 0)) =
      Dimensions.pivotalBraidedTwistScalar C p X • 1 := by
  have hg : (Aut.toEnd (braidGenerator X n 0)) = End.of
      ((α_ X X (tensorPower X n)).inv ≫ ((β_ X X).hom ▷ tensorPower X n) ≫
        (α_ X X (tensorPower X n)).hom) := by
    apply End.ext
    change (braidGenerator X n ⟨0, by omega⟩).asIso.hom = _
    simp only [braidGenerator, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
      tensorHom_id]
  change leftPartialTrace p (Aut.toEnd (braidGenerator X n 0)) = _
  dsimp only [tensorPower] at hg ⊢
  rw [hg]
  have hw := leftPartialTrace_whiskerRight p (tensorPower X n) (End.of (β_ X X).hom)
  change leftPartialTrace p (End.of
      ((α_ X X (tensorPower X n)).inv ≫ (β_ X X).hom ▷ tensorPower X n ≫
        (α_ X X (tensorPower X n)).hom)) = _ at hw
  rw [hw, leftPartialTrace_braiding_of_trace_compatibility (C := C) ht]
  apply End.ext
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Left trace compatibility implies the local deletion law, with the actual
pivotal twist scalar as its factor. -/
theorem tensorPermutationTrace_adjacent_of_leftTrace
    (hX : SelfTransparent X)
    (htotal : IsLeftTraceCompatible p X)
    {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) :
    unitScalar C (p.rightTrace ((tensorPermutationAction X hX (n + 2))
      (Equiv.Perm.decomposeFin.symm (1, σ))).asHom) =
    Dimensions.pivotalBraidedTwistScalar C p X *
      unitScalar C (p.rightTrace ((tensorPermutationAction X hX (n + 1)) σ).asHom) := by
  let f := (tensorPermutationAction X hX (n + 1)) σ
  have hswap : tensorPermutationAction X hX (n + 2) (Equiv.swap 0 1) =
      Aut.toEnd (braidGenerator X n 0) := by
    convert tensorPermutationAction_swap (n := n) hX 0 using 1; congr 2
  let b : End (X ⊗ tensorPower X (n + 1)) := Aut.toEnd (braidGenerator X n 0)
  have hact : tensorPermutationAction X hX (n + 2)
      (Equiv.Perm.decomposeFin.symm (1, σ)) =
      b * insertLeftIdentity X f := by
    rw [decomposeFin_eq_swap_fixHead, map_mul, hswap, tensorPermutationAction_fixHead]
    change b * _ = b * _
    congr 1
  rw [hact, ← htotal _ _, leftPartialTrace_right]
  change unitScalar C (p.rightTrace ((leftPartialTrace p b * f).asHom)) = _
  dsimp only [b]
  rw [
    leftPartialTrace_firstGenerator_of_trace_compatibility (C := C) n (htotal X (End.of (β_ X X).hom))]
  simp only [smul_mul_assoc, one_mul, End.smul_asHom, p.rightTrace_smul,
    unitScalar_eq_equiv, map_smul, smul_eq_mul, f]

include hdim in
/-- The symmetric integrality argument now needs only left iterated-trace
compatibility and the sign of the actual pivotal twist scalar. -/
theorem integral_of_leftTrace_and_twist_sign
    (hX : SelfTransparent X)
    (htotal : IsLeftTraceCompatible p X)
    (hsign : Dimensions.pivotalBraidedTwistScalar C p X = 1 ∨
      Dimensions.pivotalBraidedTwistScalar C p X = -1) :
    ∃ m : ℕ, fpDimension C X = m := by
  rcases hsign with h | h
  · apply integral_of_parity_adjacent_trace hdim hX false
    intro n σ
    simpa [permutationScalarTrace, parityPermutationAction, h] using
      tensorPermutationTrace_adjacent_of_leftTrace (C := C) hX htotal σ
  · apply integral_of_parity_adjacent_trace hdim hX true
    intro n σ
    have hsign' : (Centre.permutationSign ℂ (n + 2)
        (Equiv.Perm.decomposeFin.symm (1, σ)) : ℂ) =
        -(Centre.permutationSign ℂ (n + 1) σ : ℂ) := by
      simpa using sign_decomposeFin 1 σ
    simp only [permutationScalarTrace, parityPermutationAction, ↓reduceIte, Centre.twistAction,
      MonoidHom.coe_mk, OneHom.coe_mk, End.smul_asHom, p.rightTrace_smul,
      unitScalar_eq_equiv, map_smul, smul_eq_mul, hsign']
    rw [← unitScalar_eq_equiv, ← unitScalar_eq_equiv,
      tensorPermutationTrace_adjacent_of_leftTrace (C := C) hX htotal σ, h]
    ring

end PropertyF.Ground.CentreCalculus

open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Coevaluation of the chosen dual of a tensor product, expressed in the
canonical tensor-dual pairing. -/
theorem tensorDual_coevaluation (X Y : C) :
    η_ ((X ⊗ Y)ᘁ) (((X ⊗ Y)ᘁ)ᘁ) =
      η_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) ≫
        ((rightDualTensorIso X Y).inv ⊗ₘ (Dimensions.doubleDualTensorIso X Y).hom) := by
  let A := (X ⊗ Y)ᘁ
  let B := (Yᘁ) ⊗ (Xᘁ)
  let E := ((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)
  let r : A ≅ B := rightDualTensorIso X Y
  let t : Bᘁ ≅ E := rightDualTensorIso (Yᘁ) (Xᘁ)
  have hn : η_ A (Aᘁ) = η_ B (Bᘁ) ≫ r.inv ▷ (Bᘁ) ≫ A ◁ (r.homᘁ) := by
    have h := Dimensions.coevaluation_iso_map r.symm
    simpa only [Iso.symm_hom, Iso.symm_inv, tensorHom_def, Category.assoc] using h.symm
  rw [hn]
  have he : η_ B E ≫ B ◁ t.inv = η_ B (Bᘁ) :=
    Dimensions.coevaluation_rightDualIso_inv HasRightDual.exact ExactPairing.tensor
  rw [← he]
  dsimp only [Dimensions.doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap]
  simp only [tensorHom_def, whiskerLeft_comp, Category.assoc]
  rw [whisker_exchange_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Left pivotal trace evaluated with the tensor dual pairing. -/
theorem leftTrace_tensor_pairing (p : Dimensions.PivotalStructure (C := C))
    (X Y : C) (f : X ⊗ Y ⟶ X ⊗ Y) :
    (p.leftTrace f).asHom =
      η_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) ≫
        ((Yᘁ) ⊗ (Xᘁ)) ◁ (((p.iso X).inv ⊗ₘ (p.iso Y).inv) ≫ f) ≫
        ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := by
  let A := X ⊗ Y
  let D := Aᘁ
  let E := (Yᘁ) ⊗ (Xᘁ)
  let r : D ≅ E := rightDualTensorIso X Y
  let q : ExactPairing A E := ExactPairing.tensor
  have hev := Dimensions.rightDualIso_inv_evaluation
    (@HasRightDual.exact C _ _ A (RightRigidCategory.rightDual A)) q
  change r.inv ▷ A ≫ ε_ A D = @ExactPairing.evaluation C _ _ A E q at hev
  change η_ D (Dᘁ) ≫ (𝟙 D ⊗ₘ ((p.iso A).inv ≫ f)) ≫ ε_ A D = _
  have hp : p.iso (X ⊗ Y) = (p.iso X ⊗ᵢ p.iso Y) ≪≫ Dimensions.doubleDualTensorIso X Y :=
    Iso.ext (p.tensor X Y)
  rw [tensorDual_coevaluation, hp]
  simp only [Iso.trans_inv, tensorIso_inv, tensorHom_def, id_whiskerRight,
    whiskerLeft_comp, Category.assoc]
  dsimp only [A, D, E, r] at *
  simp only [Category.id_comp, ← whiskerLeft_comp_assoc, Iso.hom_inv_id_assoc,
    Category.id_comp]
  rw [← whisker_exchange_assoc, ← hev]

set_option backward.isDefEq.respectTransparency false in
/-- Closing the first tensor factor and then the remainder computes the
left pivotal trace. -/
theorem leftTrace_partialTrace [Preadditive C] [Linear ℂ C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    (p : Dimensions.PivotalStructure (C := C)) {X Y : C} (f : End (X ⊗ Y)) :
    p.leftTrace (leftPartialTrace p f).asHom = p.leftTrace f.asHom := by
  apply End.homEquiv.injective
  change (p.leftTrace (leftPartialTrace p f).asHom).asHom = (p.leftTrace f.asHom).asHom
  rw [leftTrace_tensor_pairing]
  simp only [Dimensions.PivotalStructure.leftTrace, leftPartialTrace,
    LinearMap.coe_mk, AddHom.coe_mk]
  have hc : η_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) =
      η_ (Yᘁ) ((Yᘁ)ᘁ) ⊗≫ ((Yᘁ) ◁ η_ (Xᘁ) ((Xᘁ)ᘁ)) ▷ ((Yᘁ)ᘁ) ⊗≫ 𝟙 _ := rfl
  have he : ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) =
      𝟙 (((Yᘁ) ⊗ (Xᘁ)) ⊗ (X ⊗ Y)) ⊗≫ ((Yᘁ) : C) ◁ (ε_ X (Xᘁ) ▷ Y) ⊗≫ ε_ Y (Yᘁ) := rfl
  rw [hc, he]
  simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
  monoidal
  simp
  simp only [← whiskerLeft_comp_assoc]
  rw [leftUnitor_inv_naturality_assoc]
  rw [whisker_exchange_assoc (η_ (Xᘁ) ((Xᘁ)ᘁ)) (p.iso Y).inv]
  rw [associator_naturality_right_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [← whiskerLeft_comp_assoc]
  rw [whisker_exchange_assoc (p.iso X).inv (p.iso Y).inv]

/-- In a spherical category, left partial trace computes the ordinary
pivotal trace after the remaining strand is closed. -/
theorem spherical_rightTrace_leftPartialTrace [Preadditive C] [Linear ℂ C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C]
    (p : Dimensions.PivotalStructure (C := C)) (hp : p.IsSpherical)
    {X Y : C} (f : End (X ⊗ Y)) :
    p.rightTrace (leftPartialTrace p f).asHom = p.rightTrace f.asHom :=
  (hp Y _).symm.trans <| (leftTrace_partialTrace p f).trans (hp _ _)

/-- A self-transparent simple with sign-valued twist has integral FP
dimension in any FP-valued spherical fusion category. -/
theorem integral_of_spherical_and_twist_sign
    {C : BraidedFusionCategory.{v,u}} {p : Dimensions.PivotalStructure (C := C.Obj)}
    (hp : p.IsSpherical)
    (hdim : Modular.HasFPSimpleDimensions C p)
    {X : C.Obj} [Simple X] (hX : SelfTransparent X)
    (hsign : Dimensions.pivotalBraidedTwistScalar C p X = 1 ∨
      Dimensions.pivotalBraidedTwistScalar C p X = -1) :
    ∃ m : ℕ, fpDimension C X = m :=
  integral_of_leftTrace_and_twist_sign hdim hX
    (fun _ f ↦ spherical_rightTrace_leftPartialTrace p hp f) hsign

end PropertyF.Ground.CentreCalculus
