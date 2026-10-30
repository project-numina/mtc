module
public import MTC.Center.Trace.ParityDeletion
public import MTC.Center.Dimensions.PivotalTwist
public import MTC.Braided.Trace.ThreeTrace
public import MTC.CategoryTheory.Dimensions.TensorMultiplicativity
public import MTC.CategoryTheory.Dimensions.DoubleDualPairing
public import MTC.Modular.BraidIso
public import MTC.CategoryTheory.Dimensions.DualCoherence

/-!
# Left traces of braid crossings

Two-strand and adjacent-crossing traces reduce to pivotal twists and left
partial-trace compatibility. Tensor-duality identities establish that
compatibility in spherical categories. We write `θ C p X` for the pivotal
twist scalar and `tr C p ρ n σ` for a scalar permutation trace.
-/
@[expose] public noncomputable section
local notation "θ" => PropertyF.Ground.Dimensions.pivotalBraidedTwistScalar
local notation "tr" => PropertyF.Ground.CentreCalculus.permScalarTrace
open PropertyF.Ground.Modular (HasFPSimpleDimensions IsFPSpherical)
open Equiv.Perm (decomposeFin)
open PropertyF.Ground.Dimensions
open Equiv (Perm)
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
variable (p : PivotalStructure (C := C))

/-- Close the first factor using the pivotal left dual. -/
def leftPartialTrace {X Y : C} (f : End (X ⊗ Y)) : End Y :=
  End.of ((λ_ Y).inv ≫
    ((η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ ((Xᘁ) ◁ (p.iso X).inv)) ▷ Y) ≫
    (α_ (Xᘁ) X Y).hom ≫ ((Xᘁ) ◁ f.asHom) ≫
    (α_ (Xᘁ) X Y).inv ≫ (ε_ X (Xᘁ) ▷ Y) ≫ (λ_ Y).hom)

/-- Closing the left factor and then tracing agrees with the total trace at an endomorphism. -/
abbrev IsLeftTraceCompatibleAt
    {X Y : C} (f : End (X ⊗ Y)) : Prop :=
  p.rightTrace (leftPartialTrace p f).asHom = p.rightTrace f.asHom

/-- Closing the left factor and then tracing agrees with the total trace. -/
abbrev IsLeftTraceCompatible (X : C) : Prop :=
  ∀ Y (f : End (X ⊗ Y)), IsLeftTraceCompatibleAt p f

/-- Inserting a map on the untraced right factor. -/
def insertLeftIdentity (X : C) {Y : C} (a : End Y) : End (X ⊗ Y) :=
  End.of (X ◁ a.asHom)

variable {X Y : C}

/-- A map on the untraced factor passes through the left partial trace. -/
theorem leftPartialTrace_right (a : End Y) (f : End (X ⊗ Y)) :
    leftPartialTrace p (f * insertLeftIdentity X a) =
      leftPartialTrace p f * a :=
  End.ext <| by
    simp only [leftPartialTrace, insertLeftIdentity, End.mul_asHom, whiskerLeft_comp, Category.assoc]
    rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc,
      ← leftUnitor_inv_naturality_assoc]

/-- Closing the first factor commutes with a spectator factor on the right. -/
theorem leftPartialTrace_whiskerRight (Z : C) (f : End (X ⊗ Y)) :
    leftPartialTrace p (End.of
      ((α_ X Y Z).inv ≫ (f.asHom ▷ Z) ≫ (α_ X Y Z).hom)) =
      End.of ((leftPartialTrace p f).asHom ▷ Z) :=
  End.ext <| by
    dsimp [leftPartialTrace]
    monoidal

variable {k : Type*} [Field k] [IsAlgClosed k]
    [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [CategoryTheory.Limits.HasKernels C] [Simple Y] [FiniteDimensional k (Y ⟶ Y)]

/-- Schur's lemma identifies the partial trace on a simple surviving strand
once compatibility with total trace is known. -/
theorem leftPartialTrace_simple_of_trace_compatibility (scalar : End (𝟙_ C) ≃ₐ[k] k)
    (f : End (X ⊗ Y))
    (hd : scalar (p.rightTrace (𝟙 Y)) ≠ 0) (htrace : IsLeftTraceCompatibleAt p f) :
    leftPartialTrace p f =
      (scalar (p.rightTrace f.asHom) / scalar (p.rightTrace (𝟙 Y))) • (1 : End Y) :=
  (Calculus.simple_end_eq_trace_smul p scalar (leftPartialTrace p f) hd).trans <|
    congrArg (fun t ↦ (scalar t / scalar (p.rightTrace (𝟙 Y))) • (1 : End Y)) htrace

end PropertyF.Ground.CentreCalculus

open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := C.Obj)}
  (hdim : HasFPSimpleDimensions C p) {X : C.Obj} [Simple X]

/-- Once left partial trace composes with total trace, Schur's lemma computes
the closed crossing as the pivotal twist scalar. -/
theorem leftPartialTrace_braiding_of_trace_compatibility
    (ht : IsLeftTraceCompatibleAt p (End.of (β_ X X).hom)) :
    leftPartialTrace p (End.of (β_ X X).hom) =
      θ C p X • (1 : End X) := by
  let : FiniteDimensional ℂ (X ⟶ X) := IsFusionCategory.hom_finite _ _
  simpa only [← unitScalar_eq_equiv, Dimensions.pivotalTrace_selfBraiding,
    pivotalDimension, mul_div_cancel_right₀ _ (Modular.unitScalar_rightTrace_ne_zero C p X)] using
    leftPartialTrace_simple_of_trace_compatibility p (unitScalarEquiv C)
      (End.of (β_ X X).hom) (by simpa only [← unitScalar_eq_equiv] using
        Modular.unitScalar_rightTrace_ne_zero C p X) ht

set_option backward.isDefEq.respectTransparency false in
/-- The closed first crossing with any spectator tensor factor is the same
scalar on the entire untraced factor. -/
theorem leftPartialTrace_firstGenerator_of_trace_compatibility (n : ℕ)
    (ht : IsLeftTraceCompatibleAt p (End.of (β_ X X).hom)) :
    leftPartialTrace p (Aut.toEnd (braidGenerator X n 0)) = θ C p X • 1 := by
  have hg : (Aut.toEnd (braidGenerator X n 0)) = End.of
      ((α_ X X (tensorPower X n)).inv ≫ ((β_ X X).hom ▷ tensorPower X n) ≫
        (α_ X X (tensorPower X n)).hom) := End.ext <| by
    change (braidGenerator X n 0).asIso.hom = _
    simpa only [Modular.firstBraiding, Iso.trans_hom, Iso.symm_hom, tensorIso_hom,
      Iso.refl_hom, tensorHom_id] using Modular.braidGenerator_zero X n
  dsimp only [tensorPower] at hg ⊢
  rw [hg, leftPartialTrace_whiskerRight p (tensorPower X n) (End.of (β_ X X).hom),
    leftPartialTrace_braiding_of_trace_compatibility (C := C) ht]
  apply End.ext
  simp

section
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
variable (p : PivotalStructure (C := D)) (scalar : End (𝟙_ D) →ₗ[ℂ] ℂ)
  {X : D} (hX : SelfTransparent X) (htotal : IsLeftTraceCompatible p X) (t : ℂ)
  (hfirst : ∀ n, leftPartialTrace p (Aut.toEnd (braidGenerator X n 0)) = t • 1)

include htotal hfirst in
set_option backward.isDefEq.respectTransparency false in
/-- Closing the first crossing gives the adjacent-strand trace deletion law. -/
theorem tensorPermTrace_adjacent {n : ℕ} (σ : Perm (Fin (n + 1))) :
    scalarPermTrace p scalar (tensorPermAction X hX) (n + 2) (decomposeFin.symm (1, σ)) =
      t * scalarPermTrace p scalar (tensorPermAction X hX) (n + 1) σ := by
  dsimp only [scalarPermTrace]
  rw [tensorPermAction_adjacent hX σ, ← htotal _ _]
  change scalar (p.rightTrace (leftPartialTrace p
    ((Aut.toEnd (braidGenerator X n 0) : End (X ⊗ tensorPower X (n + 1))) *
      insertLeftIdentity X ((tensorPermAction X hX (n + 1)) σ))).asHom) = _
  rw [leftPartialTrace_right, hfirst n]
  simp only [smul_mul_assoc, one_mul, End.smul_asHom, p.rightTrace_smul, map_smul, smul_eq_mul]

include htotal hfirst in
/-- A negative crossing scalar is corrected by the sign-twisted action. -/
theorem negativeParity_adjacentTrace (hneg : t = -1) :
    HasAdjacentTrace (scalarPermTrace p scalar (parityPermAction D hX true)) := fun n σ ↦ by
  simp only [scalarPermTrace_parity, sign_decomposeFin,
    show (1 : Fin (n + 2)) ≠ 0 from one_ne_zero, ite_false,
    tensorPermTrace_adjacent p scalar hX htotal t hfirst σ, hneg,
    neg_mul, mul_neg, one_mul, neg_neg]
end

variable (hX : SelfTransparent X) (htotal : IsLeftTraceCompatible p X)

include hdim hX htotal in
/-- The symmetric integrality argument now needs only left iterated-trace
compatibility and the sign of the actual pivotal twist scalar. -/
theorem integral_of_leftTrace_and_twist_sign (hsign : θ C p X = 1 ∨ θ C p X = -1) :
    IsFPIntegral C X :=
  let hfirst (n : ℕ) : leftPartialTrace p (Aut.toEnd (braidGenerator X n 0)) = θ C p X • 1 :=
    leftPartialTrace_firstGenerator_of_trace_compatibility (C := C) n
      (htotal X (End.of (β_ X X).hom))
  hsign.elim
    (fun h ↦ integral_of_parity_adjacent_trace hdim hX false fun n σ ↦ by
      simpa [permScalarTrace, scalarPermTrace, parityPermAction, h] using
        tensorPermTrace_adjacent p (unitScalarEquiv C).toLinearMap hX htotal _ hfirst σ)
    (fun h ↦ integral_of_parity_adjacent_trace hdim hX true
      (negativeParity_adjacentTrace p (unitScalarEquiv C).toLinearMap hX htotal _ hfirst h))

end PropertyF.Ground.CentreCalculus

open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.CentreCalculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
variable (p : PivotalStructure (C := C))

section
variable (X Y : C)

set_option backward.isDefEq.respectTransparency false in
/-- Coevaluation of the chosen dual of a tensor product, expressed in the
canonical tensor-dual pairing. -/
theorem tensorDual_coevaluation :
    η_ ((X ⊗ Y)ᘁ) (((X ⊗ Y)ᘁ)ᘁ) =
      η_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) ≫
        ((rightDualTensorIso X Y).inv ⊗ₘ (Dimensions.doubleDualTensorIso X Y).hom) := by
  let A := (X ⊗ Y)ᘁ
  let B := (Yᘁ) ⊗ (Xᘁ)
  let E := ((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)
  let r : A ≅ B := rightDualTensorIso X Y
  let t : Bᘁ ≅ E := rightDualTensorIso (Yᘁ) (Xᘁ)
  rw [← Dimensions.coevaluation_iso_map r.symm, Iso.symm_hom, Iso.symm_inv, tensorHom_def]
  have he : η_ B E ≫ B ◁ t.inv = η_ B (Bᘁ) :=
    Dimensions.coevaluation_rightDualIso_inv HasRightDual.exact ExactPairing.tensor
  rw [← he]
  simp only [Dimensions.doubleDualTensorIso, Iso.trans_hom, Iso.symm_hom,
    Dimensions.rightDualIsoMap, tensorHom_def, whiskerLeft_comp, Category.assoc]
  rw [whisker_exchange_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Left pivotal trace evaluated with the tensor dual pairing. -/
theorem leftTrace_tensor_pairing (f : X ⊗ Y ⟶ X ⊗ Y) :
    (p.leftTrace f).asHom = η_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) ≫
      ((Yᘁ) ⊗ (Xᘁ)) ◁ (((p.iso X).inv ⊗ₘ (p.iso Y).inv) ≫ f) ≫
      ε_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) := by
  let A := X ⊗ Y
  let D := Aᘁ
  let E := (Yᘁ) ⊗ (Xᘁ)
  let r : D ≅ E := rightDualTensorIso X Y
  have hev : r.inv ▷ A ≫ ε_ A D = ε_ A E :=
    Dimensions.rightDualIso_inv_evaluation
      (@HasRightDual.exact C _ _ A (RightRigidCategory.rightDual A)) ExactPairing.tensor
  change η_ D (Dᘁ) ≫ (𝟙 D ⊗ₘ ((p.iso A).inv ≫ f)) ≫ ε_ A D = _
  rw [tensorDual_coevaluation,
    show p.iso (X ⊗ Y) = (p.iso X ⊗ᵢ p.iso Y) ≪≫ Dimensions.doubleDualTensorIso X Y from
      Iso.ext (p.tensor X Y)]
  simp only [Iso.trans_inv, tensorIso_inv, tensorHom_def, id_whiskerRight,
    whiskerLeft_comp, Category.assoc]
  dsimp only [A, D, E, r] at *
  simp only [Category.id_comp, ← whiskerLeft_comp_assoc, Iso.hom_inv_id_assoc,
    ← whisker_exchange_assoc, ← hev]

end

set_option backward.isDefEq.respectTransparency false in
/-- Closing the first tensor factor and then the remainder computes the
left pivotal trace. -/
theorem leftTrace_partialTrace {X Y : C} (f : End (X ⊗ Y)) :
    p.leftTrace (leftPartialTrace p f).asHom = p.leftTrace f.asHom := by
  apply End.homEquiv.injective
  change (p.leftTrace (leftPartialTrace p f).asHom).asHom = (p.leftTrace f.asHom).asHom
  rw [leftTrace_tensor_pairing]
  simp only [PivotalStructure.leftTrace, leftPartialTrace,
    ExactPairing.tensor_coevaluation, ExactPairing.tensor_evaluation, tensorHom_def,
    comp_whiskerRight, whiskerLeft_comp]
  monoidal
  simp
  simp only [← whiskerLeft_comp_assoc]
  rw [leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc (η_ (Xᘁ) ((Xᘁ)ᘁ)) (p.iso Y).inv,
    associator_naturality_right_assoc]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [← whiskerLeft_comp_assoc]
  rw [whisker_exchange_assoc (p.iso X).inv (p.iso Y).inv]

/-- In a spherical category, left partial trace computes the ordinary
pivotal trace after the remaining strand is closed. -/
theorem spherical_rightTrace_leftPartialTrace
    (hp : p.IsSpherical) {X Y : C} (f : End (X ⊗ Y)) :
    IsLeftTraceCompatibleAt p f :=
  (hp Y _).symm.trans <| (leftTrace_partialTrace p f).trans (hp _ _)

/-- A self-transparent simple with sign-valued twist has integral FP
dimension in any FP-valued spherical fusion category. -/
theorem integral_of_spherical_and_twist_sign
    {C : BraidedFusionCategory.{v,u}} {p : PivotalStructure (C := C.Obj)}
    (hfp : IsFPSpherical C p) {X : C.Obj} [Simple X] (hX : SelfTransparent X)
    (hsign : θ C p X = 1 ∨ θ C p X = -1) : IsFPIntegral C X :=
  integral_of_leftTrace_and_twist_sign hfp.2 hX
    (fun _ f ↦ spherical_rightTrace_leftPartialTrace p hfp.1 f) hsign

end PropertyF.Ground.CentreCalculus
