module
public import MTC.CategoryTheory.Dimensions.DualCoherence
public import MTC.Braided.Trace.PartialTrace

/-! # Tensor products of pivotal traces

Partial traces establish multiplicativity of the pivotal trace on tensor products.

## Main results

* `rightTraceWith_partialTraceWith`: computes the total trace using an arbitrary double-dual partial trace.
* `pivotalTrace_tensor`: proves multiplicativity of pivotal traces on tensor products.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace MTC.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

set_option backward.isDefEq.respectTransparency false in
/-- Tensor comparison of two arbitrary double-dual components. -/
theorem rightTraceWith_tensor_pairing {X Y : C} (j : X ≅ (Xᘁ)ᘁ) (k : Y ≅ (Yᘁ)ᘁ)
    (f : X ⊗ Y ⟶ X ⊗ Y) :
  (rightTraceWith ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y) f).asHom =
    η_ (X ⊗ Y) ((Yᘁ) ⊗ (Xᘁ)) ≫
      ((f ≫ (j.hom ⊗ₘ k.hom)) ⊗ₘ 𝟙 ((Yᘁ) ⊗ (Xᘁ))) ≫
      ε_ ((Yᘁ) ⊗ (Xᘁ)) (((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)) := by
  let V := (Yᘁ) ⊗ (Xᘁ)
  let U := ((Xᘁ)ᘁ) ⊗ ((Yᘁ)ᘁ)
  let p1 : ExactPairing (X ⊗ Y) ((X ⊗ Y)ᘁ) := HasRightDual.exact
  let p2 : ExactPairing (X ⊗ Y) V := ExactPairing.tensor
  let s : Vᘁ ≅ U := rightDualTensorIso (Yᘁ) (Xᘁ)
  let u := f ≫ (j.hom ⊗ₘ k.hom)
  have hr : η_ (X ⊗ Y) V ≫ ((u ≫ s.inv) ⊗ₘ 𝟙 V) ≫ ε_ V (Vᘁ) =
      η_ (X ⊗ Y) V ≫ (u ⊗ₘ 𝟙 V) ≫ ε_ V U := by
    simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, comp_whiskerRight, Category.assoc,
      show s.inv ▷ V ≫ ε_ V (Vᘁ) = ε_ V U from
        rightDualIso_inv_evaluation HasRightDual.exact ExactPairing.tensor]
  simpa only [rightTraceWith, End.homEquiv_apply, doubleDualTensorIso, Iso.trans_hom,
    Iso.symm_hom, tensorIso_hom, rightDualIsoMap, Category.assoc, rightDualTensorIso,
    s, u, p1, p2, U, V] using (trace_change_rightDual p1 p2 (u ≫ s.inv)).trans hr


omit [RightRigidCategory C] in
/-- Close the right tensor factor using an arbitrary double-dual isomorphism. -/
def partialTraceWith {Y : C} [HasRightDual Y] [HasRightDual (Yᘁ)]
    (k : Y ≅ (Yᘁ)ᘁ) (X : C) (f : End (X ⊗ Y)) : End X :=
  End.of ((ρ_ X).inv ≫ (X ◁ η_ Y (Yᘁ)) ≫ (α_ X Y (Yᘁ)).inv ≫
    (f.asHom ▷ (Yᘁ)) ≫ (α_ X Y (Yᘁ)).hom ≫
    (X ◁ (k.hom ▷ (Yᘁ))) ≫ (X ◁ ε_ (Yᘁ) ((Yᘁ)ᘁ)) ≫ (ρ_ X).hom)

set_option backward.isDefEq.respectTransparency false in
/-- Closing the right factor first works without a pivotal structure. -/
theorem rightTraceWith_partialTraceWith {X Y : C} (j : X ≅ (Xᘁ)ᘁ) (k : Y ≅ (Yᘁ)ᘁ)
    (f : End (X ⊗ Y)) :
    rightTraceWith j (partialTraceWith k X f).asHom =
      rightTraceWith ((j ⊗ᵢ k) ≪≫ doubleDualTensorIso X Y) f.asHom := End.homEquiv.injective <| by
  rw [End.homEquiv_apply, End.homEquiv_apply, rightTraceWith_tensor_pairing]
  simp only [rightTraceWith, partialTraceWith, ExactPairing.tensor_coevaluation,
    ExactPairing.tensor_evaluation, tensorHom_def, comp_whiskerRight]
  monoidal
  simp
  rw [whisker_exchange_assoc j.hom (λ_ (Xᘁ)).hom,
    whisker_exchange_assoc j.hom (ε_ (Yᘁ) ((Yᘁ)ᘁ) ▷ (Xᘁ)),
    whisker_exchange_assoc j.hom (k.hom ▷ (Yᘁ) ▷ (Xᘁ)),
    ← associator_naturality_left_assoc j.hom (Y ⊗ Yᘁ) (Xᘁ),
    ← comp_whiskerRight_assoc, ← associator_naturality_left, comp_whiskerRight, Category.assoc]


end MTC.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Calculus
namespace MTC.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- Closing the right tensor factor and then the left gives the total pivotal trace. -/
theorem rightTrace_partialTrace (p : PivotalStructure (C := C)) {X Y : C} (f : End (X ⊗ Y)) :
  p.rightTrace (rightPartialTrace p f).asHom = p.rightTrace f.asHom := by
  simpa [rightTraceWith, PivotalStructure.rightTrace, partialTraceWith, rightPartialTrace,
    ← p.tensor X Y, Category.assoc] using rightTraceWith_partialTraceWith (p.iso X) (p.iso Y) f

end MTC.Dimensions

namespace MTC.Calculus

variable {k : Type*} [Field k] [IsAlgClosed k]
  {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]

/-- The partial trace on a simple object is its normalized total trace. -/
theorem rightPartialTrace_simple [CategoryTheory.Limits.HasKernels C] {X Y : C}
    [Simple X] [FiniteDimensional k (X ⟶ X)] (p : Dimensions.PivotalStructure (C := C))
    (scalar : End (𝟙_ C) ≃ₐ[k] k) (f : End (X ⊗ Y))
    (hd : scalar (p.rightTrace (𝟙 X)) ≠ 0) :
    rightPartialTrace p f =
      (scalarTrace p scalar f / scalar (p.rightTrace (𝟙 X))) • (1 : End X) := by
  simpa only [scalarTrace, Dimensions.rightTrace_partialTrace p f] using
    simple_end_eq_trace_smul p scalar (rightPartialTrace p f) hd

end MTC.Calculus

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
open MTC.Calculus
namespace MTC.Dimensions
universe v u
variable {k : Type*} [CommSemiring k]
  {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]

variable (p : PivotalStructure (C := C))

variable (scalar : End (𝟙_ C) ≃ₐ[k] k)

omit [RightRigidCategory C] in
set_option backward.isDefEq.respectTransparency false in
/-- Closing a right-factor endomorphism gives its scalar trace times the identity. -/
theorem partialTraceWith_tensor_right_scalar {Y : C} [HasRightDual Y] [HasRightDual (Yᘁ)]
    (j : Y ≅ (Yᘁ)ᘁ)
    (X : C) (b : Y ⟶ Y) :
    partialTraceWith j X (End.of (𝟙 X ⊗ₘ b)) = scalar (rightTraceWith j b) • 1 := by
  have h : partialTraceWith j X (End.of (𝟙 X ⊗ₘ b)) =
      End.of ((ρ_ X).inv ≫ X ◁ (rightTraceWith j b).asHom ≫ (ρ_ X).hom) := by
    apply End.ext
    simp only [partialTraceWith, rightTraceWith, tensorHom_def, id_whiskerRight,
      Category.id_comp, whiskerLeft_comp, comp_whiskerRight, Category.assoc]
    monoidal
  rw [h, eq_smul_one_of_algEquiv scalar (rightTraceWith j b)]
  apply End.ext
  simp

/-- The partial trace of a tensor product is the left factor times the trace of the right. -/
theorem rightPartialTrace_tensor {X Y : C} (a : X ⟶ X) (b : Y ⟶ Y) :
    rightPartialTrace p (End.of (a ⊗ₘ b)) = scalar (p.rightTrace b) • End.of a := by
  rw [show End.of (a ⊗ₘ b) = End.of (𝟙 X ⊗ₘ b) * insertRightIdentity Y (End.of a) from
      End.ext (by simp [insertRightIdentity, tensorHom_def]),
    rightPartialTrace_right,
    show rightPartialTrace p (End.of (𝟙 X ⊗ₘ b)) = scalar (p.rightTrace b) • 1 from
      partialTraceWith_tensor_right_scalar scalar (p.iso Y) X b,
    smul_mul_assoc, one_mul]

/-- Pivotal trace is multiplicative on tensor products of endomorphisms. -/
theorem pivotalTrace_tensor {X Y : C} (a : X ⟶ X) (b : Y ⟶ Y) :
    scalar (p.rightTrace (a ⊗ₘ b)) = scalar (p.rightTrace a) * scalar (p.rightTrace b) := by
  simpa [rightPartialTrace_tensor p scalar a b, PivotalStructure.rightTrace_smul, mul_comm] using
    congrArg scalar (rightTrace_partialTrace p (End.of (a ⊗ₘ b))).symm

end MTC.Dimensions

end
