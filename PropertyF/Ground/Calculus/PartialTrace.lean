module
public import PropertyF.Ground.Dimensions.Trace
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Partial pivotal trace

The right partial trace closes a tensor factor using duality. Its compatibility with
endomorphisms of the other factor yields formulas for simple objects.
-/

open PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- Close the right tensor factor using evaluation, coevaluation, and the
pivotal isomorphism. -/
def rightPartialTrace (p : PivotalStructure (C := C)) {X Y : C} (f : End (X ⊗ Y)) : End X :=
  End.of ((ρ_ X).inv ≫ (X ◁ η_ Y (Yᘁ)) ≫ (α_ X Y (Yᘁ)).inv ≫
    (f.asHom ▷ (Yᘁ)) ≫ (α_ X Y (Yᘁ)).hom ≫
    (X ◁ ((p.iso Y).hom ▷ (Yᘁ))) ≫
    (X ◁ ε_ (Yᘁ) ((Yᘁ)ᘁ)) ≫ (ρ_ X).hom)
/-- Insert an endomorphism on the untraced tensor factor. -/
def insertRightIdentity {X : C} (Y : C) (a : End X) : End (X ⊗ Y) :=
  End.of (a.asHom ▷ Y)

section PartialTraceActions

variable (p : PivotalStructure (C := C)) {X Y : C} (a : End X) (f : End (X ⊗ Y))

/-- Partial trace commutes with postcomposition on the untraced factor. -/
theorem rightPartialTrace_left :
    rightPartialTrace p (insertRightIdentity Y a * f) =
      a * rightPartialTrace p f :=
  End.ext (by simp only [rightPartialTrace, insertRightIdentity,
    End.mul_asHom, comp_whiskerRight, Category.assoc, associator_naturality_left_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality])


/-- Partial trace commutes with precomposition on the untraced factor. -/
theorem rightPartialTrace_right :
    rightPartialTrace p (f * insertRightIdentity Y a) =
      rightPartialTrace p f * a :=
  End.ext (by simp only [rightPartialTrace, insertRightIdentity,
    End.mul_asHom, comp_whiskerRight, Category.assoc, ← associator_inv_naturality_left_assoc,
    whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc])

end PartialTraceActions

/-- Tracing an identity strand gives the categorical dimension of the closed
factor, acting on the untraced object. -/
theorem rightPartialTrace_one (p : PivotalStructure (C := C))
    (X Y : C) : rightPartialTrace p (X := X) (Y := Y) 1 =
      End.of ((ρ_ X).inv ≫ (X ◁ (p.rightTrace (𝟙 Y)).asHom) ≫ (ρ_ X).hom) :=
  End.ext (by simp [rightPartialTrace, PivotalStructure.rightTrace, tensorHom_def])

variable (p : PivotalStructure (C := C))

/-- Closing a right tensor factor commutes with adding an identity factor on
the left, with the associator made explicit. -/
theorem rightPartialTrace_whiskerLeft {A X Y : C} (f : End (X ⊗ Y)) :
    rightPartialTrace p (End.of
      ((α_ A X Y).hom ≫ (A ◁ f.asHom) ≫ (α_ A X Y).inv)) =
      End.of (A ◁ (rightPartialTrace p f).asHom) :=
  End.ext (by simp [rightPartialTrace])

section ScalarTrace

variable {k : Type*} [CommSemiring k] [Preadditive C] [Linear k C]
  [MonoidalPreadditive C] [MonoidalLinear k C]

/-- The partial trace commutes with scalar multiplication. -/
@[simp] theorem rightPartialTrace_smul {X Y : C} (z : k) (f : End (X ⊗ Y)) :
    rightPartialTrace p (z • f) = z • rightPartialTrace p f :=
  End.ext (by simp [rightPartialTrace])

/-- The scalar-valued pivotal trace of an endomorphism. -/
def scalarTrace (scalar : End (𝟙_ C) ≃ₐ[k] k) {X : C} (f : End X) : k :=
  scalar (p.rightTrace f.asHom)

variable (scalar : End (𝟙_ C) ≃ₐ[k] k)

/-- The partial trace of an inserted endomorphism is the dimension of the
closed factor times that endomorphism. -/
theorem rightPartialTrace_insert {X Y : C} (a : End X) :
    rightPartialTrace p (insertRightIdentity Y a) =
      (scalar (p.rightTrace (𝟙 Y))) • a := by
  rw [← mul_one (insertRightIdentity Y a), rightPartialTrace_left, rightPartialTrace_one]
  exact End.ext (by rw [eq_smul_one_of_algEquiv scalar (p.rightTrace (𝟙 Y))]; simp)

end ScalarTrace

section SimpleTrace

variable {k : Type*} [Field k] [IsAlgClosed k] [Preadditive C] [Linear k C]
  [MonoidalPreadditive C] [MonoidalLinear k C] (scalar : End (𝟙_ C) ≃ₐ[k] k)

/-- A simple endomorphism is determined by its pivotal trace. -/
theorem simple_end_eq_trace_smul [CategoryTheory.Limits.HasKernels C]
    {Y : C} [Simple Y] [FiniteDimensional k (Y ⟶ Y)]
    (a : End Y) (hd : scalar (p.rightTrace (𝟙 Y)) ≠ 0) :
    a = (scalarTrace p scalar a / scalar (p.rightTrace (𝟙 Y))) • (1 : End Y) :=
  let ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id k a.asHom
  let hcval : c = scalar (p.rightTrace a.asHom) / scalar (p.rightTrace (𝟙 Y)) := by
    apply (eq_div_iff hd).2
    rw [← hc, p.rightTrace_smul]
    simp
  End.ext (by simpa [scalarTrace, ← hcval] using hc.symm)

end SimpleTrace

end PropertyF.Ground.Calculus
