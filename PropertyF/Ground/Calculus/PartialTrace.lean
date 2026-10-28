module
public import PropertyF.Ground.Dimensions.Trace
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Partial trace over the right tensor factor, constructed from duality. -/

open PropertyF.Ground.Dimensions

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Calculus
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The scalar-valued pivotal trace of an endomorphism. -/
def scalarTrace (p : PivotalStructure (C := C)) (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ)
    {X : C} (f : End X) : ℂ := scalar (p.rightTrace f.asHom)

/-- Close the right tensor factor using evaluation, coevaluation, and the
pivotal isomorphism. -/
def rightPartialTrace (p : PivotalStructure (C := C)) (X Y : C) :
    End (X ⊗ Y) →ₗ[ℂ] End X where
  toFun f := End.of ((ρ_ X).inv ≫ (X ◁ η_ Y (Yᘁ)) ≫ (α_ X Y (Yᘁ)).inv ≫
    (f.asHom ▷ (Yᘁ)) ≫ (α_ X Y (Yᘁ)).hom ≫
    (X ◁ ((p.iso Y).hom ▷ (Yᘁ))) ≫
    (X ◁ ε_ (Yᘁ) ((Yᘁ)ᘁ)) ≫ (ρ_ X).hom)
  map_add' f g := by
    apply End.ext
    simp
  map_smul' z f := by
    apply End.ext
    simp

/-- Insert an endomorphism on the untraced tensor factor. -/
def insertRightIdentity (X Y : C) (a : End X) : End (X ⊗ Y) :=
  End.of (a.asHom ▷ Y)

/-- Partial trace commutes with postcomposition on the untraced factor. -/
theorem rightPartialTrace_left (p : PivotalStructure (C := C))
    {X Y : C} (a : End X) (f : End (X ⊗ Y)) :
    rightPartialTrace p X Y (insertRightIdentity X Y a * f) =
      a * rightPartialTrace p X Y f :=
  End.ext (by simp only [rightPartialTrace, insertRightIdentity, LinearMap.coe_mk, AddHom.coe_mk,
    End.mul_asHom, comp_whiskerRight, Category.assoc, associator_naturality_left_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality])


/-- Partial trace commutes with precomposition on the untraced factor. -/
theorem rightPartialTrace_right (p : PivotalStructure (C := C))
    {X Y : C} (a : End X) (f : End (X ⊗ Y)) :
    rightPartialTrace p X Y (f * insertRightIdentity X Y a) =
      rightPartialTrace p X Y f * a :=
  End.ext (by simp only [rightPartialTrace, insertRightIdentity, LinearMap.coe_mk, AddHom.coe_mk,
    End.mul_asHom, comp_whiskerRight, Category.assoc, ← associator_inv_naturality_left_assoc,
    whisker_exchange_assoc, ← rightUnitor_inv_naturality_assoc])

/-- Tracing an identity strand gives the categorical dimension of the closed
factor, acting on the untraced object. -/
theorem rightPartialTrace_one (p : PivotalStructure (C := C))
    (X Y : C) : rightPartialTrace p X Y 1 =
      End.of ((ρ_ X).inv ≫ (X ◁ (p.rightTrace (𝟙 Y)).asHom) ≫ (ρ_ X).hom) :=
  End.ext (by simp only [rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk,
    End.one_asHom, id_whiskerRight, Category.comp_id, Iso.inv_hom_id_assoc,
    PivotalStructure.rightTrace, Category.id_comp, tensorHom_def, whiskerLeft_id,
    whiskerLeft_comp, Category.assoc])

variable (p : PivotalStructure (C := C)) (scalar : End (𝟙_ C) ≃ₐ[ℂ] ℂ)

/-- The partial trace of an inserted endomorphism is the dimension of the
closed factor times that endomorphism. -/
theorem rightPartialTrace_insert {X Y : C} (a : End X) :
    rightPartialTrace p X Y (insertRightIdentity X Y a) =
      (scalar (p.rightTrace (𝟙 Y))) • a := by
  have hscalar : p.rightTrace (𝟙 Y) = (scalar (p.rightTrace (𝟙 Y))) • (1 : End (𝟙_ C)) := by
    apply scalar.injective
    simp
  rw [← mul_one (insertRightIdentity X Y a), rightPartialTrace_left, rightPartialTrace_one, hscalar]
  exact End.ext (by simp)

/-- A simple endomorphism is determined by its pivotal trace. -/
theorem simple_end_eq_trace_smul [CategoryTheory.Limits.HasKernels C]
    {Y : C} [Simple Y] [FiniteDimensional ℂ (Y ⟶ Y)]
    (a : End Y) (hd : scalar (p.rightTrace (𝟙 Y)) ≠ 0) :
    a = (scalarTrace p scalar a / scalar (p.rightTrace (𝟙 Y))) • (1 : End Y) := by
  simp only [scalarTrace]
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ a.asHom
  have hcval : c = scalar (p.rightTrace a.asHom) / scalar (p.rightTrace (𝟙 Y)) := by
    apply (eq_div_iff hd).2
    rw [← hc, p.rightTrace_smul]
    simp
  exact End.ext (by simpa [← hcval] using hc.symm)


/-- Schur's lemma reduces the simple-survivor partial-trace formula to the
single, explicitly stated compatibility of iterated and total pivotal traces. -/
theorem rightPartialTrace_simple_of_trace_compatibility [CategoryTheory.Limits.HasKernels C] {X Y : C}
    [Simple X] [FiniteDimensional ℂ (X ⟶ X)]
    (f : End (X ⊗ Y)) (hd : scalar (p.rightTrace (𝟙 X)) ≠ 0)
    (htrace : p.rightTrace (rightPartialTrace p X Y f).asHom = p.rightTrace f.asHom) :
    rightPartialTrace p X Y f =
      (scalarTrace p scalar f / scalar (p.rightTrace (𝟙 X))) • (1 : End X) := by
  simpa only [scalarTrace, htrace] using simple_end_eq_trace_smul p scalar (rightPartialTrace p X Y f) hd

/-- Closing a right tensor factor commutes with adding an identity factor on
the left, with the associator made explicit. -/
theorem rightPartialTrace_whiskerLeft {A X Y : C} (f : End (X ⊗ Y)) :
    rightPartialTrace p (A ⊗ X) Y (End.of
      ((α_ A X Y).hom ≫ (A ◁ f.asHom) ≫ (α_ A X Y).inv)) =
      End.of (A ◁ (rightPartialTrace p X Y f).asHom) :=
  End.ext (by
    simp only [rightPartialTrace, LinearMap.coe_mk, AddHom.coe_mk,
      comp_whiskerRight, whiskerLeft_comp, Category.assoc]
    monoidal)

end PropertyF.Ground.Calculus
