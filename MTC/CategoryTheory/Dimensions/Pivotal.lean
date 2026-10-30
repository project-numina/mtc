module
public import MTC.Braided.Definitions

/-! # Pivotal structures

`rightDualIsoMap` and `doubleDualTensorIso` provide the duality comparisons
needed to state a `PivotalStructure`. Its left and right traces specialize to
the quantum traces on identity morphisms; `IsSpherical` requires them to agree.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions

universe v u

section RightRigid
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

omit [RightRigidCategory C] in
/-- Contravariant action of the chosen right dual on an isomorphism. -/
def rightDualIsoMap {X Y : C} [HasRightDual X] [HasRightDual Y] (e : X ≅ Y) : Yᘁ ≅ Xᘁ where
  hom := e.homᘁ
  inv := e.invᘁ
  hom_inv_id := by rw [← comp_rightAdjointMate]; simp
  inv_hom_id := by rw [← comp_rightAdjointMate]; simp

/-- Tensorator for the double-right-dual object assignment, built from the
uniqueness of right duals and the tensor product duality. -/
def doubleDualTensorIso (X Y : C) : (Xᘁ)ᘁ ⊗ (Yᘁ)ᘁ ≅ ((X ⊗ Y)ᘁ)ᘁ :=
  (rightDualTensorIso (Yᘁ) (Xᘁ)).symm ≪≫ rightDualIsoMap (rightDualTensorIso X Y)

/-- The chosen right dual, with the rigid-category choice used uniformly. -/
def rightDualObject (X : C) : C := Xᘁ

/-- The rigid-category choice of the unit dual is canonically isomorphic to the unit. -/
def rightDualUnitIso : rightDualObject (𝟙_ C) ≅ 𝟙_ C :=
  rightDualIso (X := 𝟙_ C)
    (@HasRightDual.exact C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C)))
    (inferInstance : ExactPairing (𝟙_ C) (𝟙_ C))

/-- Unit comparison for the double-right-dual object assignment. -/
def doubleDualUnitIso : 𝟙_ C ≅ rightDualObject (rightDualObject (𝟙_ C)) :=
  letI : HasRightDual (𝟙_ C) := RightRigidCategory.rightDual _
  rightDualUnitIso.symm ≪≫ rightDualIsoMap rightDualUnitIso

omit [RightRigidCategory C] in
/-- Trace using a single chosen double-dual isomorphism; no pivotal structure
is needed. -/
def rightTraceWith {X : C} [HasRightDual X] [HasRightDual (Xᘁ)]
    (j : X ≅ (Xᘁ)ᘁ) (f : X ⟶ X) : End (𝟙_ C) :=
  End.of (η_ X (Xᘁ) ≫ ((f ≫ j.hom) ⊗ₘ 𝟙 (Xᘁ)) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ))

/-- A pivotal structure is a monoidal natural isomorphism from the identity
to the double-right-dual, expressed using the canonical duality comparisons. -/
structure PivotalStructure where
  /-- The natural isomorphism from each object to its double dual. -/
  iso : ∀ X : C, X ≅ (Xᘁ)ᘁ
  naturality : ∀ {X Y : C} (f : X ⟶ Y), f ≫ (iso Y).hom =
    (iso X).hom ≫ (fᘁ)ᘁ
  tensor : ∀ X Y, (iso (X ⊗ Y)).hom =
    ((iso X).hom ⊗ₘ (iso Y).hom) ≫ (doubleDualTensorIso X Y).hom
  unit : (iso (𝟙_ C)).hom = (doubleDualUnitIso (C := C)).hom

namespace PivotalStructure

/-- Right pivotal trace, an endomorphism of the tensor unit. -/
def rightTrace (p : PivotalStructure (C := C)) {X : C} (f : X ⟶ X) : End (𝟙_ C) :=
  rightTraceWith (p.iso X) f

/-- Left pivotal trace, using the inverse pivotal isomorphism. -/
def leftTrace (p : PivotalStructure (C := C)) {X : C} (f : X ⟶ X) : End (𝟙_ C) :=
  End.of (ExactPairing.coevaluation (Xᘁ) ((Xᘁ)ᘁ) ≫
    (𝟙 (Xᘁ) ⊗ₘ ((p.iso X).inv ≫ f)) ≫ ExactPairing.evaluation X (Xᘁ))

/-- A spherical pivotal structure has equal left and right traces on every
endomorphism, without any semisimplicity assumption. -/
def IsSpherical (p : PivotalStructure (C := C)) : Prop :=
  ∀ (X : C) (f : X ⟶ X), p.leftTrace f = p.rightTrace f

end PivotalStructure

end RightRigid

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The trace of the identity is the quantum trace of its double-dual component. -/
theorem rightTraceWith_id {X : C} (j : X ≅ (Xᘁ)ᘁ) :
    rightTraceWith j (𝟙 X) = rightQuantumTrace j := by
  simp [rightTraceWith, rightQuantumTrace]

/-- For a rigid category these traces of the identity recover the traces used
in the existing intrinsic squared norm. -/
theorem rightTrace_id (p : PivotalStructure (C := C)) (X : C) :
    p.rightTrace (𝟙 X) = rightQuantumTrace (p.iso X) :=
  rightTraceWith_id (p.iso X)

theorem leftTrace_id (p : PivotalStructure (C := C)) (X : C) :
    p.leftTrace (𝟙 X) = leftQuantumTrace (p.iso X) :=
  by simp [PivotalStructure.leftTrace, leftQuantumTrace]

/-- In a spherical category the two quantum dimensions agree. -/
theorem spherical_quantumTraces_eq {p : PivotalStructure (C := C)}
    (hp : p.IsSpherical) (X : C) :
    rightQuantumTrace (p.iso X) = leftQuantumTrace (p.iso X) := by
  simpa only [← rightTrace_id, ← leftTrace_id] using (hp X (𝟙 X)).symm

end PropertyF.Ground.Dimensions
