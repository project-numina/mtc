module
public import PropertyF.Ground.Dimensions.ENOMatrices
public import PropertyF.Ground.Dimensions.DualTensorNaturality
public import PropertyF.Ground.Dimensions.GroundNorm

/-! # Scalar twists and tensor extension

Scalar sign twists and tensor-defect identities describe extensions from simple objects.

## Main results

* `rootSignTwist`: constructs a scalar twist of the fourth-dual root.
* `doubleDualTensor_extension`: extends the tensor compatibility from simple objects.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

section
variable (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0)

/-- The fourth-dual root twisted by scalar signs on simple objects. -/
def rootSignTwist :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj :=
  simpleScalarNaturalIso C c hc ≪≫ fourthDualRootNaturalIso C

/-- The scalar-twisted root has the canonical double-dual unit component. -/
abbrev RootSignUnitLaw : Prop :=
  ((rootSignTwist C c hc).app (𝟙_ C.Obj)).hom = (doubleDualUnitIso (C := C.Obj)).hom

/-- The tensor comparison induced by the sign-twisted root. -/
def rootSignTensorIso (X Y : C.Obj) :
    X ⊗ Y ≅ ((X ⊗ Y)ᘁ)ᘁ :=
  ((rootSignTwist C c hc).app X ⊗ᵢ (rootSignTwist C c hc).app Y) ≪≫
    doubleDualTensorIso X Y

/-- The defect of the sign-twisted root tensor comparison. -/
def rootSignDefect (X Y : C.Obj) : X ⊗ Y ≅ X ⊗ Y :=
  (rootSignTwist C c hc).app (X ⊗ Y) ≪≫ (rootSignTensorIso C c hc X Y).symm

end
variable {c : Fin (rank C) → ℂ} (hc : ∀ i, c i ≠ 0)

set_option backward.isDefEq.respectTransparency false in
theorem rootSignTwist_app_simple (i : Fin (rank C)) :
    ((rootSignTwist C c hc).app (simples C i)).hom =
      c i • ((fourthDualRootNaturalIso C).app (simples C i)).hom := by
  simp only [rootSignTwist, NatIso.trans_app, Iso.trans_hom,
    simpleScalarNaturalIso_app_simple]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem rootSignTensorIso_hom (i j : Fin (rank C)) :
    (rootSignTensorIso C c hc (simples C i) (simples C j)).hom =
      (c i * c j) • (rootTensorIso C (simples C i) (simples C j)).hom := by
  change (((rootSignTwist C c hc).app (simples C i)).hom ⊗ₘ
    ((rootSignTwist C c hc).app (simples C j)).hom) ≫ _ = _
  rw [rootSignTwist_app_simple, rootSignTwist_app_simple]
  simp [rootTensorIso, tensorHom_def, smul_smul, mul_comm]

theorem rootPhaseTensorIso_inv (i j : Fin (rank C)) :
    (rootSignTensorIso C c hc (simples C i) (simples C j)).inv =
      (c i * c j)⁻¹ • (rootTensorIso C (simples C i) (simples C j)).inv :=
  iso_inv_eq_inv_smul (mul_ne_zero (hc i) (hc j)) (rootSignTensorIso_hom C hc i j)

set_option backward.isDefEq.respectTransparency false in
theorem rootPhaseDefect_apply {i j k : Fin (rank C)}
    (f : simples C k ⟶ simples C i ⊗ simples C j) :
    f ≫ (rootSignDefect C c hc (simples C i) (simples C j)).hom =
      (c k / (c i * c j)) • (f ≫ (rootTensorDefect C (simples C i) (simples C j)).hom) := by
  have hn := (simpleScalarNaturalIso C c hc).hom.naturality f
  change f ≫ ((simpleScalarNaturalIso C c hc).app (simples C i ⊗ simples C j)).hom =
    ((simpleScalarNaturalIso C c hc).app (simples C k)).hom ≫ f at hn
  rw [simpleScalarNaturalIso_app_simple] at hn
  simp only [Linear.smul_comp] at hn
  simp only [rootSignDefect, Iso.trans_hom, Iso.symm_hom, rootSignTwist, NatIso.trans_app,
    Category.assoc, rootPhaseTensorIso_inv, Linear.comp_smul]
  rw [← Category.assoc, hn]
  simp [rootTensorDefect, Linear.smul_comp, smul_smul, div_eq_mul_inv, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem rootPhaseTensor_compatible_of_scaled_defects {i j : Fin (rank C)}
    (hdef : ∀ k, (c k / (c i * c j)) • (multiplicityDefect C i j k).toLinearMap = 1) :
    (rootSignTwist C c hc).app (simples C i ⊗ simples C j) =
      rootSignTensorIso C c hc (simples C i) (simples C j) := by
  classical
  let X := simples C i ⊗ simples C j
  have hid : (rootSignDefect C c hc (simples C i) (simples C j)).hom = 𝟙 X := by
    apply simpleInclusion_hom_ext C
    intro k t
    let f := simpleInclusion C X k t
    have hfd := congrArg (fun L => L f) (hdef k)
    change (c k / (c i * c j)) • multiplicityDefect C i j k f = f at hfd
    rw [multiplicityDefect_apply] at hfd
    simpa [f, X, hfd] using rootPhaseDefect_apply C hc f
  change ((rootSignTwist C c hc).app X).hom ≫ (rootSignTensorIso C c hc _ _).inv = 𝟙 X at hid
  apply Iso.ext
  simpa [X] using (Iso.comp_inv_eq (rootSignTensorIso C c hc _ _)).1 hid


end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The right quantum trace of the canonical unit double-dual map is one. -/
theorem rightQuantumTrace_unitIso : rightQuantumTrace (doubleDualUnitIso (C := C)) = 1 :=
  End.homEquiv.injective (unitDoubleDual_trace (C := C))

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
theorem doubleDualTensor_extension (a : 𝟭 C.Obj ≅ doubleDualFunctor C.Obj)
    (hpair : ∀ i j, (a.app (simples C i ⊗ simples C j)).hom =
      (((a.app (simples C i)).hom ⊗ₘ (a.app (simples C j)).hom) ≫
        (doubleDualTensorIso (simples C i) (simples C j)).hom))
    (X Y : C.Obj) : (a.app (X ⊗ Y)).hom =
      ((a.app X).hom ⊗ₘ (a.app Y).hom) ≫ (doubleDualTensorIso X Y).hom := by
  apply tensor_simples_hom_ext C
  intro i j sx sy
  have hn {A B : C.Obj} (f : A ⟶ B) :
      f ≫ (a.app B).hom = (a.app A).hom ≫ ((fᘁ)ᘁ) := a.hom.naturality f
  rw [hn (sx ⊗ₘ sy), hpair, Category.assoc, ← doubleDualTensorIso_natural,
    tensorHom_comp_tensorHom_assoc, ← hn sx, ← hn sy,
    ← tensorHom_comp_tensorHom, Category.assoc]

variable {c : Fin (rank C) → ℂ} (hc : ∀ i, c i ≠ 0)

set_option backward.isDefEq.respectTransparency false in
theorem rootSignQuantumTrace_simple (i : Fin (rank C)) :
    unitScalar C (rightQuantumTrace ((rootSignTwist C c hc).app (simples C i))) =
      c i * rootDimension C i := by
  simpa only [rootDimension, rootTrace_id, Ground.unitScalar_eq_equiv, map_smul, smul_eq_mul] using
    congrArg (Ground.unitScalarEquiv C) (rightQuantumTrace_smul_hom (rootSignTwist_app_simple C hc i))

set_option backward.isDefEq.respectTransparency false in
theorem naturalDoubleDual_unit_eq_of_trace_one
    {a : 𝟭 C.Obj ≅ doubleDualFunctor C.Obj}
    (htrace : unitScalar C (rightQuantumTrace (a.app (𝟙_ C.Obj))) = 1) :
    (a.app (𝟙_ C.Obj)).hom = (doubleDualUnitIso (C := C.Obj)).hom := by
  let : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  let : FiniteDimensional ℂ ((𝟙_ C.Obj) ⟶ (𝟙_ C.Obj)) := IsFusionCategory.hom_finite _ _
  obtain ⟨r, _, hr, _⟩ := isomorphisms_scalar (k := ℂ) (doubleDualUnitIso (C := C.Obj)) (a.app (𝟙_ C.Obj))
  rw [rightQuantumTrace_smul_hom hr, rightQuantumTrace_unitIso] at htrace
  have hr1 : r = 1 := by
    simpa only [Ground.unitScalar_eq_equiv, map_smul, map_one, smul_eq_mul, mul_one] using htrace
  simpa [hr1] using hr

set_option backward.isDefEq.respectTransparency false in
theorem rootSignTwist_unit_of_simple_dimension
    (hunit : c (unitIndex C) * rootDimension C (unitIndex C) = 1) :
    RootSignUnitLaw C c hc := by
  apply naturalDoubleDual_unit_eq_of_trace_one
  obtain ⟨e⟩ := unitIndex_iso C
  have hq := rightQuantumTrace_iso
    (j := (rootSignTwist C c hc).app (simples C (unitIndex C)))
    (k := (rootSignTwist C c hc).app (𝟙_ C.Obj)) e
    (by simpa [doubleDualFunctor] using (rootSignTwist C c hc).hom.naturality e.hom)
  rw [← hq, rootSignQuantumTrace_simple, hunit]


end PropertyF.Ground.Dimensions

end
