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

/-- The fourth-dual root twisted by scalar signs on simple objects. -/
def rootSignTwist (C : BraidedFusionCategory.{v,u})
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0) :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj :=
  simpleScalarNaturalIso C c hc ≪≫ fourthDualRootNaturalIso C

/-- The scalar-twisted root has the canonical double-dual unit component. -/
abbrev RootSignUnitLaw (C : BraidedFusionCategory.{v,u})
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0) : Prop :=
  ((rootSignTwist C c hc).app (𝟙_ C.Obj)).hom = (doubleDualUnitIso (C := C.Obj)).hom

/-- The tensor comparison induced by the sign-twisted root. -/
def rootSignTensorIso (C : BraidedFusionCategory.{v,u})
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (X Y : C.Obj) :
    X ⊗ Y ≅ ((X ⊗ Y)ᘁ)ᘁ :=
  ((rootSignTwist C c hc).app X ⊗ᵢ (rootSignTwist C c hc).app Y) ≪≫
    doubleDualTensorIso X Y

/-- The defect of the sign-twisted root tensor comparison. -/
def rootSignDefect (C : BraidedFusionCategory.{v,u})
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (X Y : C.Obj) : X ⊗ Y ≅ X ⊗ Y :=
  (rootSignTwist C c hc).app (X ⊗ Y) ≪≫ (rootSignTensorIso C c hc X Y).symm

set_option backward.isDefEq.respectTransparency false in
theorem rootSignTwist_app_simple
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (i : Fin (rank C)) :
    ((rootSignTwist C c hc).app (simples C i)).hom =
      c i • ((fourthDualRootNaturalIso C).app (simples C i)).hom := by
  change ((simpleScalarNaturalIso C c hc).app (simples C i)).hom ≫
    ((fourthDualRootNaturalIso C).app (simples C i)).hom = _
  rw [simpleScalarNaturalIso_app_simple]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem rootSignTensorIso_hom
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (i j : Fin (rank C)) :
    (rootSignTensorIso C c hc (simples C i) (simples C j)).hom =
      (c i * c j) • (rootTensorIso C (simples C i) (simples C j)).hom := by
  change (((rootSignTwist C c hc).app (simples C i)).hom ⊗ₘ
    ((rootSignTwist C c hc).app (simples C j)).hom) ≫ _ = _
  rw [rootSignTwist_app_simple, rootSignTwist_app_simple]
  simp [rootTensorIso, tensorHom_def, smul_smul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem rootPhaseTensorIso_inv
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    (i j : Fin (rank C)) :
    (rootSignTensorIso C c hc (simples C i) (simples C j)).inv =
      (c i * c j)⁻¹ • (rootTensorIso C (simples C i) (simples C j)).inv := by
  have hn : c i * c j ≠ 0 := mul_ne_zero (hc i) (hc j)
  apply (cancel_epi (rootSignTensorIso C c hc (simples C i) (simples C j)).hom).1
  rw [Iso.hom_inv_id, rootSignTensorIso_hom]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, Iso.hom_inv_id]
  have hr : (c i * c j)⁻¹ * (c i * c j) = 1 := inv_mul_cancel₀ hn
  rw [hr, one_smul]

set_option backward.isDefEq.respectTransparency false in
theorem rootPhaseDefect_apply
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    {i j k : Fin (rank C)}
    (f : simples C k ⟶ simples C i ⊗ simples C j) :
    f ≫ (rootSignDefect C c hc (simples C i) (simples C j)).hom =
      (c k / (c i * c j)) • (f ≫ (rootTensorDefect C (simples C i) (simples C j)).hom) := by
  have hn := (simpleScalarNaturalIso C c hc).hom.naturality f
  simp only [Functor.id_map] at hn
  change f ≫ ((simpleScalarNaturalIso C c hc).app (simples C i ⊗ simples C j)).hom =
    ((simpleScalarNaturalIso C c hc).app (simples C k)).hom ≫ f at hn
  rw [simpleScalarNaturalIso_app_simple] at hn
  have hn' : f ≫ ((simpleScalarNaturalIso C c hc).app (simples C i ⊗ simples C j)).hom =
      c k • f := by simpa [Linear.smul_comp] using hn
  simp only [rootSignDefect, Iso.trans_hom, Iso.symm_hom, rootSignTwist, NatIso.trans_app,
    Category.assoc]
  rw [rootPhaseTensorIso_inv C c hc i j]
  simp only [Linear.comp_smul]
  rw [← Category.assoc, hn']
  simp [rootTensorDefect, Linear.smul_comp, smul_smul, div_eq_mul_inv, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem rootPhaseTensor_compatible_of_scaled_defects (c : Fin (rank C) → ℂ)
    (hc : ∀ i, c i ≠ 0) {i j : Fin (rank C)}
    (hdef : ∀ k, (c k / (c i * c j)) • (multiplicityDefect C i j k).toLinearMap = 1) :
    (rootSignTwist C c hc).app (simples C i ⊗ simples C j) =
      rootSignTensorIso C c hc (simples C i) (simples C j) := by
  classical
  let X := simples C i ⊗ simples C j
  let e := simpleDecomposition C X
  let V := simplePiecesObject C X
  have hid : (rootSignDefect C c hc (simples C i) (simples C j)).hom = 𝟙 X := by
    apply (cancel_epi e.inv).1
    apply biproduct.hom_ext'
    intro a
    let f : simples C a.1 ⟶ X := biproduct.ι V a ≫ e.inv
    have hfd := congrArg (fun L => L f) (hdef a.1)
    change (c a.1 / (c i * c j)) • multiplicityDefect C i j a.1 f = f at hfd
    rw [multiplicityDefect_apply] at hfd
    have ht := rootPhaseDefect_apply C c hc f
    rw [hfd] at ht
    simpa [f, Category.assoc] using ht
  apply Iso.ext
  have hid' : ((rootSignTwist C c hc).app X).hom ≫ (rootSignTensorIso C c hc _ _).inv = 𝟙 X := hid
  apply (cancel_mono (rootSignTensorIso C c hc _ _).inv).1
  simpa [X] using hid'


end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
/-- The right quantum trace of the canonical unit double-dual map is one. -/
theorem rightQuantumTrace_unitIso : rightQuantumTrace (doubleDualUnitIso (C := C)) = 1 := by
  apply End.homEquiv.injective
  exact unitDoubleDual_trace (C := C)

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
  have hx := a.hom.naturality sx
  have hy := a.hom.naturality sy
  have hz := a.hom.naturality (sx ⊗ₘ sy)
  change sx ≫ (a.app X).hom = (a.app (simples C i)).hom ≫ ((sxᘁ)ᘁ) at hx
  change sy ≫ (a.app Y).hom = (a.app (simples C j)).hom ≫ ((syᘁ)ᘁ) at hy
  change (sx ⊗ₘ sy) ≫ (a.app (X ⊗ Y)).hom =
    (a.app (simples C i ⊗ simples C j)).hom ≫ (((sx ⊗ₘ sy)ᘁ)ᘁ) at hz
  calc
    _ = (a.app (simples C i ⊗ simples C j)).hom ≫ (((sx ⊗ₘ sy)ᘁ)ᘁ) := hz
    _ = (((a.app (simples C i)).hom ⊗ₘ (a.app (simples C j)).hom) ≫
      (doubleDualTensorIso _ _).hom) ≫ (((sx ⊗ₘ sy)ᘁ)ᘁ) := by rw [hpair]
    _ = ((a.app (simples C i)).hom ⊗ₘ (a.app (simples C j)).hom) ≫
      ((((sxᘁ)ᘁ) ⊗ₘ ((syᘁ)ᘁ)) ≫ (doubleDualTensorIso X Y).hom) := by rw [Category.assoc, ← doubleDualTensorIso_natural]
    _ = ((sx ≫ (a.app X).hom) ⊗ₘ (sy ≫ (a.app Y).hom)) ≫ (doubleDualTensorIso X Y).hom := by
      rw [tensorHom_comp_tensorHom_assoc, ← hx, ← hy]
    _ = _ := by rw [← tensorHom_comp_tensorHom, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem rootSignQuantumTrace_simple
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (i : Fin (rank C)) :
    unitScalar C (rightQuantumTrace ((rootSignTwist C c hc).app (simples C i))) =
      c i * rootDimension C i := by
  have hq : rightQuantumTrace ((rootSignTwist C c hc).app (simples C i)) =
      c i • rootTrace C (𝟙 (simples C i)) := by
    rw [rootTrace_id]
    exact rightQuantumTrace_smul_hom _ _ _ (rootSignTwist_app_simple C c hc i)
  rw [hq]
  unfold rootDimension
  simp only [Ground.unitScalar_eq_equiv, map_smul, smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
theorem naturalDoubleDual_unit_eq_of_trace_one
    (a : 𝟭 C.Obj ≅ doubleDualFunctor C.Obj)
    (htrace : unitScalar C (rightQuantumTrace (a.app (𝟙_ C.Obj))) = 1) :
    (a.app (𝟙_ C.Obj)).hom = (doubleDualUnitIso (C := C.Obj)).hom := by
  let : Simple (𝟙_ C.Obj) := IsFusionCategory.unit_simple
  let : FiniteDimensional ℂ ((𝟙_ C.Obj) ⟶ (𝟙_ C.Obj)) := IsFusionCategory.hom_finite _ _
  obtain ⟨r, _, hr, _⟩ := isomorphisms_scalar (doubleDualUnitIso (C := C.Obj)) (a.app (𝟙_ C.Obj))
  have ht : rightQuantumTrace (a.app (𝟙_ C.Obj)) = r • rightQuantumTrace (doubleDualUnitIso (C := C.Obj)) := by
    apply End.homEquiv.injective
    have hr' : a.hom.app (𝟙_ C.Obj) = r • (doubleDualUnitIso (C := C.Obj)).hom := hr
    simp [rightQuantumTrace, hr', tensorHom_def]
  rw [ht, rightQuantumTrace_unitIso] at htrace
  have hr1 : r = 1 := by
    simpa only [Ground.unitScalar_eq_equiv, map_smul, map_one, smul_eq_mul, mul_one] using htrace
  simpa [hr1] using hr

set_option backward.isDefEq.respectTransparency false in
theorem rootSignTwist_unit_of_simple_dimension
    (c : Fin (rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hunit : c (unitIndex C) * rootDimension C (unitIndex C) = 1) :
    RootSignUnitLaw C c hc := by
  apply naturalDoubleDual_unit_eq_of_trace_one
  obtain ⟨e⟩ := unitIndex_iso C
  have hn := (rootSignTwist C c hc).hom.naturality e.hom
  have hq := rightQuantumTrace_iso
    ((rootSignTwist C c hc).app (simples C (unitIndex C)))
    ((rootSignTwist C c hc).app (𝟙_ C.Obj)) e (by simpa [doubleDualFunctor] using hn)
  rw [← hq, rootSignQuantumTrace_simple, hunit]


end PropertyF.Ground.Dimensions

end
