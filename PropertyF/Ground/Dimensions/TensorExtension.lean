module
public import PropertyF.Ground.Dimensions.ENOMatrices
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Dimensions.GroundNorm

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

def rootSignTwist (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) :
    𝟭 C.Obj ≅ doubleDualFunctor C.Obj :=
  simpleScalarNaturalIso C c hc ≪≫ fourthDualRootNaturalIso C

def rootSignTensorIso (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (X Y : C.Obj) :
    X ⊗ Y ≅ ((X ⊗ Y)ᘁ)ᘁ :=
  ((rootSignTwist C c hc).app X ⊗ᵢ (rootSignTwist C c hc).app Y) ≪≫
    doubleDualTensorIso X Y

def rootSignDefect (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (X Y : C.Obj) : X ⊗ Y ≅ X ⊗ Y :=
  (rootSignTwist C c hc).app (X ⊗ Y) ≪≫ (rootSignTensorIso C c hc X Y).symm

set_option backward.isDefEq.respectTransparency false in
theorem rootSignTwist_app_simple
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (i : Fin (Ground.rank C)) :
    ((rootSignTwist C c hc).app (Ground.simples C i)).hom =
      c i • ((fourthDualRootNaturalIso C).app (Ground.simples C i)).hom := by
  change ((simpleScalarNaturalIso C c hc).app (Ground.simples C i)).hom ≫
    ((fourthDualRootNaturalIso C).app (Ground.simples C i)).hom = _
  rw [simpleScalarNaturalIso_app_simple]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem rootSignTensorIso_hom
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (i j : Fin (Ground.rank C)) :
    (rootSignTensorIso C c hc (Ground.simples C i) (Ground.simples C j)).hom =
      (c i * c j) • (rootTensorIso C (Ground.simples C i) (Ground.simples C j)).hom := by
  change (((rootSignTwist C c hc).app (Ground.simples C i)).hom ⊗ₘ
    ((rootSignTwist C c hc).app (Ground.simples C j)).hom) ≫ _ = _
  rw [rootSignTwist_app_simple, rootSignTwist_app_simple]
  simp [rootTensorIso, tensorHom_def, smul_smul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem rootPhaseTensorIso_inv
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    (i j : Fin (Ground.rank C)) :
    (rootSignTensorIso C c hc (Ground.simples C i) (Ground.simples C j)).inv =
      (c i * c j)⁻¹ • (rootTensorIso C (Ground.simples C i) (Ground.simples C j)).inv := by
  have hn : c i * c j ≠ 0 := mul_ne_zero (hc i) (hc j)
  apply (cancel_epi (rootSignTensorIso C c hc (Ground.simples C i) (Ground.simples C j)).hom).1
  rw [Iso.hom_inv_id, rootSignTensorIso_hom]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul, Iso.hom_inv_id]
  have hr : (c i * c j)⁻¹ * (c i * c j) = 1 := inv_mul_cancel₀ hn
  rw [hr, one_smul]

set_option backward.isDefEq.respectTransparency false in
theorem rootPhaseDefect_apply
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    (i j k : Fin (Ground.rank C))
    (f : Ground.simples C k ⟶ Ground.simples C i ⊗ Ground.simples C j) :
    f ≫ (rootSignDefect C c hc (Ground.simples C i) (Ground.simples C j)).hom =
      (c k / (c i * c j)) • (f ≫ (rootTensorDefect C (Ground.simples C i) (Ground.simples C j)).hom) := by
  have hn := (simpleScalarNaturalIso C c hc).hom.naturality f
  simp only [Functor.id_map] at hn
  change f ≫ ((simpleScalarNaturalIso C c hc).app (Ground.simples C i ⊗ Ground.simples C j)).hom =
    ((simpleScalarNaturalIso C c hc).app (Ground.simples C k)).hom ≫ f at hn
  rw [simpleScalarNaturalIso_app_simple] at hn
  have hn' : f ≫ ((simpleScalarNaturalIso C c hc).app (Ground.simples C i ⊗ Ground.simples C j)).hom =
      c k • f := by simpa [Linear.smul_comp] using hn
  simp only [rootSignDefect, Iso.trans_hom, Iso.symm_hom, rootSignTwist, NatIso.trans_app,
    Category.assoc]
  rw [rootPhaseTensorIso_inv C c hc i j]
  simp only [Linear.comp_smul]
  rw [← Category.assoc, hn']
  simp [rootTensorDefect, Linear.smul_comp, smul_smul, div_eq_mul_inv, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem rootPhaseTensor_compatible_of_scaled_defects (c : Fin (Ground.rank C) → ℂ)
    (hc : ∀ i, c i ≠ 0) (i j : Fin (Ground.rank C))
    (hdef : ∀ k, (c k / (c i * c j)) • (multiplicityDefect C i j k).toLinearMap = 1) :
    (rootSignTwist C c hc).app (Ground.simples C i ⊗ Ground.simples C j) =
      rootSignTensorIso C c hc (Ground.simples C i) (Ground.simples C j) := by
  classical
  let X := Ground.simples C i ⊗ Ground.simples C j
  let e := simpleDecomposition C X
  let V := simplePiecesObject C X
  have hid : (rootSignDefect C c hc (Ground.simples C i) (Ground.simples C j)).hom = 𝟙 X := by
    apply (cancel_epi e.inv).1
    apply biproduct.hom_ext'
    intro a
    let f : Ground.simples C a.1 ⟶ X := biproduct.ι V a ≫ e.inv
    have hfd := congrArg (fun L => L f) (hdef a.1)
    change (c a.1 / (c i * c j)) • multiplicityDefect C i j a.1 f = f at hfd
    rw [multiplicityDefect_apply] at hfd
    have ht := rootPhaseDefect_apply C c hc i j a.1 f
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
  let hp : ExactPairing (𝟙_ C) (rightDualObject (𝟙_ C)) :=
    @HasRightDual.exact C _ _ (𝟙_ C) (RightRigidCategory.rightDual (𝟙_ C))
  let hq : ExactPairing (𝟙_ C) (𝟙_ C) := exactPairingUnit
  let r := rightDualIso hp hq
  have h := trace_change_rightDual hp hq r.inv
  have hev := rightDualIso_inv_evaluation hp hq
  apply End.homEquiv.injective
  change @ExactPairing.coevaluation C _ _ (𝟙_ C) (rightDualObject (𝟙_ C)) hp ≫
    ((r.inv ≫ @rightAdjointMate C _ _ (rightDualObject (𝟙_ C)) (𝟙_ C)
      (RightRigidCategory.rightDual _) (RightRigidCategory.rightDual _) r.hom) ⊗ₘ
        𝟙 (rightDualObject (𝟙_ C))) ≫
      @ExactPairing.evaluation C _ _ (rightDualObject (𝟙_ C))
        (rightDualObject (rightDualObject (𝟙_ C)))
        (@HasRightDual.exact C _ _ _ (RightRigidCategory.rightDual _)) = 𝟙 (𝟙_ C)
  have hfinal : @ExactPairing.coevaluation C _ _ (𝟙_ C) (𝟙_ C) hq ≫
      (r.inv ⊗ₘ 𝟙 (𝟙_ C)) ≫
      @ExactPairing.evaluation C _ _ (𝟙_ C) (rightDualObject (𝟙_ C)) hp = 𝟙 (𝟙_ C) := by
    simp only [tensorHom_def, whiskerLeft_id, Category.comp_id]
    change @ExactPairing.coevaluation C _ _ (𝟙_ C) (𝟙_ C) hq ≫
      ((rightDualIso hp hq).inv ▷ (𝟙_ C) ≫
        @ExactPairing.evaluation C _ _ (𝟙_ C) (rightDualObject (𝟙_ C)) hp) = 𝟙 (𝟙_ C)
    rw [hev]
    change (ρ_ (𝟙_ C)).inv ≫ (ρ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C)
    exact Iso.inv_hom_id _
  exact h.trans hfinal

end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : Ground.BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
theorem doubleDualTensor_extension (a : 𝟭 C.Obj ≅ doubleDualFunctor C.Obj)
    (hnat : ∀ {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y'),
      (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
        (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ))
    (hpair : ∀ i j, (a.app (Ground.simples C i ⊗ Ground.simples C j)).hom =
      (((a.app (Ground.simples C i)).hom ⊗ₘ (a.app (Ground.simples C j)).hom) ≫
        (doubleDualTensorIso (Ground.simples C i) (Ground.simples C j)).hom))
    (X Y : C.Obj) : (a.app (X ⊗ Y)).hom =
      ((a.app X).hom ⊗ₘ (a.app Y).hom) ≫ (doubleDualTensorIso X Y).hom := by
  classical
  let ex := simpleDecomposition C X
  let ey := simpleDecomposition C Y
  let V := simplePiecesObject C X
  let W := simplePiecesObject C Y
  apply (cancel_epi (ex.symm ⊗ᵢ ey.symm).hom).1
  apply tensorBiproduct_hom_ext C V W
  intro i j
  let sx : Ground.simples C i.1 ⟶ X := biproduct.ι V i ≫ ex.inv
  let sy : Ground.simples C j.1 ⟶ Y := biproduct.ι W j ≫ ey.inv
  have hx := a.hom.naturality sx
  have hy := a.hom.naturality sy
  have hz := a.hom.naturality (sx ⊗ₘ sy)
  change sx ≫ (a.app X).hom = (a.app (Ground.simples C i.1)).hom ≫ ((sxᘁ)ᘁ) at hx
  change sy ≫ (a.app Y).hom = (a.app (Ground.simples C j.1)).hom ≫ ((syᘁ)ᘁ) at hy
  change (sx ⊗ₘ sy) ≫ (a.app (X ⊗ Y)).hom =
    (a.app (Ground.simples C i.1 ⊗ Ground.simples C j.1)).hom ≫ (((sx ⊗ₘ sy)ᘁ)ᘁ) at hz
  have hh : (sx ⊗ₘ sy) ≫ (a.app (X ⊗ Y)).hom =
      (sx ⊗ₘ sy) ≫ (((a.app X).hom ⊗ₘ (a.app Y).hom) ≫ (doubleDualTensorIso X Y).hom) := by
    calc
      _ = (a.app (Ground.simples C i.1 ⊗ Ground.simples C j.1)).hom ≫ (((sx ⊗ₘ sy)ᘁ)ᘁ) := hz
      _ = (((a.app (Ground.simples C i.1)).hom ⊗ₘ (a.app (Ground.simples C j.1)).hom) ≫
        (doubleDualTensorIso _ _).hom) ≫ (((sx ⊗ₘ sy)ᘁ)ᘁ) := by rw [hpair]
      _ = ((a.app (Ground.simples C i.1)).hom ⊗ₘ (a.app (Ground.simples C j.1)).hom) ≫
        ((((sxᘁ)ᘁ) ⊗ₘ ((syᘁ)ᘁ)) ≫ (doubleDualTensorIso X Y).hom) := by rw [Category.assoc, ← hnat]
      _ = ((sx ≫ (a.app X).hom) ⊗ₘ (sy ≫ (a.app Y).hom)) ≫ (doubleDualTensorIso X Y).hom := by
        rw [tensorHom_comp_tensorHom_assoc, ← hx, ← hy]
      _ = _ := by rw [← tensorHom_comp_tensorHom, Category.assoc]
  simpa [sx, sy, ex, ey, V, W, tensorIso_hom, tensorHom_comp_tensorHom,
    Category.assoc] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
theorem rootSignQuantumTrace_simple
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (i : Fin (Ground.rank C)) :
    Ground.unitScalar C (rightQuantumTrace ((rootSignTwist C c hc).app (Ground.simples C i))) =
      c i * rootDimension C i := by
  have hq : rightQuantumTrace ((rootSignTwist C c hc).app (Ground.simples C i)) =
      c i • rootTrace C (𝟙 (Ground.simples C i)) := by
    apply End.homEquiv.injective
    have h := rootSignTwist_app_simple C c hc i
    change (rootSignTwist C c hc).hom.app (Ground.simples C i) = _ at h
    simp [rightQuantumTrace, rootTrace, rightTraceWith, h, tensorHom_def]
  rw [hq]
  unfold rootDimension
  simp only [← groundUnitScalarEquiv_apply, map_smul, smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
theorem naturalDoubleDual_unit_eq_of_trace_one
    (a : 𝟭 C.Obj ≅ doubleDualFunctor C.Obj)
    (htrace : Ground.unitScalar C (rightQuantumTrace (a.app (𝟙_ C.Obj))) = 1) :
    (a.app (𝟙_ C.Obj)).hom = (doubleDualUnitIso (C := C.Obj)).hom := by
  letI : Simple (𝟙_ C.Obj) := Ground.IsFusionCategory.unit_simple
  letI : FiniteDimensional ℂ ((𝟙_ C.Obj) ⟶ (𝟙_ C.Obj)) := Ground.IsFusionCategory.hom_finite _ _
  obtain ⟨r, _, hr, _⟩ := doubleDualIso_scalar (doubleDualUnitIso (C := C.Obj)) (a.app (𝟙_ C.Obj))
  have ht : rightQuantumTrace (a.app (𝟙_ C.Obj)) = r • rightQuantumTrace (doubleDualUnitIso (C := C.Obj)) := by
    apply End.homEquiv.injective
    have hr' : a.hom.app (𝟙_ C.Obj) = r • (doubleDualUnitIso (C := C.Obj)).hom := hr
    simp [rightQuantumTrace, hr', tensorHom_def]
  rw [ht, rightQuantumTrace_unitIso] at htrace
  have hr1 : r = 1 := by
    simpa only [← groundUnitScalarEquiv_apply, map_smul, map_one, smul_eq_mul, mul_one] using htrace
  simpa [hr1] using hr

set_option backward.isDefEq.respectTransparency false in
theorem rootSignTwist_unit_of_simple_dimension
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0)
    (hunit : c (Ground.unitIndex C) * rootDimension C (Ground.unitIndex C) = 1) :
    ((rootSignTwist C c hc).app (𝟙_ C.Obj)).hom = (doubleDualUnitIso (C := C.Obj)).hom := by
  apply naturalDoubleDual_unit_eq_of_trace_one
  obtain ⟨e⟩ := Ground.unitIndex_iso C
  have hn := (rootSignTwist C c hc).hom.naturality e.hom
  have hq := rightQuantumTrace_iso
    ((rootSignTwist C c hc).app (Ground.simples C (Ground.unitIndex C)))
    ((rootSignTwist C c hc).app (𝟙_ C.Obj)) e (by simpa [doubleDualFunctor] using hn)
  rw [← hq, rootSignQuantumTrace_simple, hunit]


end PropertyF.Ground.Dimensions

end
