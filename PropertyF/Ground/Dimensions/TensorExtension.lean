module
public import PropertyF.Ground.Dimensions.RootSignTwist
public import PropertyF.Ground.Dimensions.UnitNorm

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u
attribute [local instance] Abelian.hasFiniteBiproducts

set_option backward.isDefEq.respectTransparency false in
theorem doubleDualTensor_extension
    (C : Ground.BraidedFusionCategory.{v,u}) (a : 𝟭 C.Obj ≅ doubleDualFunctor C.Obj)
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

/-- The sign-twisted root is a genuine pivotal structure once the double-dual
tensorator is natural, its simple-pair defects have the required signs, and
its unit component is normalized. -/
def rootSignPivotal (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (hs : ∀ i, c i * c i = 1)
    (hnat : ∀ {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y'),
      (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
        (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ))
    (hdef : ∀ i j k, (multiplicityDefect C i j k).toLinearMap = (c i * c j * c k) • 1)
    (hunit : ((rootSignTwist C c hc).app (𝟙_ C.Obj)).hom =
      (doubleDualUnitIso (C := C.Obj)).hom) : PivotalStructure (C := C.Obj) where
  iso X := (rootSignTwist C c hc).app X
  naturality {X Y} f := by
    have h := (rootSignTwist C c hc).hom.naturality f
    change f ≫ ((rootSignTwist C c hc).app Y).hom =
      ((rootSignTwist C c hc).app X).hom ≫ ((fᘁ)ᘁ) at h
    exact h
  tensor X Y := by
    apply doubleDualTensor_extension C (rootSignTwist C c hc) hnat
    intro i j
    exact congrArg Iso.hom (rootSignTensor_compatible_of_scalar_defects C c hc hs i j (hdef i j))
  unit := hunit

set_option backward.isDefEq.respectTransparency false in
theorem rootSignPivotal_dimension (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (hs : ∀ i, c i * c i = 1)
    (hnat : ∀ {X X' Y Y' : C.Obj} (f : X ⟶ X') (g : Y ⟶ Y'),
      (((fᘁ)ᘁ) ⊗ₘ ((gᘁ)ᘁ)) ≫ (doubleDualTensorIso X' Y').hom =
        (doubleDualTensorIso X Y).hom ≫ (((f ⊗ₘ g)ᘁ)ᘁ))
    (hdef : ∀ i j k, (multiplicityDefect C i j k).toLinearMap = (c i * c j * c k) • 1)
    (hunit : ((rootSignTwist C c hc).app (𝟙_ C.Obj)).hom =
      (doubleDualUnitIso (C := C.Obj)).hom) (i : Fin (Ground.rank C)) :
    pivotalDimension C (rootSignPivotal C c hc hs hnat hdef hunit) (Ground.simples C i) =
      c i * rootDimension C i := by
  have ht : (rootSignPivotal C c hc hs hnat hdef hunit).rightTrace (𝟙 (Ground.simples C i)) =
      c i • rootTrace C (𝟙 (Ground.simples C i)) := by
    apply End.homEquiv.injective
    have h := rootSignTwist_app_simple C c hc i
    change (rootSignTwist C c hc).hom.app (Ground.simples C i) = _ at h
    simp [PivotalStructure.rightTrace, rootSignPivotal, rootTrace, rightTraceWith, h, tensorHom_def]
  unfold pivotalDimension rootDimension
  rw [ht]
  simp only [← groundUnitScalarEquiv_apply, map_smul, smul_eq_mul]

set_option backward.isDefEq.respectTransparency false in
theorem rootSignQuantumTrace_simple (C : Ground.BraidedFusionCategory.{v,u})
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
theorem naturalDoubleDual_unit_eq_of_trace_one (C : Ground.BraidedFusionCategory.{v,u})
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
theorem rootSignTwist_unit_of_simple_dimension (C : Ground.BraidedFusionCategory.{v,u})
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
