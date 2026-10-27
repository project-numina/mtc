module
public import PropertyF.Ground.Dimensions.ENOMatrices

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u
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
theorem rootSignTwist_app_simple (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (i : Fin (Ground.rank C)) :
    ((rootSignTwist C c hc).app (Ground.simples C i)).hom =
      c i • ((fourthDualRootNaturalIso C).app (Ground.simples C i)).hom := by
  change ((simpleScalarNaturalIso C c hc).app (Ground.simples C i)).hom ≫
    ((fourthDualRootNaturalIso C).app (Ground.simples C i)).hom = _
  rw [simpleScalarNaturalIso_app_simple]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem rootSignTensorIso_hom (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (i j : Fin (Ground.rank C)) :
    (rootSignTensorIso C c hc (Ground.simples C i) (Ground.simples C j)).hom =
      (c i * c j) • (rootTensorIso C (Ground.simples C i) (Ground.simples C j)).hom := by
  change (((rootSignTwist C c hc).app (Ground.simples C i)).hom ⊗ₘ
    ((rootSignTwist C c hc).app (Ground.simples C j)).hom) ≫ _ = _
  rw [rootSignTwist_app_simple, rootSignTwist_app_simple]
  simp [rootTensorIso, tensorHom_def, smul_smul, mul_comm]

set_option backward.isDefEq.respectTransparency false in
theorem rootSignTensorIso_inv (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (hs : ∀ i, c i * c i = 1)
    (i j : Fin (Ground.rank C)) :
    (rootSignTensorIso C c hc (Ground.simples C i) (Ground.simples C j)).inv =
      (c i * c j) • (rootTensorIso C (Ground.simples C i) (Ground.simples C j)).inv := by
  have hsq : (c i * c j) * (c i * c j) = 1 := by
    rw [show (c i * c j) * (c i * c j) = (c i * c i) * (c j * c j) by ring, hs i, hs j]
    norm_num
  apply (cancel_epi (rootSignTensorIso C c hc (Ground.simples C i) (Ground.simples C j)).hom).1
  rw [Iso.hom_inv_id, rootSignTensorIso_hom]
  simp [Linear.smul_comp, Linear.comp_smul, smul_smul, hsq]

set_option backward.isDefEq.respectTransparency false in
theorem rootSignDefect_apply (C : Ground.BraidedFusionCategory.{v,u})
    (c : Fin (Ground.rank C) → ℂ) (hc : ∀ i, c i ≠ 0) (hs : ∀ i, c i * c i = 1)
    (i j k : Fin (Ground.rank C))
    (f : Ground.simples C k ⟶ Ground.simples C i ⊗ Ground.simples C j) :
    f ≫ (rootSignDefect C c hc (Ground.simples C i) (Ground.simples C j)).hom =
      (c k * (c i * c j)) • (f ≫ (rootTensorDefect C (Ground.simples C i) (Ground.simples C j)).hom) := by
  have hn := (simpleScalarNaturalIso C c hc).hom.naturality f
  simp only [Functor.id_map] at hn
  change f ≫ ((simpleScalarNaturalIso C c hc).app (Ground.simples C i ⊗ Ground.simples C j)).hom =
    ((simpleScalarNaturalIso C c hc).app (Ground.simples C k)).hom ≫ f at hn
  rw [simpleScalarNaturalIso_app_simple] at hn
  have hn' : f ≫ ((simpleScalarNaturalIso C c hc).app (Ground.simples C i ⊗ Ground.simples C j)).hom =
      c k • f := by simpa [Linear.smul_comp] using hn
  simp only [rootSignDefect, Iso.trans_hom, Iso.symm_hom, rootSignTwist, NatIso.trans_app,
    Category.assoc]
  rw [rootSignTensorIso_inv C c hc hs i j]
  simp only [Linear.comp_smul]
  rw [← Category.assoc, hn']
  simp [rootTensorDefect, Linear.smul_comp, smul_smul, mul_comm, mul_left_comm]

set_option backward.isDefEq.respectTransparency false in
theorem rootSignTensor_compatible_of_scalar_defects
    (C : Ground.BraidedFusionCategory.{v,u}) (c : Fin (Ground.rank C) → ℂ)
    (hc : ∀ i, c i ≠ 0) (hs : ∀ i, c i * c i = 1)
    (i j : Fin (Ground.rank C))
    (hdef : ∀ k, (multiplicityDefect C i j k).toLinearMap =
      (c i * c j * c k) • 1) :
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
    change multiplicityDefect C i j a.1 f = (c i * c j * c a.1) • f at hfd
    rw [multiplicityDefect_apply] at hfd
    have ht := rootSignDefect_apply C c hc hs i j a.1 f
    rw [hfd, smul_smul] at ht
    have hsign : (c a.1 * (c i * c j)) * (c i * c j * c a.1) = 1 := by
      rw [show (c a.1 * (c i * c j)) * (c i * c j * c a.1) =
        (c i * c i) * (c j * c j) * (c a.1 * c a.1) by ring, hs i, hs j, hs a.1]
      norm_num
    rw [hsign, one_smul] at ht
    simpa [f, Category.assoc] using ht
  apply Iso.ext
  have hid' : ((rootSignTwist C c hc).app X).hom ≫ (rootSignTensorIso C c hc _ _).inv = 𝟙 X := hid
  apply (cancel_mono (rootSignTensorIso C c hc _ _).inv).1
  simpa [X] using hid'

set_option backward.isDefEq.respectTransparency false in
theorem rootPhaseTensorIso_inv (C : Ground.BraidedFusionCategory.{v,u})
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
theorem rootPhaseDefect_apply (C : Ground.BraidedFusionCategory.{v,u})
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
theorem rootPhaseTensor_compatible_of_scaled_defects
    (C : Ground.BraidedFusionCategory.{v,u}) (c : Fin (Ground.rank C) → ℂ)
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
