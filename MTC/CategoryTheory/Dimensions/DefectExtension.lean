module
public import MTC.CategoryTheory.Dimensions.DualCoherence
public import MTC.CategoryTheory.Dimensions.FourthDualUnit
public import MTC.CategoryTheory.Dimensions.DoubleDualPairing
public import MTC.CategoryTheory.Dimensions.MultiplicityDefect
public import MTC.CategoryTheory.Dimensions.DefectNaturality
public import MTC.CategoryTheory.Dimensions.RootDualLabel
public import MTC.CategoryTheory.Dimensions.FourthTensorUnit

public import MTC.CategoryTheory.Dimensions.TensorExtension

/-! # Extending tensor-defect identities

Duality, associativity and coevaluation identities extend root tensor-defect relations.

## Main results

* `rootTensorDefect_coevaluation`: relates the tensor defect to coevaluation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

/-- A scalar eigenvector pulls back along a monomorphism intertwining two endomorphisms. -/
theorem scalar_eigenvector_of_mono {k : Type*} [CommSemiring k]
    {D : Type u} [Category.{v} D] [Preadditive D] [Linear k D]
    {I A B : D} {u : I ⟶ A} {v : I ⟶ B} {s : A ⟶ B} [Mono s]
    {f : A ⟶ A} {g : B ⟶ B} {c : k}
    (hu : u ≫ s = v) (hfg : s ≫ g = f ≫ s) (hv : v ≫ g = c • v) :
    u ≫ f = c • u :=
  (cancel_mono s).1 <| by
    rw [Category.assoc, ← hfg, ← Category.assoc, hu, hv, ← hu, Linear.smul_comp]

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The root tensor defect acts on a simple duality cup by the product of the unit-root and dual signs. -/
theorem rootTensorDefect_coevaluation (i : Fin (rank C)) :
    let X := simples C i
    η_ X (Xᘁ) ≫ (rootTensorDefect C X (Xᘁ)).hom =
      (rootDimension C (unitIndex C) * (rootDualSign C i).1) • η_ X (Xᘁ) := by
  let I := 𝟙_ C.Obj
  let : HasRightDual I := RightRigidCategory.rightDual I
  let X := simples C i
  let W := X ⊗ (Xᘁ)
  let a := (fourthDualRootNaturalIso C).app X
  let b := (fourthDualRootNaturalIso C).app (Xᘁ)
  let t := rootTensorIso C X (Xᘁ)
  let e := (rootDualSign C i).1
  have hc : η_ X (Xᘁ) ≫ (a.hom ⊗ₘ b.hom) = e • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) :=
    root_components_coevaluation i
  have hn : η_ X (Xᘁ) ≫ ((fourthDualRootNaturalIso C).app W).hom =
    ((fourthDualRootNaturalIso C).app I).hom ≫ (((η_ X (Xᘁ))ᘁ)ᘁ) :=
    (fourthDualRootNaturalIso C).hom.naturality (η_ X (Xᘁ))
  have ht : η_ X (Xᘁ) ≫ t.hom =
      e • ((doubleDualUnitIso (C := C.Obj)).hom ≫ (((η_ X (Xᘁ))ᘁ)ᘁ)) := by
    change η_ X (Xᘁ) ≫ ((a.hom ⊗ₘ b.hom) ≫ (doubleDualTensorIso X (Xᘁ)).hom) = _
    rw [← Category.assoc, hc, Linear.smul_comp, ← doubleDual_coevaluation X]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono t.hom).1
  change (η_ X (Xᘁ) ≫ (((fourthDualRootNaturalIso C).app W).hom ≫ t.inv)) ≫ t.hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Linear.smul_comp]
  rw [hn, fourthDualRoot_unit_component, Linear.smul_comp, ht, ← mul_smul, mul_assoc,
    (rootDualSign C i).2.1, mul_one]
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The root defect has the same eigenvalue on the braided-swapped cup. -/
theorem rootTensorDefect_swapped_coevaluation (i : Fin (rank C)) :
    let X := simples C i
    letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
    η_ (Xᘁ) X ≫ (rootTensorDefect C (Xᘁ) X).hom =
      (rootDimension C (unitIndex C) * (rootDualSign C i).1) • η_ (Xᘁ) X :=
  let X := simples C i
  let A := Xᘁ
  letI : ExactPairing A X := BraidedCategory.exactPairing_swap X A
  let r : X ≅ (Xᘁ)ᘁ := rightDualIso inferInstance HasRightDual.exact
  let a := rightDualLabelIso C i
  scalar_eigenvector_of_mono (s := A ◁ r.hom)
    (coevaluation_rightDualIso inferInstance HasRightDual.exact)
    (by simpa only [id_tensorHom] using rootTensorDefect_natural C (𝟙 A) r.hom)
    (by simpa only [rootDualSign_dual] using (scalar_eigenvector_of_mono
      (s := (a ⊗ᵢ (rightDualIsoMap a).symm).hom) (coevaluation_iso_map a)
      (rootTensorDefect_natural C a.hom (rightDualIsoMap a).symm.hom)
      (rootTensorDefect_coevaluation (dualIndex C i))))
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The actual root tensor defect obeys the noncommutative tensor-cocycle law. -/
theorem rootTensorDefect_associativity (X Y Z : C.Obj) :
    (rootTensorDefect C X (Y ⊗ Z)).hom ≫ X ◁ (rootTensorDefect C Y Z).hom =
      (α_ X Y Z).inv ≫ (rootTensorDefect C (X ⊗ Y) Z).hom ≫
        (rootTensorDefect C X Y).hom ▷ Z ≫ (α_ X Y Z).hom := by
  let : (doubleDualFunctor C.Obj).Monoidal := doubleDualMonoidal C.Obj
  let : (doubleDualFunctor C.Obj).OplaxMonoidal := (doubleDualMonoidal C.Obj).toOplaxMonoidal
  let : (𝟭 C.Obj).OplaxMonoidal :=
    (Functor.Monoidal.transport (fourthDualRootNaturalIso C).symm).toOplaxMonoidal
  have hd (A B : C.Obj) : Functor.OplaxMonoidal.δ (𝟭 C.Obj) A B = (rootTensorDefect C A B).hom := by
    have hF : Functor.OplaxMonoidal.δ (doubleDualFunctor C.Obj) A B = (doubleDualTensorIso A B).inv := rfl
    simpa [rootTensorDefect, rootTensorIso, hF] using
      (Functor.Monoidal.transport_δ (fourthDualRootNaturalIso C).symm A B)
  simpa only [hd, Functor.id_obj, Functor.id_map] using
    Functor.OplaxMonoidal.δ_comp_whiskerLeft_δ (𝟭 C.Obj) X Y Z
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
variable {C} in
/-- The signed three-object cup slide follows from involutivity of its outer tensor defect. -/
theorem rootTensorDefect_slide_of_involution
    {i : Fin (rank C)} (K : C.Obj)
    (hinv : IsInvolutiveHom (rootTensorDefect C ((simples C i)ᘁ) (simples C i ⊗ K)).hom) :
    RootTensorDefectSlide C i K := by
  let X := simples C i
  let A := Xᘁ
  let I := 𝟙_ C.Obj
  let : ExactPairing A X := BraidedCategory.exactPairing_swap X A
  let cup : I ⟶ A ⊗ X := η_ A X
  let η : K ⟶ A ⊗ (X ⊗ K) := (λ_ K).inv ≫ cup ▷ K ≫ (α_ A X K).hom
  let D := (rootTensorDefect C A (X ⊗ K)).hom
  let E := A ◁ (rootTensorDefect C X K).hom
  let u := rootDimension C (unitIndex C)
  let e := (rootDualSign C i).1
  have hs : u * u = 1 := rootDimension_unit_sq C
  have hc : cup ≫ (rootTensorDefect C A X).hom = (u * e) • cup :=
    rootTensorDefect_swapped_coevaluation i
  have hn := rootTensorDefect_natural C cup (𝟙 K)
  simp only [tensorHom_id] at hn
  have hu : (rootTensorDefect C I K).hom = u • 𝟙 (I ⊗ K) := rootTensorDefect_unit_left C K
  have hcomm : E ≫ D = D ≫ E := by
    simpa only [id_tensorHom] using rootTensorDefect_natural C (𝟙 A) (rootTensorDefect C X K).hom
  have hloop : η ≫ D ≫ E = e • η := by
    change ((λ_ K).inv ≫ cup ▷ K ≫ (α_ A X K).hom) ≫ D ≫ E = _
    rw [Category.assoc, rootTensorDefect_associativity]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (cup ▷ K), hn]
    simp only [hu, Linear.smul_comp, Linear.comp_smul, Category.id_comp]
    rw [← comp_whiskerRight_assoc, hc]
    simp only [MonoidalLinear.smul_whiskerRight, Linear.comp_smul, Linear.smul_comp,
      smul_smul, ← mul_assoc, hs, one_mul]
    rfl
  change η ≫ E = e • (η ≫ D)
  rw [← hcomm] at hloop
  change D ≫ D = 𝟙 _ at hinv
  simpa only [Category.assoc, hinv, Category.comp_id, Linear.smul_comp] using
    (congrArg (fun f => f ≫ D) hloop)
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false in
/-- Involutivity on simple pairs extends to all object pairs by semisimple decomposition. -/
theorem rootTensorDefect_involution_extension
    (hsimple : ∀ i j, IsInvolutiveHom (rootTensorDefect C (simples C i) (simples C j)).hom)
    (X Y : C.Obj) : IsInvolutiveHom (rootTensorDefect C X Y).hom :=
  tensor_decomposition_hom_ext (simpleDecomposition C X) (simpleDecomposition C Y) fun sx sy ↦ by
    rw [← Category.assoc, rootTensorDefect_natural C sx sy, Category.assoc,
      rootTensorDefect_natural C sx sy, ← Category.assoc, hsimple, Category.id_comp, Category.comp_id]
variable {C} in
/-- The fourth-dual tensor law on simple pairs implies ENO trace reciprocity. -/
theorem trace_reciprocity_of_fourth_dual
    (hfourth : SimpleFourthDualTensorLaw C) :
    ENOTraceMatrixReciprocity C :=
  trace_reciprocity_of_coevaluation fun _ _ ↦ rootTensorDefect_slide_of_involution _
    (rootTensorDefect_involution_extension C (fun i j ↦ rootTensorDefect_involution_of_tensor_square C
      ((rootTensor_square_eq_fourthDual_tensor C _ _).trans (hfourth i j).symm)) _ _)

end PropertyF.Ground.Dimensions

end
