module
public import PropertyF.Ground.Dimensions.DualCoherence
public import PropertyF.Ground.Dimensions.RootDualPairing
public import PropertyF.Ground.Dimensions.DoubleDualPairing
public import PropertyF.Ground.Dimensions.MultiplicityDefect
public import PropertyF.Ground.Dimensions.DefectNaturality
public import PropertyF.Ground.Dimensions.RootDualLabel
public import PropertyF.Ground.Dimensions.FourthTensorUnit
public import PropertyF.Ground.Dimensions.CoevaluationSliding
public import PropertyF.Ground.Dimensions.TensorExtension

/-! # Extending tensor-defect identities

Duality, associativity and coevaluation identities extend root tensor-defect relations.

## Main results

* `rootTensorDefect_coevaluation`: relates the tensor defect to coevaluation.
* `positive_spherical_of_nonunit_fourth_dual`: constructs a positive spherical structure from fourth-dual compatibility.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The root tensor defect acts on a simple duality cup by the product of the unit-root and dual signs. -/
theorem rootTensorDefect_coevaluation
    (i : Fin (rank C)) :
    let X := simples C i
    η_ X (Xᘁ) ≫ (rootTensorDefect C X (Xᘁ)).hom =
      (rootDimension C (unitIndex C) * rootDualSign C i) • η_ X (Xᘁ) := by
  let I := 𝟙_ C.Obj
  let : HasRightDual I := RightRigidCategory.rightDual I
  let X := simples C i
  let W := X ⊗ (Xᘁ)
  let : HasRightDual W := RightRigidCategory.rightDual W
  let a := (fourthDualRootNaturalIso C).app X
  let b := (fourthDualRootNaturalIso C).app (Xᘁ)
  let t := rootTensorIso C X (Xᘁ)
  let u := rootDimension C (unitIndex C)
  let e := rootDualSign C i
  have he : e * e = 1 := rootDualSign_sq C i
  have hc := root_components_coevaluation C i
  change η_ X (Xᘁ) ≫ (a.hom ⊗ₘ b.hom) = e • η_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ) at hc
  have hn := (fourthDualRootNaturalIso C).hom.naturality (η_ X (Xᘁ))
  change η_ X (Xᘁ) ≫ ((fourthDualRootNaturalIso C).app W).hom =
    ((fourthDualRootNaturalIso C).app I).hom ≫ (((η_ X (Xᘁ))ᘁ)ᘁ) at hn
  have hunit := fourthDualRoot_unit_component C
  change ((fourthDualRootNaturalIso C).app I).hom = u • (doubleDualUnitIso (C := C.Obj)).hom at hunit
  have hdual := doubleDual_coevaluation X
  have ht : η_ X (Xᘁ) ≫ t.hom =
      e • ((doubleDualUnitIso (C := C.Obj)).hom ≫ (((η_ X (Xᘁ))ᘁ)ᘁ)) := by
    change η_ X (Xᘁ) ≫ ((a.hom ⊗ₘ b.hom) ≫ (doubleDualTensorIso X (Xᘁ)).hom) = _
    rw [← Category.assoc, hc]
    simp only [Linear.smul_comp]
    congr 1
    apply (cancel_mono (doubleDualTensorIso X (Xᘁ)).inv).1
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hdual.symm
  apply (cancel_mono t.hom).1
  change (η_ X (Xᘁ) ≫ (((fourthDualRootNaturalIso C).app W).hom ≫ t.inv)) ≫ t.hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Linear.smul_comp]
  rw [hn, hunit, Linear.smul_comp, ht]
  rw [← mul_smul, mul_assoc, he, mul_one]
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})

set_option backward.isDefEq.respectTransparency false in
/-- The cup eigenvalue is invariant under changing the simple representative. -/
theorem rootTensorDefect_coevaluation_of_iso
    {X : C.Obj} (i : Fin (rank C)) (a : X ≅ simples C i) :
    η_ X (Xᘁ) ≫ (rootTensorDefect C X (Xᘁ)).hom =
      (rootDimension C (unitIndex C) * rootDualSign C i) • η_ X (Xᘁ) := by
  let Y := simples C i
  let b := (rightDualIsoMap a).symm
  let d := a ⊗ᵢ b
  have hc : η_ X (Xᘁ) ≫ d.hom = η_ Y (Yᘁ) := coevaluation_iso_map a
  have hn := rootTensorDefect_natural C a.hom b.hom
  change d.hom ≫ (rootTensorDefect C Y (Yᘁ)).hom =
    (rootTensorDefect C X (Xᘁ)).hom ≫ d.hom at hn
  apply (cancel_mono d.hom).1
  calc
    _ = η_ X (Xᘁ) ≫ (d.hom ≫ (rootTensorDefect C Y (Yᘁ)).hom) := by
      rw [hn, Category.assoc]
    _ = η_ Y (Yᘁ) ≫ (rootTensorDefect C Y (Yᘁ)).hom := by rw [← Category.assoc, hc]
    _ = _ := by rw [rootTensorDefect_coevaluation, ← hc, Linear.smul_comp]
set_option backward.isDefEq.respectTransparency false in
/-- The root defect has the same eigenvalue on the braided-swapped cup. -/
theorem rootTensorDefect_swapped_coevaluation
    (i : Fin (rank C)) :
    let X := simples C i
    letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
    η_ (Xᘁ) X ≫ (rootTensorDefect C (Xᘁ) X).hom =
      (rootDimension C (unitIndex C) * rootDualSign C i) • η_ (Xᘁ) X := by
  let X := simples C i
  let A := Xᘁ
  let Q := (Xᘁ)ᘁ
  let p : ExactPairing A X := BraidedCategory.exactPairing_swap X A
  let q : ExactPairing A Q := HasRightDual.exact
  let : ExactPairing A X := p
  let : ExactPairing A Q := q
  let r : X ≅ Q := rightDualIso p q
  have hc := coevaluation_rightDualIso p q
  change η_ A X ≫ A ◁ r.hom = η_ A Q at hc
  have hn := rootTensorDefect_natural C (𝟙 A) r.hom
  simp only [id_tensorHom] at hn
  have he := rootTensorDefect_coevaluation_of_iso C (dualIndex C i) (rightDualLabelIso C i)
  change η_ A Q ≫ (rootTensorDefect C A Q).hom = _ at he
  rw [rootDualSign_dual] at he
  apply (cancel_mono (A ◁ r.hom)).1
  calc
    _ = η_ A X ≫ ((A ◁ r.hom) ≫ (rootTensorDefect C A Q).hom) := by
      rw [hn, Category.assoc]
    _ = η_ A Q ≫ (rootTensorDefect C A Q).hom := by rw [← Category.assoc, hc]
    _ = _ := by rw [he, ← hc, Linear.smul_comp]
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
  have h := Functor.OplaxMonoidal.δ_comp_whiskerLeft_δ (𝟭 C.Obj) X Y Z
  simp only [hd, Functor.id_obj, Functor.id_map] at h
  exact h
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- The signed three-object cup slide follows from involutivity of its outer tensor defect. -/
theorem rootTensorDefect_slide_of_involution
    {i : Fin (rank C)} (K : C.Obj)
    (hinv : let X := simples C i
      (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom =
        𝟙 ((Xᘁ) ⊗ (X ⊗ K))) :
    let X := simples C i
    letI : ExactPairing (Xᘁ) X := BraidedCategory.exactPairing_swap X (Xᘁ)
    let η : K ⟶ (Xᘁ) ⊗ (X ⊗ K) :=
      (λ_ K).inv ≫ (η_ (Xᘁ) X ▷ K) ≫ (α_ (Xᘁ) X K).hom
    η ≫ (Xᘁ) ◁ (rootTensorDefect C X K).hom =
      rootDualSign C i • (η ≫ (rootTensorDefect C (Xᘁ) (X ⊗ K)).hom) := by
  let X := simples C i
  let A := Xᘁ
  let I := 𝟙_ C.Obj
  let p : ExactPairing A X := BraidedCategory.exactPairing_swap X A
  let : ExactPairing A X := p
  let cup : I ⟶ A ⊗ X := η_ A X
  let η : K ⟶ A ⊗ (X ⊗ K) := (λ_ K).inv ≫ cup ▷ K ≫ (α_ A X K).hom
  let D := (rootTensorDefect C A (X ⊗ K)).hom
  let E := A ◁ (rootTensorDefect C X K).hom
  let u := rootDimension C (unitIndex C)
  let e := rootDualSign C i
  have hs : u * u = 1 := rootDimension_unit_sq C
  have hc : cup ≫ (rootTensorDefect C A X).hom = (u * e) • cup :=
    rootTensorDefect_swapped_coevaluation C i
  have hn := rootTensorDefect_natural C cup (𝟙 K)
  simp only [tensorHom_id] at hn
  have hu : (rootTensorDefect C I K).hom = u • 𝟙 (I ⊗ K) := rootTensorDefect_unit_left C K
  have hcomm := rootTensorDefect_natural C (𝟙 A) (rootTensorDefect C X K).hom
  simp only [id_tensorHom] at hcomm
  change E ≫ D = D ≫ E at hcomm
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
  have hloop' : η ≫ E ≫ D = e • η := by rw [hcomm]; exact hloop
  change D ≫ D = 𝟙 _ at hinv
  simpa only [Category.assoc, hinv, Category.comp_id, Linear.smul_comp] using
    (congrArg (fun f => f ≫ D) hloop')
end PropertyF.Ground.Dimensions

end

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

variable (C : BraidedFusionCategory.{v,u})
set_option backward.isDefEq.respectTransparency false in
/-- A signed scalar tensor defect forces the fourth-dual tensor law. -/
theorem fourthDualIso_tensor_of_signed_defect
    {X Y : C.Obj} (z : ℂ) (hz : z * z = 1)
    (hd : (rootTensorDefect C X Y).hom = z • 𝟙 (X ⊗ Y)) :
    (fourthDualIso C (X ⊗ Y)).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C Y).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) ((Yᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X Y).homᘁ)ᘁ) := by
  let T := rootTensorIso C X Y
  let A := (fourthDualRootNaturalIso C).app (X ⊗ Y)
  have ht : T.hom = z • A.hom :=
    (iso_comp_inv_eq_smul_iff_of_sq_one A T z hz).1 hd
  have hsq : T.hom ≫ ((T.homᘁ)ᘁ) = (fourthDualIso C (X ⊗ Y)).hom := by
    rw [ht]
    simp only [rightAdjointMate_smul, Linear.smul_comp, Linear.comp_smul, smul_smul,
      hz, one_smul]
    exact congrArg (fun n => (n.app (X ⊗ Y)).hom) (fourthDualRootNaturalSquare_eq C)
  exact hsq.symm.trans (rootTensor_square_eq_fourthDual_tensor C X Y)

/-- The fourth-dual tensor law holds when the left factor is the chosen unit
simple representative. -/
theorem fourthDualIso_tensor_unitLabel_left (X : C.Obj) :
    (fourthDualIso C (simples C (unitIndex C) ⊗ X)).hom =
      ((fourthDualIso C (simples C (unitIndex C))).hom ⊗ₘ (fourthDualIso C X).hom) ≫
        (doubleDualTensorIso (((simples C (unitIndex C))ᘁ)ᘁ) ((Xᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso (simples C (unitIndex C)) X).homᘁ)ᘁ) :=
  fourthDualIso_tensor_of_signed_defect C (rootDimension C (unitIndex C))
    (rootDimension_unit_sq C) (rootTensorDefect_unitLabel_left C X)

/-- The fourth-dual tensor law holds when the right factor is the chosen unit
simple representative. -/
theorem fourthDualIso_tensor_unitLabel_right (X : C.Obj) :
    (fourthDualIso C (X ⊗ simples C (unitIndex C))).hom =
      ((fourthDualIso C X).hom ⊗ₘ (fourthDualIso C (simples C (unitIndex C))).hom) ≫
        (doubleDualTensorIso ((Xᘁ)ᘁ) (((simples C (unitIndex C))ᘁ)ᘁ)).hom ≫
          (((doubleDualTensorIso X (simples C (unitIndex C))).homᘁ)ᘁ) :=
  fourthDualIso_tensor_of_signed_defect C (rootDimension C (unitIndex C))
    (rootDimension_unit_sq C) (rootTensorDefect_unitLabel_right C X)
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
    (hsimple : ∀ i j, (rootTensorDefect C (simples C i) (simples C j)).hom ≫
      (rootTensorDefect C (simples C i) (simples C j)).hom =
        𝟙 (simples C i ⊗ simples C j)) (X Y : C.Obj) :
    (rootTensorDefect C X Y).hom ≫ (rootTensorDefect C X Y).hom = 𝟙 (X ⊗ Y) := by
  apply tensor_simples_hom_ext C
  intro i j sx sy
  have hn := rootTensorDefect_natural C sx sy
  rw [← Category.assoc, hn, Category.assoc, hn, ← Category.assoc, hsimple,
    Category.id_comp, Category.comp_id]
/-- The fourth-dual tensor law on simple pairs implies ENO trace reciprocity. -/
theorem trace_reciprocity_of_fourth_dual
    (hfourth : ∀ i j : Fin (rank C),
      fourthDualTensorLaw C (simples C i) (simples C j)) :
    ENOTraceMatrixReciprocity C := by
  have hinv : ∀ X Y : C.Obj, (rootTensorDefect C X Y).hom ≫ (rootTensorDefect C X Y).hom = 𝟙 (X ⊗ Y) := by
    apply rootTensorDefect_involution_extension C
    intro i j
    apply rootTensorDefect_involution_of_tensor_square C
    rw [rootTensor_square_eq_fourthDual_tensor, ← hfourth]
  apply trace_reciprocity_of_coevaluation C
  intro i k
  exact rootTensorDefect_slide_of_involution C (simples C k) (hinv _ _)

/-- The fourth-dual law on non-unit simple pairs suffices for the canonical pseudo-unitary spherical structure. -/
theorem positive_spherical_of_nonunit_fourth_dual
    (hfourth : ∀ i j : Fin (rank C), i ≠ unitIndex C → j ≠ unitIndex C →
      fourthDualTensorLaw C (simples C i) (simples C j))
    (hpu : PseudoUnitary C) :
    HasFPSphericalStructure C := by
  have hsimple : ∀ i j : Fin (rank C),
      fourthDualTensorLaw C (simples C i) (simples C j) := by
    intro i j
    by_cases hi : i = unitIndex C
    · subst i
      exact fourthDualIso_tensor_unitLabel_left C (simples C j)
    · by_cases hj : j = unitIndex C
      · subst j
        exact fourthDualIso_tensor_unitLabel_right C (simples C i)
      · exact hfourth i j hi hj
  exact positive_spherical_of_simple_fourth_and_reciprocity C hsimple
    (trace_reciprocity_of_fourth_dual C hsimple) hpu
end PropertyF.Ground.Dimensions

end
