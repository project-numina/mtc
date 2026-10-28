module
public import PropertyF.Ground.Dimensions.Pivotal
public import Mathlib.CategoryTheory.Monoidal.Linear

/-! # Pivotal traces

Right and left traces are linear, cyclic and compatible with duality and isomorphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- An algebra equivalent to the scalar field is spanned by its identity. -/
theorem eq_smul_one_of_algEquiv {A : Type*} [Semiring A] [Algebra ℂ A]
    (e : A ≃ₐ[ℂ] ℂ) (a : A) : a = e a • (1 : A) :=
  e.injective (by simp)

/-- Cyclicity needs naturality only for the two components involved. -/
theorem rightTraceWith_cyclic {X Y : C} {j : X ≅ (Xᘁ)ᘁ} {k : Y ≅ (Yᘁ)ᘁ}
    (f : X ⟶ Y) (g : Y ⟶ X) (hnat : f ≫ k.hom = j.hom ≫ (fᘁ)ᘁ) :
    rightTraceWith j (f ≫ g) = rightTraceWith k (g ≫ f) := by
  apply End.homEquiv.injective
  change η_ X (Xᘁ) ≫ (((f ≫ g) ≫ j.hom) ⊗ₘ 𝟙 (Xᘁ)) ≫ ε_ (Xᘁ) ((Xᘁ)ᘁ) =
    η_ Y (Yᘁ) ≫ (((g ≫ f) ≫ k.hom) ⊗ₘ 𝟙 (Yᘁ)) ≫ ε_ (Yᘁ) ((Yᘁ)ᘁ)
  simp only [tensorHom_def, whiskerLeft_id, Category.comp_id, comp_whiskerRight,
    Category.assoc]
  rw [← coevaluation_comp_rightAdjointMate_assoc, whisker_exchange_assoc g (fᘁ),
    whisker_exchange_assoc j.hom (fᘁ), ← rightAdjointMate_comp_evaluation,
    ← comp_whiskerRight_assoc j.hom (fᘁᘁ), ← hnat, comp_whiskerRight_assoc]

end PropertyF.Ground.Dimensions

namespace PropertyF.Ground.Dimensions.PivotalStructure

universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  (p : PivotalStructure (C := C)) {X : C}

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
/-- The right trace is linear in its endomorphism argument. -/
theorem rightTrace_add (f g : X ⟶ X) : p.rightTrace (f + g) = p.rightTrace f + p.rightTrace g :=
  End.homEquiv.injective (by simp [rightTrace, tensorHom_def])

theorem rightTrace_smul (c : ℂ) (f : X ⟶ X) : p.rightTrace (c • f) = c • p.rightTrace f :=
  End.homEquiv.injective (by simp [rightTrace, tensorHom_def])

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
/-- The left trace is linear in its endomorphism argument. -/
theorem leftTrace_add (f g : X ⟶ X) : p.leftTrace (f + g) = p.leftTrace f + p.leftTrace g :=
  End.homEquiv.injective (by simp [leftTrace, tensorHom_def])

theorem leftTrace_smul (c : ℂ) (f : X ⟶ X) : p.leftTrace (c • f) = c • p.leftTrace f :=
  End.homEquiv.injective (by simp [leftTrace, tensorHom_def])

end PropertyF.Ground.Dimensions.PivotalStructure

namespace PropertyF.Ground.Dimensions.PivotalStructure
open CategoryTheory CategoryTheory.MonoidalCategory
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The right pivotal trace is cyclic. -/
theorem rightTrace_cyclic (p : PivotalStructure (C := C)) {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ X) : p.rightTrace (f ≫ g) = p.rightTrace (g ≫ f) :=
  rightTraceWith_cyclic f g (p.naturality f)

/-- Pivotal dimensions are invariant under object isomorphism. -/
theorem rightTrace_id_iso (p : PivotalStructure (C := C)) {X Y : C} (e : X ≅ Y) :
    p.rightTrace (𝟙 X) = p.rightTrace (𝟙 Y) := by simpa using p.rightTrace_cyclic e.hom e.inv

end PropertyF.Ground.Dimensions.PivotalStructure

namespace PropertyF.Ground.Dimensions
open CategoryTheory CategoryTheory.MonoidalCategory
universe v u
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- Scaling the double-dual component scales its right quantum trace. -/
theorem rightQuantumTrace_smul_hom [Preadditive C] [Linear ℂ C]
    [MonoidalPreadditive C] [MonoidalLinear ℂ C] {X : C}
    {j k : X ≅ (Xᘁ)ᘁ} {c : ℂ} (h : j.hom = c • k.hom) :
    rightQuantumTrace j = c • rightQuantumTrace k :=
  End.homEquiv.injective (by simp [rightQuantumTrace, h, tensorHom_def])

/-- The left quantum trace of an isomorphism is the right quantum trace of the
corresponding inverse dual isomorphism. -/
theorem leftQuantumTrace_eq_rightDual {X : C} (j : X ≅ (Xᘁ)ᘁ) :
    leftQuantumTrace j = rightQuantumTrace (rightDualIsoMap j).symm := by
  apply End.homEquiv.injective
  change η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (𝟙 (Xᘁ) ⊗ₘ j.inv) ≫ ε_ X (Xᘁ) =
    η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ ((j.invᘁ) ⊗ₘ 𝟙 ((Xᘁ)ᘁ)) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)
  simp only [tensorHom_def, id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
  rw [rightAdjointMate_comp_evaluation]

section
variable {X Y : C} {j : X ≅ (Xᘁ)ᘁ} {k : Y ≅ (Yᘁ)ᘁ}

/-- Compatible double-dual components have the same right quantum trace under
an object isomorphism. -/
theorem rightQuantumTrace_iso
    (e : X ≅ Y) (hnat : e.hom ≫ k.hom = j.hom ≫ (e.homᘁ)ᘁ) :
    rightQuantumTrace j = rightQuantumTrace k := by
  simpa [rightTraceWith, rightQuantumTrace] using (rightTraceWith_cyclic e.hom e.inv hnat)

/-- Compatibility of double-dual components is preserved by inverse duality. -/
theorem dual_components_natural
    (e : X ≅ Y) (hnat : e.hom ≫ k.hom = j.hom ≫ (e.homᘁ)ᘁ) :
    (e.invᘁ) ≫ (rightDualIsoMap k).symm.hom =
      (rightDualIsoMap j).symm.hom ≫ ((e.invᘁ)ᘁ)ᘁ := by
  let ee := rightDualIsoMap (rightDualIsoMap e)
  have hiso : e ≪≫ k = j ≪≫ ee := Iso.ext hnat
  have hinv := congrArg (fun (a : X ≅ (Yᘁ)ᘁ) => a.inv) hiso
  simpa only [Iso.trans_inv, comp_rightAdjointMate, ee, rightDualIsoMap, Iso.symm_hom] using
    (congrArg (fun (a : (Yᘁ)ᘁ ⟶ X) => rightAdjointMate a) hinv)

/-- Both quantum traces are preserved when double-dual components are
transported across an object isomorphism. -/
theorem quantumTraces_iso
    (e : X ≅ Y) (hnat : e.hom ≫ k.hom = j.hom ≫ (e.homᘁ)ᘁ) :
    rightQuantumTrace j = rightQuantumTrace k ∧ leftQuantumTrace j = leftQuantumTrace k := by
  refine ⟨rightQuantumTrace_iso e hnat, ?_⟩
  simpa only [leftQuantumTrace_eq_rightDual] using
    rightQuantumTrace_iso (rightDualIsoMap e.symm) (dual_components_natural e hnat)

end

/-- Left trace is right trace on the dual endomorphism with the inverse dual
pivotal component. -/
theorem leftTrace_eq_rightTraceWith_dual (p : PivotalStructure (C := C))
    {X : C} (f : X ⟶ X) :
    p.leftTrace f = rightTraceWith (rightDualIsoMap (p.iso X)).symm (fᘁ) := by
  apply End.homEquiv.injective
  change η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (𝟙 (Xᘁ) ⊗ₘ ((p.iso X).inv ≫ f)) ≫ ε_ X (Xᘁ) =
    η_ (Xᘁ) ((Xᘁ)ᘁ) ≫ (((fᘁ) ≫ (p.iso X).invᘁ) ⊗ₘ 𝟙 ((Xᘁ)ᘁ)) ≫ ε_ ((Xᘁ)ᘁ) (((Xᘁ)ᘁ)ᘁ)
  simp only [tensorHom_def, id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
  rw [← comp_rightAdjointMate, rightAdjointMate_comp_evaluation]

/-- The inverse dual pivotal components are natural on dual morphisms. -/
theorem dual_pivotal_naturality (p : PivotalStructure (C := C))
    {X Y : C} (f : X ⟶ Y) :
    (fᘁ) ≫ (rightDualIsoMap (p.iso X)).symm.hom =
      (rightDualIsoMap (p.iso Y)).symm.hom ≫ ((fᘁ)ᘁ)ᘁ := by
  simpa only [rightDualIsoMap, Iso.symm_hom, comp_rightAdjointMate] using
    congrArg (fun (a : (Xᘁ)ᘁ ⟶ Y) => rightAdjointMate a)
      ((CommSq.vert_inv (CommSq.mk (p.naturality f))).w).symm

/-- The left pivotal trace is cyclic without requiring sphericality. -/
theorem leftTrace_cyclic (p : PivotalStructure (C := C)) {X Y : C}
    (f : X ⟶ Y) (g : Y ⟶ X) : p.leftTrace (f ≫ g) = p.leftTrace (g ≫ f) := by
  simpa only [leftTrace_eq_rightTraceWith_dual, comp_rightAdjointMate] using
    rightTraceWith_cyclic (gᘁ) (fᘁ) (dual_pivotal_naturality p g)

end PropertyF.Ground.Dimensions
