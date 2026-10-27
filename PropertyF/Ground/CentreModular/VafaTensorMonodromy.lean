module
public import PropertyF.Ground.CentreModular.VafaNaturalTensor

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u

/-- The FP tensor determinant rule holds for scalar multiples of a component
of an arbitrary natural automorphism. -/
theorem fpDeterminant_tensor_scalar_natural (C : BraidedFusionCategory.{v,u})
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (X Y : C.Obj) (z : ℂˣ) :
    fpDeterminant C (X ⊗ Y) (Iso.refl X ⊗ᵢ (scalarIso C Y z ≪≫ η.app Y)) =
      fpDimension C X • fpDeterminant C Y (scalarIso C Y z ≪≫ η.app Y) := by
  have h : (Iso.refl X ⊗ᵢ (scalarIso C Y z ≪≫ η.app Y)) =
      (Iso.refl X ⊗ᵢ scalarIso C Y z) ≪≫ (Iso.refl X ⊗ᵢ η.app Y) := by
    apply Iso.ext
    simp [tensorIso_hom, tensorHom_def, whiskerLeft_comp]
  rw [h, fpDeterminant_trans, fpDeterminant_trans, fpDeterminant_tensor_scalar,
    fpDeterminant_tensor_natural, smul_add]

/-- Balancing identifies the mixed double braiding of two simples with a
scalar multiple of the twist component. -/
theorem monodromy_simple_eq_scalar_natural (C : BraidedFusionCategory.{v,u})
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (t : Fin (rank C) → ℂˣ)
    (hbalance : ∀ i j, η.app (simples C i ⊗ simples C j) =
      scalarIso C (simples C i ⊗ simples C j) (t i * t j) ≪≫
        monodromyIso C (simples C i) (simples C j))
    (i j : Fin (rank C)) :
    monodromyIso C (simples C i) (simples C j) =
      scalarIso C (simples C i ⊗ simples C j) (t i * t j)⁻¹ ≪≫
        η.app (simples C i ⊗ simples C j) := by
  rw [hbalance]
  have h : scalarIso C (simples C i ⊗ simples C j) (t i * t j)⁻¹ =
      (scalarIso C (simples C i ⊗ simples C j) (t i * t j)).symm := by
    apply Iso.ext
    rfl
  rw [h]
  simp

/-- Under the explicit balancing equation, the tensor determinant rule holds
for every simple mixed monodromy. -/
theorem fpDeterminant_tensor_simple_monodromy (C : BraidedFusionCategory.{v,u})
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (t : Fin (rank C) → ℂˣ)
    (hbalance : ∀ i j, η.app (simples C i ⊗ simples C j) =
      scalarIso C (simples C i ⊗ simples C j) (t i * t j) ≪≫
        monodromyIso C (simples C i) (simples C j))
    (X : C.Obj) (i j : Fin (rank C)) :
    fpDeterminant C (X ⊗ (simples C i ⊗ simples C j))
      (Iso.refl X ⊗ᵢ monodromyIso C (simples C i) (simples C j)) =
      fpDimension C X • fpDeterminant C (simples C i ⊗ simples C j)
        (monodromyIso C (simples C i) (simples C j)) := by
  rw [monodromy_simple_eq_scalar_natural C η t hbalance]
  exact fpDeterminant_tensor_scalar_natural C η X _ _

/-- Braiding transports tensoring an automorphism on the right to tensoring it
on the left, preserving its categorical FP determinant. -/
theorem fpDeterminant_tensor_flip (C : BraidedFusionCategory.{v,u})
    (X Y : C.Obj) (a : Y ≅ Y) :
    fpDeterminant C (Y ⊗ X) (a ⊗ᵢ Iso.refl X) =
      fpDeterminant C (X ⊗ Y) (Iso.refl X ⊗ᵢ a) := by
  let e := β_ Y X
  have h : a ⊗ᵢ Iso.refl X = e ≪≫ (Iso.refl X ⊗ᵢ a) ≪≫ e.symm := by
    apply Iso.ext
    apply (cancel_mono e.hom).1
    simpa [e, Category.assoc, tensorIso_hom] using
      (braiding_naturality a.hom (𝟙 X))
  rw [h]
  exact fpDeterminant_conjugate C e.symm (Iso.refl X ⊗ᵢ a)

/-- Under balancing, tensoring a simple mixed monodromy on either side
satisfies the FP determinant rule. -/
theorem fpDeterminant_simple_monodromy_tensor (C : BraidedFusionCategory.{v,u})
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (t : Fin (rank C) → ℂˣ)
    (hbalance : ∀ i j, η.app (simples C i ⊗ simples C j) =
      scalarIso C (simples C i ⊗ simples C j) (t i * t j) ≪≫
        monodromyIso C (simples C i) (simples C j))
    (X : C.Obj) (i j : Fin (rank C)) :
    fpDeterminant C ((simples C i ⊗ simples C j) ⊗ X)
      (monodromyIso C (simples C i) (simples C j) ⊗ᵢ Iso.refl X) =
      fpDimension C X • fpDeterminant C (simples C i ⊗ simples C j)
        (monodromyIso C (simples C i) (simples C j)) := by
  rw [fpDeterminant_tensor_flip]
  exact fpDeterminant_tensor_simple_monodromy C η t hbalance X i j

end PropertyF.Ground.CentreModular
