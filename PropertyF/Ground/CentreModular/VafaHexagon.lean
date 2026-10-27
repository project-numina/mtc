module
public import PropertyF.Ground.CentreModular.VafaTensorMonodromy
public import PropertyF.Ground.Modular.Verlinde

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace PropertyF.Ground.CentreModular
universe v u

/-- The categorical double-braiding hexagon, as a product of conjugate
monodromy automorphisms. -/
theorem monodromy_hexagon_iso (C : BraidedFusionCategory.{v,u}) (Z X Y : C.Obj) :
    (α_ Z X Y) ≪≫ monodromyIso C Z (X ⊗ Y) ≪≫ (α_ Z X Y).symm =
      (((β_ Z X) ⊗ᵢ Iso.refl Y) ≪≫ (α_ X Z Y)) ≪≫
        (Iso.refl X ⊗ᵢ monodromyIso C Z Y) ≪≫
        (((β_ Z X) ⊗ᵢ Iso.refl Y) ≪≫ (α_ X Z Y)).symm ≪≫
        (monodromyIso C Z X ⊗ᵢ Iso.refl Y) := by
  apply Iso.ext
  have h := Modular.doubleBraiding_tensor_factorization Z X Y
  simp only [monodromyIso, Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Iso.refl_hom,
    tensorHom_id, id_tensorHom, Category.assoc]
  simp only [Modular.doubleBraiding, Category.assoc] at h
  simpa [Category.assoc, ← comp_whiskerRight] using h

/-- The actual FP determinant of the monodromy hexagon is the weighted sum
of the two simple monodromy determinants, under simple twist balancing. -/
theorem fpDeterminant_monodromy_hexagon (C : BraidedFusionCategory.{v,u})
    (η : 𝟭 C.Obj ≅ 𝟭 C.Obj) (t : Fin (rank C) → ℂˣ)
    (hbalance : ∀ i j, η.app (simples C i ⊗ simples C j) =
      scalarIso C (simples C i ⊗ simples C j) (t i * t j) ≪≫
        monodromyIso C (simples C i) (simples C j))
    (z i j : Fin (rank C)) :
    fpDeterminant C (simples C z ⊗ (simples C i ⊗ simples C j))
      (monodromyIso C (simples C z) (simples C i ⊗ simples C j)) =
    fpSimple C i • fpDeterminant C (simples C z ⊗ simples C j)
      (monodromyIso C (simples C z) (simples C j)) +
    fpSimple C j • fpDeterminant C (simples C z ⊗ simples C i)
      (monodromyIso C (simples C z) (simples C i)) := by
  let Z := simples C z
  let X := simples C i
  let Y := simples C j
  let t' := α_ Z X Y
  let u := ((β_ Z X) ⊗ᵢ Iso.refl Y) ≪≫ (α_ X Z Y)
  let q := Iso.refl X ⊗ᵢ monodromyIso C Z Y
  let r := monodromyIso C Z X ⊗ᵢ Iso.refl Y
  have hconj := fpDeterminant_conjugate C t'.symm (monodromyIso C Z (X ⊗ Y))
  change fpDeterminant C ((Z ⊗ X) ⊗ Y)
    (t' ≪≫ monodromyIso C Z (X ⊗ Y) ≪≫ t'.symm) = _ at hconj
  rw [monodromy_hexagon_iso] at hconj
  have hq := fpDeterminant_conjugate C u.symm q
  change fpDeterminant C ((Z ⊗ X) ⊗ Y) (u ≪≫ q ≪≫ u.symm) = _ at hq
  change fpDeterminant C ((Z ⊗ X) ⊗ Y) (u ≪≫ q ≪≫ u.symm ≪≫ r) = _ at hconj
  have heq : (u ≪≫ q ≪≫ u.symm ≪≫ r) = (u ≪≫ q ≪≫ u.symm) ≪≫ r := by
    apply Iso.ext
    simp
  rw [heq, fpDeterminant_trans, hq] at hconj
  have h1 := fpDeterminant_tensor_simple_monodromy C η t hbalance X z j
  have h2 := fpDeterminant_simple_monodromy_tensor C η t hbalance Y z i
  change fpDeterminant C (X ⊗ (Z ⊗ Y)) q = _ at h1
  change fpDeterminant C ((Z ⊗ X) ⊗ Y) r = _ at h2
  rw [h1, h2, fpDimension_simple, fpDimension_simple] at hconj
  exact hconj.symm

end PropertyF.Ground.CentreModular
