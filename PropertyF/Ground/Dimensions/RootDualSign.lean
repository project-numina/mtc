module
public import PropertyF.Ground.Dimensions.NaturalRoots
public import PropertyF.Ground.Dimensions.IntrinsicNonzero

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u

set_option backward.isDefEq.respectTransparency false in
/-- The inverse dual of a natural fourth-dual square root is also a root at
the dual object. -/
theorem inverseDualRoot_square (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj) :
    (rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm.hom ≫
      (((((rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm.hom)ᘁ)ᘁ)) =
      (fourthDualIso C (Xᘁ)).hom := by
  let j : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  have hroot : j.hom ≫ ((j.homᘁ)ᘁ) = (fourthDualIso C X).hom := by
    have h := congrArg (fun n => (n.app X).hom) (fourthDualRootNaturalSquare_eq C)
    exact h
  have hiso : j ≪≫ rightDualIsoMap (rightDualIsoMap j) = fourthDualIso C X := by
    apply Iso.ext
    exact hroot
  have hinv := congrArg Iso.inv hiso
  have hm := congrArg (fun f => rightAdjointMate f) hinv
  rw [fourthDualIso_rightDual]
  simpa only [Iso.trans_inv, rightDualIsoMap, Iso.symm_hom, Iso.symm_inv,
    comp_rightAdjointMate] using hm

set_option backward.isDefEq.respectTransparency false in
/-- On a simple object, the natural root on the dual differs from the inverse
dual root by a sign. -/
theorem rootDual_differs_by_sign (C : Ground.BraidedFusionCategory.{v,u}) (X : C.Obj)
    [Simple X] : ∃ ε : ℂ, ε * ε = 1 ∧
      ((fourthDualRootNaturalIso C).app (Xᘁ)).hom =
        ε • (rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm.hom := by
  letI : Simple (Xᘁ) := Ground.simple_rightDual C X
  letI : FiniteDimensional ℂ ((Xᘁ) ⟶ (Xᘁ)) := Ground.IsFusionCategory.hom_finite _ _
  let l : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (rightDualIsoMap ((fourthDualRootNaturalIso C).app X)).symm
  let k : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (fourthDualRootNaturalIso C).app (Xᘁ)
  obtain ⟨ε, _, he, _⟩ := doubleDualIso_scalar l k
  refine ⟨ε, ?_, he⟩
  have hk : k.hom ≫ ((k.homᘁ)ᘁ) = (fourthDualIso C (Xᘁ)).hom := by
    have h := congrArg (fun n => (n.app (Xᘁ)).hom) (fourthDualRootNaturalSquare_eq C)
    exact h
  have hl : l.hom ≫ ((l.homᘁ)ᘁ) = (fourthDualIso C (Xᘁ)).hom := inverseDualRoot_square C X
  have hscale : k.hom ≫ ((k.homᘁ)ᘁ) = (ε * ε) • (l.hom ≫ ((l.homᘁ)ᘁ)) := by
    rw [he]
    simp only [rightAdjointMate_smul, Linear.smul_comp, Linear.comp_smul, smul_smul]
  have hm : (ε * ε) • (fourthDualIso C (Xᘁ)).hom = (1 : ℂ) • (fourthDualIso C (Xᘁ)).hom := by
    calc
      _ = (ε * ε) • (l.hom ≫ ((l.homᘁ)ᘁ)) := by rw [hl]
      _ = k.hom ≫ ((k.homᘁ)ᘁ) := hscale.symm
      _ = _ := by simpa using hk
  have hn : (fourthDualIso C (Xᘁ)).hom ≠ 0 := by
    intro h
    have hh := congrArg (fun f => f ≫ (fourthDualIso C (Xᘁ)).inv) h
    simp at hh
    exact id_nonzero (Xᘁ) hh
  exact smul_left_injective ℂ hn hm

set_option backward.isDefEq.respectTransparency false in
/-- The intrinsic norm is the product of the root dimension and the root
right-dual dimension, up to the ENO sign. -/
theorem squaredNorm_eq_signed_root_dimensions (C : Ground.BraidedFusionCategory.{v,u})
    (X : C.Obj) [Simple X] : ∃ ε : ℂ, ε * ε = 1 ∧
      Ground.squaredNorm C X = ε *
        Ground.unitScalar C (rightQuantumTrace ((fourthDualRootNaturalIso C).app X)) *
        Ground.unitScalar C (rightQuantumTrace ((fourthDualRootNaturalIso C).app (Xᘁ))) := by
  obtain ⟨ε, hε, he⟩ := rootDual_differs_by_sign C X
  refine ⟨ε, hε, ?_⟩
  let j : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  let l : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (rightDualIsoMap j).symm
  let k : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (fourthDualRootNaturalIso C).app (Xᘁ)
  have ht : rightQuantumTrace k = ε • rightQuantumTrace l := by
    apply End.homEquiv.injective
    have he' : k.hom = ε • l.hom := he
    simp [rightQuantumTrace, he', tensorHom_def]
  rw [target_squaredNorm_choice_independent C X j, leftQuantumTrace_eq_rightDual j]
  change Ground.unitScalar C (rightQuantumTrace j) * Ground.unitScalar C (rightQuantumTrace l) =
    ε * Ground.unitScalar C (rightQuantumTrace j) * Ground.unitScalar C (rightQuantumTrace k)
  rw [ht]
  simp only [← groundUnitScalarEquiv_apply, map_smul, smul_eq_mul]
  calc
    _ = (ε * ε) * (groundUnitScalarEquiv C (rightQuantumTrace j) *
      groundUnitScalarEquiv C (rightQuantumTrace l)) := by rw [hε, one_mul]
    _ = _ := by ring

end PropertyF.Ground.Dimensions
