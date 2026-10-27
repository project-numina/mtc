module
public import PropertyF.Ground.Dimensions.RootDualSign
public import PropertyF.Ground.Dimensions.ENOMatrices
public import PropertyF.Ground.Dimensions.SimpleHomBasis
public import PropertyF.Ground.Dimensions.CharacterDual

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
/-- The sign comparing the root on a simple's dual to the inverse dual root. -/
noncomputable def rootDualSign (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) : ℂ := by
  letI : Simple (Ground.simples C i) := Ground.simples_simple C i
  exact Classical.choose (rootDual_differs_by_sign C (Ground.simples C i))

theorem rootDualSign_sq (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    rootDualSign C i * rootDualSign C i = 1 := by
  letI : Simple (Ground.simples C i) := Ground.simples_simple C i
  exact (Classical.choose_spec (rootDual_differs_by_sign C (Ground.simples C i))).1

theorem rootDualSign_component (C : Ground.BraidedFusionCategory.{v,u}) (i : Fin (Ground.rank C)) :
    ((fourthDualRootNaturalIso C).app ((Ground.simples C i)ᘁ)).hom =
      rootDualSign C i • (rightDualIsoMap ((fourthDualRootNaturalIso C).app (Ground.simples C i))).symm.hom := by
  letI : Simple (Ground.simples C i) := Ground.simples_simple C i
  exact (Classical.choose_spec (rootDual_differs_by_sign C (Ground.simples C i))).2

set_option backward.isDefEq.respectTransparency false in
/-- Intrinsic simple norms are signed products of the root dimensions of a
simple and its dual, using the same sign as the dual-root component. -/
theorem squaredNorm_eq_rootDualSign_mul (C : Ground.BraidedFusionCategory.{v,u})
    (i : Fin (Ground.rank C)) :
    Ground.squaredNorm C (Ground.simples C i) = rootDualSign C i * rootDimension C i *
      rootDimension C (Ground.dualIndex C i) := by
  let X := Ground.simples C i
  letI : Simple X := Ground.simples_simple C i
  let j : X ≅ (Xᘁ)ᘁ := (fourthDualRootNaturalIso C).app X
  let l : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (rightDualIsoMap j).symm
  let k : (Xᘁ) ≅ (((Xᘁ)ᘁ)ᘁ) := (fourthDualRootNaturalIso C).app (Xᘁ)
  let e : Xᘁ ≅ ᘁX := leftDualIso
    (BraidedCategory.exactPairing_swap X (Xᘁ)) HasLeftDual.exact
  obtain ⟨u⟩ := Ground.dualIndex_iso C i
  have hId (Z : C.Obj) : rootTrace C (𝟙 Z) = rightQuantumTrace ((fourthDualRootNaturalIso C).app Z) := by
    apply End.homEquiv.injective
    simp [rootTrace, rightTraceWith, rightQuantumTrace, tensorHom_def]
  have hq : Ground.unitScalar C (rightQuantumTrace k) = rootDimension C (Ground.dualIndex C i) := by
    change Ground.unitScalar C (rightQuantumTrace ((fourthDualRootNaturalIso C).app (Xᘁ))) = _
    rw [← hId, rootTrace_id_iso C (e ≪≫ u)]
    rfl
  have hx : Ground.unitScalar C (rightQuantumTrace j) = rootDimension C i := by
    change Ground.unitScalar C (rightQuantumTrace ((fourthDualRootNaturalIso C).app X)) = _
    rw [← hId]
    rfl
  have ht : rightQuantumTrace k = rootDualSign C i • rightQuantumTrace l := by
    apply End.homEquiv.injective
    have he : k.hom = rootDualSign C i • l.hom := rootDualSign_component C i
    simp [rightQuantumTrace, he, tensorHom_def]
  rw [target_squaredNorm_choice_independent C X j, leftQuantumTrace_eq_rightDual j]
  change Ground.unitScalar C (rightQuantumTrace j) * Ground.unitScalar C (rightQuantumTrace l) =
    rootDualSign C i * rootDimension C i * rootDimension C (Ground.dualIndex C i)
  rw [← hx, ← hq, ht]
  simp only [← groundUnitScalarEquiv_apply, map_smul, smul_eq_mul]
  have hs := rootDualSign_sq C i
  calc
    _ = (rootDualSign C i * rootDualSign C i) * (groundUnitScalarEquiv C (rightQuantumTrace j) *
      groundUnitScalarEquiv C (rightQuantumTrace l)) := by rw [hs, one_mul]
    _ = _ := by ring

end PropertyF.Ground.Dimensions
