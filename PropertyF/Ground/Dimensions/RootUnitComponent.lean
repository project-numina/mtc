module
public import PropertyF.Ground.Dimensions.FourthDualUnit

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
namespace PropertyF.Ground.Dimensions
universe v u
set_option backward.isDefEq.respectTransparency false in
/-- The actual natural fourth-dual root is its unit dimension times the
canonical double-dual unit map. -/
theorem fourthDualRoot_unit_component (C : Ground.BraidedFusionCategory.{v,u}) :
    ((fourthDualRootNaturalIso C).app (𝟙_ C.Obj)).hom =
      rootDimension C (Ground.unitIndex C) • (doubleDualUnitIso (C := C.Obj)).hom := by
  let U := 𝟙_ C.Obj
  let : HasRightDual U := RightRigidCategory.rightDual U
  let : HasRightDual (Uᘁ) := RightRigidCategory.rightDual (Uᘁ)
  let : Simple U := Ground.IsFusionCategory.unit_simple
  let : FiniteDimensional ℂ (U ⟶ U) := Ground.IsFusionCategory.hom_finite _ _
  let a := (fourthDualRootNaturalIso C).app U
  let u := Ground.doubleDualIso C U
  obtain ⟨r, _, hr, _⟩ := doubleDualIso_scalar u a
  have htrace : Ground.unitScalar C (rightQuantumTrace a) = r := by
    have ht : rightQuantumTrace a = r • rightQuantumTrace u := by
      apply End.homEquiv.injective
      simp [rightQuantumTrace, hr, tensorHom_def]
    rw [ht]
    have hu : u = doubleDualUnitIso (C := C.Obj) := Iso.ext (drinfeld_unit C)
    rw [hu, rightQuantumTrace_unitIso]
    simp only [← groundUnitScalarEquiv_apply, map_smul, map_one, smul_eq_mul, mul_one]
  have hdim : rootDimension C (Ground.unitIndex C) = r := by
    obtain ⟨e⟩ := Ground.unitIndex_iso C
    have hn := (fourthDualRootNaturalIso C).hom.naturality e.hom
    have ht := rightQuantumTrace_iso
      ((fourthDualRootNaturalIso C).app (Ground.simples C (Ground.unitIndex C))) a e
      (by simpa [doubleDualFunctor, a] using hn)
    change Ground.unitScalar C (rootTrace C (𝟙 (Ground.simples C (Ground.unitIndex C)))) = r
    have hq : rootTrace C (𝟙 (Ground.simples C (Ground.unitIndex C))) =
        rightQuantumTrace ((fourthDualRootNaturalIso C).app (Ground.simples C (Ground.unitIndex C))) := by
      apply End.homEquiv.injective
      simp [rootTrace, rightTraceWith, rightQuantumTrace, tensorHom_def]
    rw [hq, ht, htrace]
  have hu : u = doubleDualUnitIso (C := C.Obj) := Iso.ext (drinfeld_unit C)
  simpa [a, hdim, hu] using hr
end PropertyF.Ground.Dimensions
